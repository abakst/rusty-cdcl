#![feature(non_ascii_idents)]
use std::collections::HashSet;
use std::collections::HashMap;
use std::iter::FromIterator;
use std::env;
use Lit::*;

pub type Var = i8;

#[derive(PartialEq, Eq, Debug, Copy, Clone, Hash)]
pub enum Lit { Pos(Var), Neg(Var) }

pub type Clause = Vec<Lit>;
pub type Model = Vec<Lit>;
pub type CNF = Vec<Clause>;

#[derive(PartialEq, Eq, Debug, Copy, Clone, Hash)]
pub struct Rec {level:i32, value:Lit}

#[derive(Debug, Clone)]
pub struct SimpleAssignment {
    trail: Vec<Rec>,
    graph: HashMap<Rec, HashSet<Rec>>
}
pub enum BCPResult { Conflict(i32, HashSet<Rec>), OK }
#[derive(Debug, Clone)]
pub enum UnitResult { Conflict(HashSet<Rec>), Unit(Lit, HashSet<Rec>), No }

#[derive(PartialEq)]
pub enum EvalResult { True, False, Unassigned }

pub trait Assignment {
    fn add(&mut self, r:Rec, reason:HashSet<Rec>);
    fn get(&self, v:Var) -> Option<&Rec>;
    fn get_reason(&self, r:&Rec) -> Option<&HashSet<Rec>>;
    fn backtrack(&mut self, l:i32);
    fn is_assigned(&self, v:Var) -> bool;
    fn iter(&self) -> std::slice::Iter<Rec>;
}

impl Rec {
    fn new(l:i32, v:Lit) -> Rec{
        Rec { level:l, value:v }
    }
}

impl SimpleAssignment {
    fn new() -> SimpleAssignment {
        SimpleAssignment { trail:Vec::new(), graph:HashMap::new() }
    }
}

impl Assignment for SimpleAssignment {
    fn add(&mut self, r:Rec, reason:HashSet<Rec>) {
        self.trail.push(r); 
        self.graph.insert(r, reason);
    }
    fn get(&self, v : Var) -> Option<&Rec> {
        self.iter()
            .fold(None, |acc, x|
                  match acc {
                      None =>
                          if var(&x.value) == v {
                              Some(x)
                          } else {
                              acc
                          }
                      _ => acc
                  }
            )
    }
    fn get_reason(&self, r:&Rec) -> Option<&HashSet<Rec>> {
        self.graph.get(&r)
    }
    fn backtrack(&mut self, l:i32) {
        let trace = self.iter().filter(|&x| x.level < l).cloned().collect();
        self.graph.retain(|k, _v| k.level < l);
        self.trail = trace;
    }
    fn is_assigned(&self, v:Var) -> bool {
        for r in &self.trail {
            if var(&r.value) == v {
                return true;
            }
        }
        return false;
    }
    fn iter(&self) -> std::slice::Iter<Rec> {
        self.trail.iter()
    }
}

fn var(l : &Lit) -> Var
{
    match l {
        Lit::Pos(v) => *v,
        Lit::Neg(v) => *v,
    }
}

fn unassigned<A:Assignment>(ϕ : &CNF, a : &A) -> HashSet<Var>
{
    let mut vs = HashSet::new();
    for c in ϕ {
        for l in c {
            let v = var(&l);
            if !a.is_assigned(v) {
                vs.insert(v);
            }
        }
    }
    return vs;
}

fn is_unit<A:Assignment>(ω : &Clause, a : &A) -> UnitResult
{
    let mut c = Vec::new();
    let mut s = HashSet::new();
    for l in ω {
        match a.get(var(&l)) {
            Some(r) => {
                if &r.value == l {
                    return UnitResult::No;
                } else {
                    s.insert(*r);
                }
            },
            None =>
                c.push(l)
        }
    }
    if let Some(l) = c.pop() {
        if c.len() == 0 {
            return UnitResult::Unit(*l, s)
        } else {
            return UnitResult::No
        }
    } else {
        return UnitResult::Conflict(s)
    }
}

fn bcp<A:Assignment>(ϕ : &CNF, a : &mut A, l : i32) -> BCPResult
{
    let mut again = true;
    while again {
        again = false;
        for c in ϕ {
            let r = is_unit(&c, a);
            match r {
                UnitResult::No => {},
                UnitResult::Conflict(s) => {
                    if c.len() == 1 {
                        return BCPResult::Conflict(0, s)
                    } else {
                        return BCPResult::Conflict(l, s)
                    }
                },
                UnitResult::Unit(lit, rest) => {
                    if c.len() == 1 {
                        a.add(Rec::new(0,lit), rest);
                    } else {
                        a.add(Rec::new(l,lit), rest);
                    }
                    again = true
                },
            }
        }
    }
    return BCPResult::OK
}

fn choose(s : HashSet<Var>) -> Option<Lit>
{
    for x in s {
        if x & 0x1 == 0 {
            return Some(Neg(x))
        } else {
            return Some(Pos(x))
        }
    }
    return None
}

fn clause_vars(c:&Clause) -> HashSet<Var>
{
    HashSet::from_iter(c.iter().map(|&x| var(&x)))
}

fn last_assigned<'l, A:Assignment>(c:&Clause, l:i32, a:&'l A) -> &'l Rec
{
    let s = clause_vars(c);
    for rec in a.iter().rev() {
        if rec.level <= l && s.contains(&var(&rec.value)) {
            return rec;
        }
    }
    panic!("uh {:?}", s);
}

fn resolve(c1:&Clause, c2:&Clause, v:Var) -> Clause
{
    let mut s:HashSet<Lit> =
        HashSet::from_iter(c1.iter()
                             .filter(|&x| var(x) != v)
                             .cloned());
    s.extend(c2.iter()
             .filter(|&x| var(x) != v)
             .cloned());

    return Vec::from_iter(s.iter().cloned());
}

fn one_lit_at_level<A:Assignment>(c:&Clause, l:i32, a:&A) -> bool
{
    let mut found = false;
    for lit in c {
        if let Some(r) = a.get(var(&lit)) {
            if r.level == l {
                if found {
                    return false;
                } else {
                    found = true;
                }
            }
        }
    }
    return found;
}

fn asserting_level<A:Assignment>(c:&Clause, a:&A) -> i32
{
    let mut levels = c.iter().map(|&lit|
                              match a.get(var(&lit)) {
                                  None => panic!("asdfasdfasdf"),
                                  Some(r) => r.level
                              }
    ).collect::<Vec<i32>>();
    levels.sort_by(|a, b| a.cmp(b));
    match levels.pop() {
        None => panic!("an empty clause"),
        Some(highest) => match levels.pop() {
            None => highest,
            Some(second_highest) => second_highest
        }
    }
}

fn level<A:Assignment>(c:&Clause, a:&A) -> i32
{
    c.iter()
     .fold(0, |acc, x|
           match a.get(var(&x)) {
               Some(r) => std::cmp::max(r.level, acc),
               _       => acc
           }
    )
}

fn analyze_conflict<A:Assignment>(a:&A, c:&HashSet<Rec>) -> (i32, Clause)
{
    let mut c1 = Vec::from_iter(c.iter().map(|&x| x.value));

    loop {
        let l = level(&c1, a);
        if l == 0
        {
            return (-1, Vec::new());
        }
        let t = last_assigned(&c1, l, a);
        let v = var(&t.value);
        match a.get_reason(&t) {
            None => panic!("nothing in graph?"),
            Some(c2set) => {
                let c2 = c2set.iter().map(|&x| x.value).collect::<Clause>();
                c1 = resolve(&c1,&Vec::from_iter(c2.iter().cloned()),v);
            }
        };
        if one_lit_at_level(&c1, l, a) {
            break;
        }
    }
    let b = asserting_level(&c1, a);
    return (b, c1)
}

pub fn neg(l:Lit) -> Lit
{
    match l {
        Pos(v) => Neg(v),
        Neg(v) => Pos(v)
    }
}
pub fn cdcl<A:Assignment>(mut ϕ : CNF, alloc : &Fn() -> A) -> (bool, A)
{
    use BCPResult::*;
    let mut assignment = alloc();
    if let Conflict(_, _) = bcp(&ϕ, &mut assignment, 0)
    {
        return (false, assignment);
    }
    let mut level = 0;
    while let Some(r) = choose(unassigned(&ϕ, &assignment)) {
        level = level + 1;
        assignment.add(Rec::new(level, r), HashSet::new());

        while let Conflict(_d, s) = bcp(&ϕ, &mut assignment, level) {
            let (b, c) = analyze_conflict(&assignment, &s);
            if b < 0 {
                return (false, assignment);
            } else {
                let learned = c.iter().map(|&r| neg(r)).collect();
                ϕ.push(learned);
                assignment.backtrack(b);
                level = b;
            }
        }
    }
    return (true, assignment);
}

fn mk_lit(l : &Var) -> Lit
{
    if *l < 0 {
        Neg(0 - (*l))
    } else {
        Pos(*l)
    }
}

fn mk_clause(v:Vec<Var>) -> Clause
{
    v.iter().map(mk_lit).collect::<Vec<Lit>>()
}

fn smt_lit(l:&Lit) {
    match l {
        Pos(v) => print!("x{}", v),
        Neg(v) => print!("(not x{})", v)
    }
}

fn read_formula(xs:&Vec<String>) -> CNF
{
    let mut f = Vec::new();
    let mut clause:HashSet<i8> = HashSet::new();
    let len = xs.len();
    for a in xs[1..len].iter() {
        let i = a.parse::<i8>().unwrap();
        if i == 0 {
            f.push(mk_clause(clause.iter().cloned().collect()));
            clause = HashSet::new();
        } else {
            clause.insert(i);
        }
    }
    return f;
}

fn dump_smt(f:&CNF)
{
    // There's probably a less gross way to do this in Rust :)
    let empty = SimpleAssignment::new();
    let vs = unassigned(&f, &empty);
    for v in vs {
        println!("(declare-const x{} Bool)", v)
    }
    println!("(assert\n  (and");
    for c in f {
        print!("    (or");
        for l in c {
            print!(" ");
            smt_lit(l);
        }
        print!(")\n");
    };
    println!("  )\n)");
    println!("(check-sat)");
}

fn main() {
    // Expects a sequence of integers, each 0 marks the end of a clause.
    // e.g. 1 2 3 0 -1 -2 -3 ==> (x₁ ∨ x₂ ∨ x₃) ∧ (¬x₁ ∨ ¬x₂ ∨ ¬x₃)
    let args:Vec<String> = env::args().collect();
    let f = read_formula(&args);

    // Should make this an option
    // Print out the smt2 program that can be used to confirm result
    dump_smt(&f);

    // Run the solver
    let (sat, _assignment) = cdcl(f, &SimpleAssignment::new);
    if sat {
         println!("SAT");
     } else {
         println!("UNSAT");
     }
}
