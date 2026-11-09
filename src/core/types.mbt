// The vocabulary the whole tool shares.
//
// Everything downstream — the symbolic interpreter, the explorer, the solver,
// the report — talks in these types only. Keeping them here (and frozen) is
// what lets the passes be written and tested independently.

///|
/// A source position. Lines and columns are 1-based, as every editor and
/// compiler diagnostic expects.
pub(all) struct Pos {
  line : Int32
  col : Int32
} derive(Debug, Eq, Hash)

///|
/// A half-open span. `end` is exclusive, so a statement one character long has
/// `start.col + 1 == end.col`.
pub(all) struct Span {
  start : Pos
  end : Pos
} derive(Debug, Eq, Hash)

///|
/// What a symbolic value is about.
///
/// The width matters: MoonBit's `Int` is 32 bits on wasm and 64 on native, and
/// a verifier that assumes one is wrong on the other. A program under
/// verification therefore declares its width, and every arithmetic operation
/// is modelled at that width with wrapping semantics.
pub(all) enum Sort {
  /// A signed integer of the given bit width.
  Int(Int)
  /// A boolean.
  Bool
  /// An integer the analysis treats as unbounded: array lengths and loop
  /// counters that are never wrapped.
  Nat
} derive(Debug, Eq)

///|
/// A term in the logic the solver understands: quantifier-free integer
/// arithmetic with comparisons, conjunctions and disjunctions.
///
/// Deliberately small. Every construct here is one the solver answers exactly,
/// which is what makes "unsat means proven" true rather than hopeful.
pub(all) enum Term {
  /// A literal integer.
  Lit(Int)
  /// A symbolic variable, named by its `SymVar.id`.
  Var(Int32)
  /// `a + b`
  Add(Term, Term)
  /// `a - b`
  Sub(Term, Term)
  /// `a * k`, `k` a literal. Non-linear multiplication is deliberately absent:
  /// a solver that claimed to handle it would be lying.
  MulLit(Term, Int)
  /// `a / k`, Euclidean, `k > 0`.
  DivLit(Term, Int)
  /// `a mod k`, `k > 0`.
  ModLit(Term, Int)
  /// Signed division of two terms, defined only when the divisor is non-zero.
  Div(Term, Term)
  /// Signed remainder of two terms, defined only when the divisor is non-zero.
  Rem(Term, Term)
  /// Unary minus.
  Neg(Term)
  /// `|a|`
  Abs(Term)
  /// Wrap `a` into `[-2^(w-1), 2^(w-1))`, two's complement.
  Wrap(Term, Int)
  /// `if c then a else b`
  Ite(Term, Term, Term)
  /// `a < b`
  Lt(Term, Term)
  /// `a <= b`
  Le(Term, Term)
  /// `a == b`
  Eq(Term, Term)
  /// `a != b`
  Ne(Term, Term)
  /// `not a`
  Not(Term)
  /// `a and b`
  And(Term, Term)
  /// `a or b`
  Or(Term, Term)
  /// `true`
  True
  /// `false`
  False
} derive(Debug, Eq)

///|
/// A declared symbolic variable: its name and sort.
pub(all) struct SymVar {
  id : Int32
  name : String
  sort : Sort
} derive(Debug, Eq)

///|
/// The outcome of a satisfiability query.
pub(all) enum Sat {
  /// The constraints hold; `model` assigns a value to every variable the
  /// solver had to decide.
  Sat(Map[Int32, Int])
  /// The constraints cannot hold. This is the answer that licenses a proof.
  Unsat
  /// The solver could not decide within its budget. Never reported as either
  /// of the other two.
  Unknown(String)
} derive(Debug)

///|
/// One line of the solver's own narration, kept so the UI can show *why* an
/// answer is what it is instead of just the answer.
pub(all) struct SolverStep {
  kind : String
  detail : String
  depth : Int
} derive(Debug, Eq)

///|
/// A verification obligation: assumptions that must imply a goal.
pub(all) struct Goal {
  label : String
  span : Span
  assumptions : Array[Term]
  conclusion : Term
} derive(Debug, Eq)

///|
/// How a goal ended up.
pub(all) enum GoalOutcome {
  /// Proven for every input satisfying the assumptions.
  Holds
  /// A concrete input satisfying the assumptions violates it.
  Violated(Map[Int32, Int], Array[SolverStep])
  /// The exploration bound cut the search short before a proof.
  Bounded(String)
  /// The solver gave up (budget or a construct outside the logic).
  Unknown(String)
} derive(Debug)

///|
/// A completed goal together with its outcome.
pub(all) struct GoalResult {
  goal : Goal
  outcome : GoalOutcome
  /// How many paths were explored to reach the answer.
  paths : Int
  /// How many solver queries were issued.
  queries : Int
  /// Wall-clock milliseconds, for the report.
  millis : Int
} derive(Debug)

///|
/// A whole program's verification result.
pub(all) struct Report {
  results : Array[GoalResult]
  /// Variables the program declared, so a counterexample can be rendered with
  /// names instead of ids.
  vars : Array[SymVar]
  /// Functions that were symbolically executed.
  functions : Array[String]
  /// Paths the explorer abandoned because it hit its bound.
  truncated : Int
} derive(Debug)
