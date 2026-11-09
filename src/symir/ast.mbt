pub(all) enum Expr {
  IntLit(IntLitExpr)
  VarRef(VarExpr)
  Bin(BinExpr)
  Un(UnExpr)
  /// `if c { a } else { b }` as an expression.
  Ite(IteExpr)
  /// A call whose value is used.
  App(AppExpr)
  /// `len(a)` — a symbolic length, non-negative and never wrapped.
  Len(LenExpr)
} derive(Debug)

///|
pub(all) struct IntLitExpr {
  value : Int
  line : Int32
} derive(Debug)

///|
pub(all) struct VarExpr {
  name : String
  line : Int32
} derive(Debug)

///|
pub(all) struct BinExpr {
  op : BinOp
  lhs : Expr
  rhs : Expr
  line : Int32
} derive(Debug)

///|
pub(all) struct UnExpr {
  op : UnOp
  operand : Expr
  line : Int32
} derive(Debug)

///|
pub(all) struct IteExpr {
  cond : Expr
  then_ : Expr
  else_ : Expr
  line : Int32
} derive(Debug)

///|
pub(all) struct AppExpr {
  name : String
  args : Array[Expr]
  line : Int32
} derive(Debug)

///|
pub(all) struct LenExpr {
  name : String
  line : Int32
} derive(Debug)

///|

pub(all) enum BinOp {
  Add
  Sub
  Mul
  Div
  Mod
  Lt
  Le
  Gt
  Ge
  Eq
  Ne
  And
  Or
} derive(Debug, Eq)

///|
pub(all) enum UnOp {
  Neg
  Not
} derive(Debug, Eq)


pub(all) enum Stmt {
  /// `let x = e` (immutable) or `let mut x = e`
  Let(LetStmt)
  /// `x = e`
  Assign(AssignStmt)
  /// `if c { ... } else { ... }`
  If(IfStmt)
  /// `while c invariant I { ... }` — the invariant is checked at the head and
  /// by the body, which is how a loop becomes a finite proof.
  While(WhileStmt)
  /// `return e`
  Ret(RetStmt)
  /// `assert c`
  Assert(AssertStmt)
  /// A call to a declared function, used as a statement.
  Call(CallStmt)
} derive(Debug)

///|
pub(all) struct LetStmt {
  name : String
  value : Expr
  mutable_ : Bool
  line : Int32
} derive(Debug)

///|
pub(all) struct AssignStmt {
  name : String
  value : Expr
  line : Int32
} derive(Debug)

///|
pub(all) struct IfStmt {
  cond : Expr
  then_ : Array[Stmt]
  else_ : Array[Stmt]
  line : Int32
} derive(Debug)

///|
pub(all) struct WhileStmt {
  cond : Expr
  invariants : Array[Expr]
  body : Array[Stmt]
  line : Int32
} derive(Debug)

///|
pub(all) struct RetStmt {
  value : Expr
  line : Int32
} derive(Debug)

///|
pub(all) struct AssertStmt {
  cond : Expr
  line : Int32
} derive(Debug)

///|
pub(all) struct CallStmt {
  name : String
  args : Array[Expr]
  line : Int32
} derive(Debug)

///|
/// An expression.

pub(all) struct Program {
  functions : Array[Fn]
  /// Names the parser rejected, with the reason. A program with errors is not
  /// verified at all.
  errors : Array[String]
} derive(Debug)

///|
/// One function: parameters, a body of statements, and where it starts.
pub(all) struct Fn {
  name : String
  params : Array[Param]
  body : Array[Stmt]
  /// Contracts the author wrote. `require` must hold on entry, `ensure` on
  /// exit, `invariant` at every loop head.
  requires : Array[Expr]
  ensures : Array[Expr]
  line : Int32
} derive(Debug)

///|
/// A parameter: its name and whether it is constrained non-negative.
pub(all) struct Param {
  name : String
  /// `Nat` parameters are array lengths and counter bounds; they are assumed
  /// non-negative and never wrapped.
  nat : Bool
} derive(Debug)

///|
/// A statement.
