///|
/// A readable form of a term, for the report and for debugging.
pub fn term_text(t : @core.Term) -> String {
  match t {
    Lit(n) => n.to_string()
    Var(id) => "v" + id.to_string()
    Add(a, b) => "(" + term_text(a) + " + " + term_text(b) + ")"
    Sub(a, b) => "(" + term_text(a) + " - " + term_text(b) + ")"
    MulLit(a, k) => "(" + term_text(a) + " * " + k.to_string() + ")"
    DivLit(a, k) => "(" + term_text(a) + " / " + k.to_string() + ")"
    ModLit(a, k) => "(" + term_text(a) + " % " + k.to_string() + ")"
    Div(a, b) => "(" + term_text(a) + " / " + term_text(b) + ")"
    Rem(a, b) => "(" + term_text(a) + " % " + term_text(b) + ")"
    Neg(a) => "-" + term_text(a)
    Abs(a) => "|" + term_text(a) + "|"
    Wrap(a, w) => "wrap" + w.to_string() + "(" + term_text(a) + ")"
    Ite(c, a, b) => "if " + term_text(c) + " then " + term_text(a) + " else " + term_text(b)
    Lt(a, b) => term_text(a) + " < " + term_text(b)
    Le(a, b) => term_text(a) + " <= " + term_text(b)
    Eq(a, b) => term_text(a) + " == " + term_text(b)
    Ne(a, b) => term_text(a) + " != " + term_text(b)
    Not(a) => "!" + term_text(a)
    And(a, b) => "(" + term_text(a) + " && " + term_text(b) + ")"
    Or(a, b) => "(" + term_text(a) + " || " + term_text(b) + ")"
    True => "true"
    False => "false"
  }
}
