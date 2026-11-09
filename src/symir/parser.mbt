// The parser: tokens to the surface AST.
//
// Recursive descent, one function per precedence level, which is the only
// structure where "what does this accept" is answerable by reading it. Every
// failure carries the line it happened on.

///|
/// Parse a whole source file.
pub fn parse(source : String) -> Program {
  let lexed = lex(source)
  let errors : Array[String] = []
  for e in lexed.errors {
    errors.push(e)
  }
  let state : PState = { tokens: lexed.tokens, pos: 0, errors, }
  let functions : Array[Fn] = []
  while !at_eof(state) {
    match parse_fn(state) {
      Some(f) => functions.push(f)
      None => {
        // The parse function already recorded why; stop rather than loop.
        break
      }
    }
  }
  { functions, errors, }
}

///|
/// Parser state: the token stream, a cursor, and the errors found so far.
priv struct PState {
  tokens : Array[Token]
  mut pos : Int
  errors : Array[String]
}

///|
fn peek(state : PState) -> Token {
  if state.pos < state.tokens.length() {
    state.tokens[state.pos]
  } else {
    { tok: Tok::Eof, line: 0, col: 0 }
  }
}

///|
fn at_eof(state : PState) -> Bool {
  match peek(state).tok {
    Tok::Eof => true
    _ => false
  }
}

///|
fn advance(state : PState) -> Token {
  let token = peek(state)
  state.pos = state.pos + 1
  token
}

///|
fn error_at(state : PState, line : Int32, message : String) -> Unit {
  state.errors.push("line " + line.to_string() + ": " + message)
}

///|
fn is_punct_tok(state : PState, text : String) -> Bool {
  match peek(state).tok {
    Tok::Punct(p) => p == text
    _ => false
  }
}

///|
fn eat_punct(state : PState, text : String) -> Bool {
  if is_punct_tok(state, text) {
    ignore(advance(state))
    true
  } else {
    false
  }
}

///|
fn expect_punct(state : PState, text : String) -> Bool {
  if eat_punct(state, text) {
    true
  } else {
    error_at(state, peek(state).line, "expected '" + text + "'")
    false
  }
}

///|
fn eat_ident(state : PState, word : String) -> Bool {
  match peek(state).tok {
    Tok::Ident(name) =>
      if name == word {
        ignore(advance(state))
        true
      } else {
        false
      }
    _ => false
  }
}

///|
fn expect_ident(state : PState) -> String {
  match peek(state).tok {
    Tok::Ident(name) => {
      ignore(advance(state))
      if is_keyword(name) {
        error_at(state, peek(state).line, "expected a name, found keyword " + name)
      }
      name
    }
    _ => {
      error_at(state, peek(state).line, "expected a name")
      ""
    }
  }
}

///|
/// One function: optional contracts, the signature, then a block.
fn parse_fn(state : PState) -> Fn? {
  let requires : Array[Expr] = []
  let ensures : Array[Expr] = []
  // Contracts come before the signature so they read like a specification.
  while true {
    if eat_ident(state, "require") {
      match parse_expr(state) {
        Some(e) => requires.push(e)
        None => return None
      }
      ignore(eat_punct(state, ";"))
      continue
    }
    if eat_ident(state, "ensure") {
      match parse_expr(state) {
        Some(e) => ensures.push(e)
        None => return None
      }
      ignore(eat_punct(state, ";"))
      continue
    }
    break
  }
  if !eat_ident(state, "fn") {
    error_at(state, peek(state).line, "expected 'fn'")
    return None
  }
  let start_line = peek(state).line
  let name = expect_ident(state)
  if !expect_punct(state, "(") {
    return None
  }
  let params : Array[Param] = []
  if !is_punct_tok(state, ")") {
    while true {
      let mut nat = false
      // `nat n` marks n as a natural. `nat` alone followed by `:` is a parameter
      // *named* nat, which is legal and reads naturally in a spec about lengths.
      if is_punct_tok_at(state, 1, ":") == false && eat_ident(state, "nat") {
        nat = true
      }
      let pname = match peek(state).tok {
        Tok::Ident(name) => {
          ignore(advance(state))
          name
        }
        _ => {
          error_at(state, peek(state).line, "expected a parameter name")
          ""
        }
      }
      // `name : Type` — the annotation is accepted and ignored. The surface
      // language has one annotation that changes meaning, `nat`, and it is
      // spelled as a prefix so it cannot be lost in a type name.
      if eat_punct(state, ":") {
        // The annotation is consumed as a bare word. `nat` is the one type that
        // changes meaning — a length or counter, assumed non-negative and never
        // wrapped — so it is honoured in either position: `nat n` and `n : nat`
        // say the same thing.
        match peek(state).tok {
          Tok::Ident(type_name) => {
            ignore(advance(state))
            if type_name == "nat" {
              nat = true
            }
          }
          _ => error_at(state, peek(state).line, "expected a type name")
        }
      }
      params.push({ name: pname, nat, })
      if !eat_punct(state, ",") {
        break
      }
    }
  }
  if !expect_punct(state, ")") {
    return None
  }
  // `-> Type` — accepted and ignored, for the same reason as a parameter
  // annotation: the surface language does not check types, and a spec that has to
  // omit them reads worse than one that may state them.
  if eat_punct(state, "-") && eat_punct(state, ">") {
    match peek(state).tok {
      Tok::Ident(_) => ignore(advance(state))
      _ => error_at(state, peek(state).line, "expected a return type")
    }
  }
  let body = parse_block(state)
  match body {
    None => None
    Some(stmts) => Some({ name, params, body: stmts, requires, ensures, line: start_line })
  }
}

///|
fn parse_block(state : PState) -> Array[Stmt]? {
  if !expect_punct(state, "{") {
    return None
  }
  let out : Array[Stmt] = []
  while !is_punct_tok(state, "}") && !at_eof(state) {
    match parse_stmt(state) {
      Some(s) => out.push(s)
      None => return None
    }
  }
  if !expect_punct(state, "}") {
    return None
  }
  Some(out)
}

///|
fn parse_stmt(state : PState) -> Stmt? {
  let line = peek(state).line
  if eat_ident(state, "let") {
    let mutable_ = eat_ident(state, "mut")
    let name = expect_ident(state)
    if !expect_punct(state, "=") {
      return None
    }
    match parse_expr(state) {
      None => None
      Some(value) => {
        ignore(eat_punct(state, ";"))
        Some(Stmt::Let({ name, value, mutable_, line }))
      }
    }
  } else if eat_ident(state, "if") {
    match parse_if_like(state, line) {
      None => None
      Some(pair) => Some(pair)
    }
  } else if eat_ident(state, "while") {
    let cond = match parse_expr(state) {
      Some(c) => c
      None => return None
    }
    let invariants : Array[Expr] = []
    while eat_ident(state, "invariant") {
      match parse_expr(state) {
        Some(inv) => invariants.push(inv)
        None => return None
      }
    }
    match parse_block(state) {
      None => None
      Some(body) => Some(Stmt::While({ cond, invariants, body, line }))
    }
  } else if eat_ident(state, "return") {
    match parse_expr(state) {
      None => None
      Some(value) => {
        ignore(eat_punct(state, ";"))
        Some(Stmt::Ret({ value, line }))
      }
    }
  } else if eat_ident(state, "assert") {
    match parse_expr(state) {
      None => None
      Some(cond) => {
        ignore(eat_punct(state, ";"))
        Some(Stmt::Assert({ cond, line }))
      }
    }
  } else {
    // An assignment or a call statement: `name = e` or `name(args)`.
    match peek(state).tok {
      Tok::Ident(name) => {
        ignore(advance(state))
        if eat_punct(state, "=") {
          match parse_expr(state) {
            None => None
            Some(value) => {
              ignore(eat_punct(state, ";"))
              Some(Stmt::Assign({ name, value, line }))
            }
          }
        } else if is_punct_tok(state, "(") {
          match parse_args(state) {
            None => None
            Some(args) => Some(Stmt::Call({ name, args, line }))
          }
        } else {
          error_at(state, line, "expected '=' or '(' after " + name)
          None
        }
      }
      _ => {
        error_at(state, line, "expected a statement")
        None
      }
    }
  }
}

///|
fn parse_if_like(state : PState, line : Int32) -> Stmt? {
  let cond = match parse_expr(state) {
    Some(c) => c
    None => return None
  }
  let then_ = match parse_block(state) {
    Some(b) => b
    None => return None
  }
  let else_ : Array[Stmt] = []
  if eat_ident(state, "else") {
    if eat_ident(state, "if") {
      // `else if` is a nested if in the else branch.
      match parse_if_like(state, peek(state).line) {
        None => return None
        Some(nested) => {
          else_.push(nested)
          return Some(Stmt::If({ cond, then_, else_, line }))
        }
      }
    }
    match parse_block(state) {
      None => return None
      Some(b) => {
        for s in b {
          else_.push(s)
        }
      }
    }
  }
  Some(Stmt::If({ cond, then_, else_, line }))
}

///|
fn parse_args(state : PState) -> Array[Expr]? {
  if !expect_punct(state, "(") {
    return None
  }
  let out : Array[Expr] = []
  if !is_punct_tok(state, ")") {
    while true {
      match parse_expr(state) {
        None => return None
        Some(e) => out.push(e)
      }
      if !eat_punct(state, ",") {
        break
      }
    }
  }
  if !expect_punct(state, ")") {
    return None
  }
  Some(out)
}

///|
/// Logical OR: the lowest precedence. `a || b || c` groups to the left.
fn parse_expr(state : PState) -> Expr? {
  let mut left = match parse_and(state) {
    Some(e) => e
    None => return None
  }
  while true {
    let line = peek(state).line
    if eat_punct(state, "||") {
      let right = match parse_and(state) {
        Some(e) => e
        None => return None
      }
      left = Expr::Bin({ op: BinOp::Or, lhs: left, rhs: right, line })
      continue
    }
    break
  }
  Some(left)
}

///|
/// Logical AND, binding tighter than OR and looser than comparison.
fn parse_and(state : PState) -> Expr? {
  let mut left = match parse_comparison(state) {
    Some(e) => e
    None => return None
  }
  while true {
    let line = peek(state).line
    if eat_punct(state, "&&") {
      let right = match parse_comparison(state) {
        Some(e) => e
        None => return None
      }
      left = Expr::Bin({ op: BinOp::And, lhs: left, rhs: right, line })
      continue
    }
    break
  }
  Some(left)
}

///|
/// Comparison, non-associative: `a < b < c` is rejected rather than guessed at,
/// because both readings (chained vs. left-grouped on 0/1) are surprising.
fn parse_comparison(state : PState) -> Expr? {
  let left = match parse_additive(state) {
    Some(e) => e
    None => return None
  }
  let line = peek(state).line
  let op = if eat_punct(state, "==") {
    Some(BinOp::Eq)
  } else if eat_punct(state, "!=") {
    Some(BinOp::Ne)
  } else if eat_punct(state, "<=") {
    Some(BinOp::Le)
  } else if eat_punct(state, ">=") {
    Some(BinOp::Ge)
  } else if eat_punct(state, "<") {
    Some(BinOp::Lt)
  } else if eat_punct(state, ">") {
    Some(BinOp::Gt)
  } else {
    None
  }
  match op {
    None => Some(left)
    Some(operator) => {
      let right = match parse_additive(state) {
        Some(e) => e
        None => return None
      }
      Some(Expr::Bin({ op: operator, lhs: left, rhs: right, line }))
    }
  }
}

///|
/// Arithmetic: `+` and `-`, left associative.
fn parse_additive(state : PState) -> Expr? {
  let mut left = match parse_term(state) {
    Some(e) => e
    None => return None
  }
  while true {
    let line = peek(state).line
    if eat_punct(state, "+") {
      let right = match parse_term(state) {
        Some(e) => e
        None => return None
      }
      left = Expr::Bin({ op: BinOp::Add, lhs: left, rhs: right, line })
      continue
    }
    if eat_punct(state, "-") {
      let right = match parse_term(state) {
        Some(e) => e
        None => return None
      }
      left = Expr::Bin({ op: BinOp::Sub, lhs: left, rhs: right, line })
      continue
    }
    break
  }
  Some(left)
}

///|
/// Multiplicative: `*`, `/`, `%`.
fn parse_term(state : PState) -> Expr? {
  let mut left = match parse_atom(state) {
    Some(e) => e
    None => return None
  }
  while true {
    let line = peek(state).line
    let op = if eat_punct(state, "*") {
      Some(BinOp::Mul)
    } else if eat_punct(state, "/") {
      Some(BinOp::Div)
    } else if eat_punct(state, "%") {
      Some(BinOp::Mod)
    } else {
      None
    }
    match op {
      None => break
      Some(operator) => {
        let right = match parse_atom(state) {
          Some(e) => e
          None => return None
        }
        left = Expr::Bin({ op: operator, lhs: left, rhs: right, line })
      }
    }
  }
  Some(left)
}

///|
/// Atoms: literals, names, calls, `len(x)`, parenthesised expressions, unary
/// minus, `if` expressions.
fn parse_atom(state : PState) -> Expr? {
  let line = peek(state).line
  match peek(state).tok {
    Tok::IntTok(n) => {
      ignore(advance(state))
      return Some(Expr::IntLit({ value: n, line }))
    }
    Tok::Punct(p) =>
      if p == "(" {
        ignore(advance(state))
        let inner = match parse_expr(state) {
          Some(e) => e
          None => return None
        }
        if !expect_punct(state, ")") {
          return None
        }
        return Some(inner)
      } else if p == "-" {
        ignore(advance(state))
        let operand = match parse_atom(state) {
          Some(e) => e
          None => return None
        }
        return Some(Expr::Un({ op: UnOp::Neg, operand, line }))
      } else if p == "!" {
        ignore(advance(state))
        let operand = match parse_atom(state) {
          Some(e) => e
          None => return None
        }
        return Some(Expr::Un({ op: UnOp::Not, operand, line }))
      } else {
        error_at(state, line, "expected an expression")
        None
      }
    Tok::Ident(name) =>
      if name == "true" {
        ignore(advance(state))
        return Some(Expr::IntLit({ value: 1, line }))
      } else if name == "false" {
        ignore(advance(state))
        return Some(Expr::IntLit({ value: 0, line }))
      } else if name == "len" {
        ignore(advance(state))
        if !expect_punct(state, "(") {
          return None
        }
        let target = expect_ident(state)
        if !expect_punct(state, ")") {
          return None
        }
        return Some(Expr::Len({ name: target, line }))
      } else if name == "if" {
        ignore(advance(state))
        let cond = match parse_expr(state) {
          Some(c) => c
          None => return None
        }
        if !expect_punct(state, "{") {
          return None
        }
        let then_ = match parse_expr(state) {
          Some(e) => e
          None => return None
        }
        if !expect_punct(state, "}") {
          return None
        }
        if !eat_ident(state, "else") {
          error_at(state, line, "an `if` expression needs `else`")
          return None
        }
        if !expect_punct(state, "{") {
          return None
        }
        let else_ = match parse_expr(state) {
          Some(e) => e
          None => return None
        }
        if !expect_punct(state, "}") {
          return None
        }
        Some(Expr::Ite({ cond, then_, else_, line }))
      } else if is_keyword(name) {
        error_at(state, line, "unexpected keyword " + name + " in an expression")
        None
      } else {
        ignore(advance(state))
        if is_punct_tok(state, "(") {
          match parse_args(state) {
            None => None
            Some(args) => return Some(Expr::App({ name, args, line }))
          }
        } else {
          return Some(Expr::VarRef({ name, line }))
        }
      }
    Tok::Eof => {
      error_at(state, line, "unexpected end of input")
      return None
    }
  }
}

///|
/// Whether the token at `offset` is the given punctuation. Used for the two-token
/// lookahead that tells `nat n` (a modifier) from `nat : T` (a name).
fn is_punct_tok_at(state : PState, offset : Int, text : String) -> Bool {
  let index = state.pos + offset
  if index >= state.tokens.length() {
    return false
  }
  match state.tokens[index].tok {
    Tok::Punct(p) => p == text
    _ => false
  }
}
