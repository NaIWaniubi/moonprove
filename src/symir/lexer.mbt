// A hand-written recursive-descent parser for the verifier's surface language.
//
// Why not reuse `moonbitlang/parser`: this language is a *subset* with contracts
// added, and a general MoonBit parser would accept far more than the verifier can
// reason about. A parser that accepts it, then a checker that rejects it, is two
// places to be wrong. Here, anything not understood is a parse error with a line.

///|
/// Token kinds. The lexer emits these plus their spans.
pub(all) enum Tok {
  /// An integer literal.
  IntTok(Int)
  /// An identifier or keyword; the parser decides which.
  Ident(String)
  /// Punctuation and operators.
  Punct(String)
  /// End of input.
  Eof
} derive(Debug, Eq)

///|
/// A token with its source position.
pub(all) struct Token {
  tok : Tok
  line : Int32
  col : Int32
} derive(Debug)

///|
/// The lexer's output: tokens or a lexical error.
pub(all) struct Lexed {
  tokens : Array[Token]
  errors : Array[String]
} derive(Debug)

///|
/// Keywords of the surface language. `invariant`, `require` and `ensure` are the
/// additions over plain MoonBit syntax.
fn is_keyword(word : String) -> Bool {
  match word {
    "fn" | "let" | "mut" | "if" | "else" | "while" | "return" | "assert" |
    "invariant" | "require" | "ensure" | "true" | "false" | "len" | "nat" => true
    _ => false
  }
}

///|
/// Split source into tokens. Comments (`//` to end of line) are dropped.
///
/// The lexer never throws: a stray character becomes an `errors` entry and the
/// scan continues, so the caller reports every problem in one pass.
pub fn lex(source : String) -> Lexed {
  let tokens : Array[Token] = []
  let errors : Array[String] = []
  let chars = source.to_array()
  let mut i = 0
  let mut line = 1
  let mut col = 1
  while i < chars.length() {
    let c = chars[i]
    if c == '\n' {
      line = line + 1
      col = 1
      i = i + 1
      continue
    }
    if c == ' ' || c == '\t' || c == '\r' {
      i = i + 1
      col = col + 1
      continue
    }
    if c == '/' && i + 1 < chars.length() && chars[i + 1] == '/' {
      while i < chars.length() && chars[i] != '\n' {
        i = i + 1
      }
      continue
    }
    if is_digit(c) {
      let start = i
      let start_col = col
      while i < chars.length() && is_digit(chars[i]) {
        i = i + 1
        col = col + 1
      }
      let text = slice_text(chars, start, i)
      let value = @string.parse_int(text) catch {
        _ => {
          errors.push("line " + line.to_string() + ": integer literal out of range: " + text)
          0
        }
      }
      tokens.push({ tok: Tok::IntTok(value), line, col: start_col })
      continue
    }
    if is_ident_start(c) {
      let start = i
      let start_col = col
      while i < chars.length() && is_ident_part(chars[i]) {
        i = i + 1
        col = col + 1
      }
      let text = slice_text(chars, start, i)
      tokens.push({ tok: Tok::Ident(text), line, col: start_col })
      continue
    }
    // Two-character operators first.
    let two = if i + 1 < chars.length() {
      slice_text(chars, i, i + 2)
    } else {
      ""
    }
    let three = if i + 2 < chars.length() {
      slice_text(chars, i, i + 3)
    } else {
      ""
    }
    if three == "==>" || three == "<==>" {
      errors.push("line \{line}: unsupported operator \{three}")
      i = i + 3
      col = col + 3
      continue
    }
    if two == "==" ||
      two == "!=" ||
      two == "<=" ||
      two == ">=" ||
      two == "&&" ||
      two == "||" {
      tokens.push({ tok: Tok::Punct(two), line, col })
      i = i + 2
      col = col + 2
      continue
    }
    if is_punct(c) {
      tokens.push({ tok: Tok::Punct(c.to_string()), line, col })
      i = i + 1
      col = col + 1
      continue
    }
    errors.push("line \{line}: unexpected character '\{c}'")
    i = i + 1
    col = col + 1
  }
  tokens.push({ tok: Tok::Eof, line, col })
  { tokens, errors }
}

///|
fn is_digit(c : Char) -> Bool {
  c.to_int() >= '0'.to_int() && c.to_int() <= '9'.to_int()
}

///|
fn is_ident_start(c : Char) -> Bool {
  let n = c.to_int()
  (n >= 'a'.to_int() && n <= 'z'.to_int()) ||
  (n >= 'A'.to_int() && n <= 'Z'.to_int()) ||
  c == '_'
}

///|
fn is_ident_part(c : Char) -> Bool {
  is_ident_start(c) || is_digit(c)
}

///|
fn is_punct(c : Char) -> Bool {
  match c {
    '(' | ')' | '{' | '}' | ',' | ';' | ':' | '+' | '-' | '*' | '/' | '%' |
    '<' | '>' | '=' | '!' | '&' | '|' => true
    _ => false
  }
}

///|
fn slice_text(chars : Array[Char], start : Int, end : Int) -> String {
  let out = StringBuilder()
  let mut i = start
  while i < end && i < chars.length() {
    out.write_char(chars[i])
    i = i + 1
  }
  out.to_string()
}
