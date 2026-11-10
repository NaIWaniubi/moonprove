// The CLI: three commands, one job each.
//
//   verify FILE            check a file's contracts and assertions
//   dump FILE              print the parsed program (for debugging a spec)
//   explain FILE           print the solver's narration for each goal
//
// Exit codes follow the Unix convention a CI expects: 0 everything proven,
// 1 something was violated, 2 usage or read error, 3 something could not be
// decided (a distinct code so CI can tell "not proven" from "disproven").

///|
let tool_version : String = "0.2.0"

///|
fn usage() -> Unit {
  println(
    "moonprove " + tool_version + " — bounded verification for MoonBit-like code\n\n" +
    "  verify FILE [--json] [--width N]   prove contracts and assertions\n" +
    "  explain FILE                       show the solver's narration\n" +
    "  dump FILE                          print the parsed program\n" +
    "  version | help\n\n" +
    "Exit codes: 0 proven, 1 violated, 2 usage or read error, 3 undecided.",
  )
}

///|
fn fail(code : Int, message : String) -> Unit {
  println("error: " + message)
  @sys.exit(code)
}

///|
fn main {
  let argv = @env.args()
  if argv.length() < 2 {
    usage()
    return
  }
  let command = argv[1]
  if command == "version" || command == "--version" {
    println("moonprove " + tool_version)
    return
  }
  if command == "help" || command == "--help" {
    usage()
    return
  }
  let mut path = ""
  let mut format = "text"
  let mut width = 32
  let mut i = 2
  while i < argv.length() {
    let arg = argv[i]
    if arg == "--json" {
      format = "json"
      i = i + 1
    } else if arg == "--format" {
      if i + 1 >= argv.length() {
        fail(2, "--format needs a value (text, json, sarif)")
      }
      format = argv[i + 1]
      if format != "text" && format != "json" && format != "sarif" {
        fail(2, "unknown format " + format + " (use text, json or sarif)")
      }
      i = i + 2
    } else if arg == "--width" {
      if i + 1 >= argv.length() {
        fail(2, "--width needs a value")
      }
      width = @string.parse_int(argv[i + 1]) catch {
        _ => {
          fail(2, "--width needs an integer")
          32
        }
      }
      i = i + 2
    } else if arg.has_prefix("-") {
      fail(2, "unknown flag " + arg)
    } else {
      if path != "" {
        fail(2, "one file at a time")
      }
      path = arg
      i = i + 1
    }
  }
  if path == "" {
    fail(2, "no file given")
  }
  let source = @fs.read_file_to_string(path) catch {
    @fs.IOError(msg) => {
      fail(2, "cannot read " + path + ": " + msg)
      ""
    }
  }
  match command {
    "verify" => run_verify(source, format, width, path)
    "explain" => run_explain(source)
    "dump" => run_dump(source)
    _ => fail(2, "unknown command " + command)
  }
}
