import Wiz.Parser.Interp
import Wiz.Parser.Builtin
import Wiz.Parser.SyntaxCmd

/-!
# Parsing a file

Files are parsed **one command at a time**, because a command such as `syntax` can
change the grammar used for the next one. Stage 3's frontend interleaves parsing with
elaboration in the same way. This module provides the pieces and a parse-only driver
for `wiz parse`.

**Error recovery:** after a parse error, skip from the start of the failed command to
the next line that starts in column 0
and carry on. One bad command then produces one error instead of ending the whole
file. The LSP needs this.
-/

namespace Wiz

structure Message where
  pos : Nat
  msg : String
  deriving Repr, Inhabited

def Message.render (input : String) (m : Message) : String :=
  let (l, c) := lineCol input m.pos
  s!"{l + 1}:{c + 1}: {m.msg}"

/-- Parse the command starting at (or after whitespace following) `pos`. -/
def parseCommand (chars : Array Char) (tables : ParserTables) (pos : Nat) :
    Except ParseError (Syntax × Nat) :=
  (runDescr (.withPosition (.cat "command" 0)) >>= fun r => pure r[0]!).run chars tables pos

/-- The start of the next line beginning in column 0 with a non-space character,
strictly after `pos`. -/
def recoverPos (chars : Array Char) (pos : Nat) : Nat := Id.run do
  let mut i := pos + 1
  while i < chars.size do
    if chars[i - 1]! == '\n' && !chars[i]!.isWhitespace then return i
    i := i + 1
  chars.size

/-- Grammar-changing commands. Everything else leaves the tables alone. -/
def updateTables (tables : ParserTables) (cmd : Syntax) : Except String ParserTables :=
  match cmd.kind with
  | "command.declareSyntaxCat" => match (cmd.getArg 1).getId? with
    | some c => pure (Builtin.addMetaParsers (tables.declareCategory c) c)
    | none => throw "malformed declare_syntax_cat"
  | "command.syntax" => addSyntax tables cmd
  | _ => pure tables

structure ParsedFile where
  commands : Array Syntax := #[]
  messages : Array Message := #[]
  tables : ParserTables

/-- Parse a whole file, applying grammar-changing commands as they are seen. -/
partial def parseFile (input : String) (tables : ParserTables := Builtin.tables) : ParsedFile :=
  let chars := input.toList.toArray
  go chars 0 { tables }
where
  go (chars : Array Char) (pos : Nat) (acc : ParsedFile) : ParsedFile :=
    if skipWs chars pos ≥ chars.size then acc else
    match parseCommand chars acc.tables pos with
    | .ok (cmd, stop) =>
      match updateTables acc.tables cmd with
      | .ok tables => go chars stop { acc with commands := acc.commands.push cmd, tables }
      | .error msg =>
        go chars stop { acc with
          commands := acc.commands.push cmd
          messages := acc.messages.push { pos := cmd.info.start, msg } }
    | .error e =>
      let msg := (e.render input).splitOn ": " |>.drop 1 |> ": ".intercalate
      go chars (recoverPos chars (skipWs chars pos)) { acc with messages := acc.messages.push { pos := e.pos, msg } }

end Wiz
