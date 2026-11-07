import Lean.Data.Json
import Wiz.Query
import Wiz.Rig.Instances

/-!
# The language server

`wiz lsp` speaks the Language Server Protocol over stdin/stdout: JSON-RPC messages with
`Content-Length` headers. It keeps every open document's text and a query engine
(`Query.lean`), so after an edit only the commands from the edit on are elaborated
again. Supported: diagnostics (`publishDiagnostics`), hover (the type of the identifier
under the cursor), go to definition (also into libraries), and completion of global
names.

Positions: LSP counts lines and UTF-16 code units; we count Unicode characters, which
agree except for characters outside the Basic Multilingual Plane.
-/

namespace Wiz.LSP

open Lean (Json)

abbrev St := CommandState ZeroOneMany

structure Doc where
  text : String
  engine : Query.Engine ZeroOneMany := {}
  state : St := {}

structure Server where
  docs : Std.HashMap String Doc := {}
  /-- library modules: name ↦ (path, source) -/
  libs : Std.HashMap String (String × String) := {}

/-- Line and column (0-based) of a character offset. -/
def toPos (text : String) (off : Nat) : Json :=
  let pre := (text.toList.take off)
  let line := pre.count '\n'
  let col := (pre.reverse.takeWhile (· != '\n')).length
  Json.mkObj [("line", line), ("character", col)]

/-- The character offset of an LSP position. -/
def ofPos (text : String) (line col : Nat) : Nat := Id.run do
  let cs := text.toList
  let mut l := 0
  let mut i := 0
  while l < line && i < cs.length do
    if cs[i]! == '\n' then l := l + 1
    i := i + 1
  pure (i + col)

def range (text : String) (info : SourceInfo) : Json :=
  Json.mkObj [("start", toPos text info.start), ("end", toPos text (max info.stop (info.start + 1)))]

/-- Elaborate a document (incrementally) with the libraries available to `import`. -/
def elaborate (srv : Server) (doc : Doc) : Doc :=
  let libs := srv.libs
  let init : St := { loader := fun m => (libs.get? m).map (·.2) }
  let key₀ := hash (libs.toList.map (·.2.2) |>.toString)
  let (s, eng) := Query.elaborate doc.engine doc.text init key₀
  { doc with state := s, engine := eng }

def diagnostics (uri : String) (doc : Doc) : Json :=
  let ds := doc.state.messages.toList.map fun m =>
    Json.mkObj [("range", range doc.text m.info),
                ("severity", (if m.severity == .error then 1 else 3 : Nat)),
                ("source", "wiz"), ("message", m.text)]
  Json.mkObj [("jsonrpc", "2.0"), ("method", "textDocument/publishDiagnostics"),
              ("params", Json.mkObj [("uri", uri), ("diagnostics", Json.arr ds.toArray)])]

def capabilities : Json :=
  Json.mkObj [("capabilities", Json.mkObj [
    ("textDocumentSync", (1 : Nat)), ("hoverProvider", true), ("definitionProvider", true),
    ("completionProvider", Json.mkObj [("triggerCharacters", Json.arr #["."])])]),
    ("serverInfo", Json.mkObj [("name", "wiz")])]

/-- The JSON number or string at `path`, if any. -/
def get? (j : Json) (path : List String) : Option Json :=
  path.foldlM (fun j k => (j.getObjVal? k).toOption) j

def getStr (j : Json) (path : List String) : String :=
  match get? j path with
  | some (.str s) => s
  | _ => ""

def getNat (j : Json) (path : List String) : Nat :=
  match get? j path with
  | some j => (j.getNat?.toOption).getD 0
  | none => 0

/-- Handle one message; returns the replies (and notifications) to send. -/
def handle (srv : Server) (msg : Json) : Server × Array Json := Id.run do
  let method := getStr msg ["method"]
  let id := (msg.getObjVal? "id").toOption
  let reply (result : Json) : Json :=
    Json.mkObj [("jsonrpc", "2.0"), ("id", id.getD Json.null), ("result", result)]
  let uri := getStr msg ["params", "textDocument", "uri"]
  match method with
  | "initialize" => (srv, #[reply capabilities])
  | "shutdown" => (srv, #[reply Json.null])
  | "textDocument/didOpen" | "textDocument/didChange" =>
    let text := if method == "textDocument/didOpen" then getStr msg ["params", "textDocument", "text"]
      else match get? msg ["params", "contentChanges"] with
        | some (.arr cs) => match cs.back? with
          | some c => getStr c ["text"]
          | none => ""
        | _ => ""
    let old := (srv.docs.get? uri).getD { text }
    let doc := elaborate srv { old with text }
    ({ srv with docs := srv.docs.insert uri doc }, #[diagnostics uri doc])
  | "textDocument/didClose" => ({ srv with docs := srv.docs.erase uri }, #[])
  | "textDocument/hover" | "textDocument/definition" | "textDocument/completion" =>
    let some doc := srv.docs.get? uri | return (srv, #[reply Json.null])
    let off := ofPos doc.text (getNat msg ["params", "position", "line"]) (getNat msg ["params", "position", "character"])
    match method with
    | "textDocument/hover" =>
      match Query.hoverAt doc.state off with
      | some (n, ty) =>
        let md := s!"```wiz\n{n} : {ty}\n```"
        (srv, #[reply (Json.mkObj [("contents", Json.mkObj [("kind", "markdown"), ("value", md)])])])
      | none => (srv, #[reply Json.null])
    | "textDocument/definition" =>
      match Query.definitionAt doc.state off with
      | some (_, info, "") => (srv, #[reply (Json.mkObj [("uri", uri), ("range", range doc.text info)])])
      | some (_, info, m) =>
        match srv.libs.get? m with
        | some (path, src) =>
          (srv, #[reply (Json.mkObj [("uri", "file://" ++ path), ("range", range src info)])])
        | none => (srv, #[reply Json.null])
      | none => (srv, #[reply Json.null])
    | _ =>
      let names : Array Name := Query.completionsAt doc.state doc.text off
      let items : Array Json := names.map fun (n : Name) => Json.mkObj [("label", Json.str n), ("kind", (3 : Nat))]
      (srv, #[reply (Json.arr items)])
  | _ => (srv, if id.isSome then #[reply Json.null] else #[])

/-- Read one message: headers, a blank line, then `Content-Length` bytes of JSON. -/
partial def readMessage (stdin : IO.FS.Stream) : IO (Option Json) := do
  let mut len := 0
  repeat
    let line ← stdin.getLine
    if line.isEmpty then return none
    let line := line.trimAscii.toString
    if line.isEmpty then break
    if line.startsWith "Content-Length:" then len := ((line.drop 15).trimAscii.toString).toNat!
  let body ← stdin.read len.toUSize
  match Json.parse (String.fromUTF8! body) with
  | .ok j => pure (some j)
  | .error _ => pure (some Json.null)

def writeMessage (stdout : IO.FS.Stream) (j : Json) : IO Unit := do
  let body := j.compress
  stdout.putStr s!"Content-Length: {body.utf8ByteSize}\r\n\r\n{body}"
  stdout.flush

/-- Serve until `exit`. -/
partial def serve (libs : Std.HashMap String (String × String)) : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let rec loop (srv : Server) : IO Unit := do
    let some msg ← readMessage stdin | return
    if getStr msg ["method"] == "exit" then return
    let (srv, out) := handle srv msg
    for j in out do writeMessage stdout j
    loop srv
  loop { libs }

end Wiz.LSP
