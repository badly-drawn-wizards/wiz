import Lean.Data.Json
import Wiz.Query
import Wiz.Rig.Instances
import Wiz.Infoview
import Wiz.Actions

/-!
# The language server

`wiz lsp` speaks the Language Server Protocol over stdin/stdout: JSON-RPC messages with
`Content-Length` headers. It keeps every open document's text and a query engine
(`Query.lean`), so after an edit only the commands from the edit on are elaborated
again. Supported: diagnostics (`publishDiagnostics`), hover (the type of the identifier
under the cursor), go to definition (also into libraries), completion of global names,
and the infoview's requests (`wiz/plainGoal`, `wiz/interactiveGoals`, …; the protocol is
in `wiz-notes/infoview-protocol.md`): goals and expected types read from the info tree,
printed as tagged text whose tags are refs into the document's **session table**.

Positions: LSP counts lines and UTF-16 code units; we count Unicode characters, which
agree except for characters outside the Basic Multilingual Plane.
-/

namespace Wiz.LSP

open Lean (Json)

abbrev St := CommandState ZeroOneMany

structure Doc where
  text : String
  version : Option Int := none
  engine : Query.Engine ZeroOneMany := {}
  state : St := {}
  /-- the session: refs in `table` are valid while it stays the same -/
  session : Nat := 0
  table : Array (Subterm ZeroOneMany) := #[]
  /-- interactive results already given in this session (so polling reuses their refs) -/
  memo : Std.HashMap String Json := {}
  /-- code actions offered in this session, for `codeAction/resolve` -/
  actions : Array Actions.Action := #[]

structure Server where
  docs : Std.HashMap String Doc := {}
  /-- library modules: name ↦ (path, source) -/
  libs : Std.HashMap String (String × String) := {}
  /-- the last session number handed out (sessions are unique over the server's life) -/
  sessions : Nat := 0
  /-- the client asked for `wiz/elaborated` notifications -/
  elaboratedNotes : Bool := false
  /-- the client resolves code actions' edits lazily (`codeAction/resolve`) -/
  resolveEdits : Bool := false

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
  let init : St := { loader := fun m => (libs.get? m).map (·.2), termInfo := true }
  let key₀ := hash (libs.toList.map (·.2.2) |>.toString)
  let (s, eng) := Query.elaborate doc.engine doc.text init key₀
  { doc with state := s, engine := eng }

def diagnostic (doc : Doc) (m : Msg) : Json :=
  let code := if m.code.isEmpty then [] else
    [("code", Json.str m.code),
     ("data", Json.mkObj ((Actions.messageData doc.state m).map fun (k, vs) =>
        (k, if k == "name" then Json.str (vs.headD "") else Json.arr (vs.map Json.str).toArray)))]
  Json.mkObj ([("range", range doc.text m.info),
               ("severity", (match m.severity with | .error => 1 | .warning => 2 | .info => 3 : Nat)),
               ("source", "wiz"), ("message", m.text)] ++ code)

def diagnostics (uri : String) (doc : Doc) : Json :=
  let ds := doc.state.messages.toList.map (diagnostic doc)
  Json.mkObj [("jsonrpc", "2.0"), ("method", "textDocument/publishDiagnostics"),
              ("params", Json.mkObj [("uri", uri), ("diagnostics", Json.arr ds.toArray)])]

def infoviewMethods : List String :=
  ["wiz/plainGoal", "wiz/plainTermGoal", "wiz/interactiveGoals", "wiz/interactiveTermGoal", "wiz/subtermInfo"]

def capabilities : Json :=
  Json.mkObj [("capabilities", Json.mkObj [
    ("textDocumentSync", (1 : Nat)), ("hoverProvider", true), ("definitionProvider", true),
    ("completionProvider", Json.mkObj [("triggerCharacters", Json.arr #["."])]),
    ("codeActionProvider", Json.mkObj [("codeActionKinds", Json.arr #["quickfix", "refactor.rewrite"]),
                                       ("resolveProvider", true)]),
    ("experimental", Json.mkObj [("wizInfoview", Json.mkObj [("version", (1 : Nat)),
      ("methods", Json.arr (infoviewMethods.map Json.str).toArray),
      ("notifications", Json.arr #["wiz/elaborated"])])])]),
    ("serverInfo", Json.mkObj [("name", "wiz")])]

/-! ## The infoview -/

/-- Tagged text as JSON; the tags' ids are shifted by `base` (the table's size before). -/
partial def ttJson (subs : Array (Subterm ZeroOneMany)) (base : Nat) : TT → Json
  | .text s => Json.mkObj [("text", s)]
  | .append xs => Json.mkObj [("append", Json.arr (xs.map (ttJson subs base)))]
  | .tag id t =>
    let sub := subs[id]!
    let tag := Json.mkObj ([("ref", Json.num (base + id)), ("kind", Json.str sub.kind)] ++
      (sub.name.toList.map fun n => ("name", Json.str n)))
    Json.mkObj [("tag", Json.arr #[tag, ttJson subs base t])]

/-- Run a tagged printer, adding its subterms to the document's table. -/
def withTable (doc : Doc) (x : StateM (Array (Subterm ZeroOneMany)) α) (k : α → (TT → Json) → Json) : Doc × Json :=
  let (a, subs) := x.run #[]
  let base := doc.table.size
  ({ doc with table := doc.table ++ subs }, k a (ttJson subs base))

def goalJson (g : TaggedGoal) (tj : TT → Json) : Json :=
  Json.mkObj [
    ("hyps", Json.arr (g.hyps.map fun (x, t, v) => Json.mkObj [("names", Json.arr #[Json.str x]),
      ("type", tj t), ("val", match v with | some v => tj v | none => Json.null)])),
    ("type", tj g.target), ("goalPrefix", "⊢ "),
    ("userName", match g.userName with | some n => Json.str n | none => Json.null)]

def plainGoals (gs : Array (GoalView ZeroOneMany)) : Json :=
  let shown := gs.map (·.show)
  let rendered := if shown.isEmpty then "no goals" else s!"```wiz\n{"\n\n".intercalate shown.toList}\n```"
  Json.mkObj [("rendered", rendered), ("goals", Json.arr (shown.map Json.str))]

/-- Where a library module's source is, as a URI. -/
def location (srv : Server) (uri : String) (doc : Doc) (n : Name) : Json :=
  match doc.state.declSites.get? n with
  | some (info, "") => Json.mkObj [("uri", uri), ("range", range doc.text info)]
  | some (info, m) => match srv.libs.get? m with
    | some (path, src) => Json.mkObj [("uri", "file://" ++ path), ("range", range src info)]
    | none => Json.null
  | none => Json.null

/-- The type of a subterm, from the kernel, if every variable in scope has a known type. -/
def subtermType (g : Globals ZeroOneMany) (sub : Subterm ZeroOneMany) : Option (Term ZeroOneMany) := do
  let tys ← sub.types.reverse.mapM id
  let ctx := (sub.names.reverse.zip tys).foldl (fun (ctx : Ctx ZeroOneMany) (x, ty) =>
    ctx.bind x (QPoly.const QuantitySyntax.explicitDefault) (Wiz.eval g ctx.env ty)) { globals := g, erased := true }
  match Wiz.infer ctx sub.term with
  | .ok (ty, _) => some (quote g ctx.lvl ty)
  | .error _ => none

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

/-- Answer an infoview request on an open document. -/
def infoview (srv : Server) (uri : String) (doc : Doc) (method : String) (msg : Json) :
    Except (Int × String) (Doc × Json) := do
  let st := doc.state
  let off := ofPos doc.text (getNat msg ["params", "position", "line"]) (getNat msg ["params", "position", "character"])
  let memo (key : String) (x : Doc × Json) : Doc × Json :=
    match doc.memo.get? key with
    | some j => (doc, j)
    | none => let (d, j) := x; ({ d with memo := d.memo.insert key j }, j)
  match method with
  | "wiz/plainGoal" =>
    pure (doc, match Query.goalsAt st off with
      | some (_, _, gs) => plainGoals gs
      | none => Json.null)
  | "wiz/plainTermGoal" =>
    pure (doc, match Query.termGoalAt st off with
      | some (info, g) => Json.mkObj [("goal", g.show), ("range", range doc.text info)]
      | none => Json.null)
  | "wiz/interactiveGoals" =>
    match Query.goalsAt st off with
    | none => pure (doc, Json.null)
    | some (key, info, gs) =>
      let k (tgs : Array TaggedGoal) (tj : TT → Json) : Json :=
        Json.mkObj [("goals", Json.arr (tgs.map (goalJson · tj))), ("range", range doc.text info),
                    ("session", doc.session)]
      pure (memo s!"goals {key}" (withTable doc (gs.mapM (·.tagged)) k))
  | "wiz/interactiveTermGoal" =>
    match Query.termGoalAt st off with
    | none => pure (doc, Json.null)
    | some (info, g) =>
      let k (tg : TaggedGoal) (tj : TT → Json) : Json :=
        Json.mkObj [("goal", goalJson tg tj), ("range", range doc.text info), ("session", doc.session)]
      pure (memo s!"term {info.start} {info.stop}" (withTable doc g.tagged k))
  | _ => -- wiz/subtermInfo
    let some session := (get? msg ["params", "session"]).bind (·.getNat?.toOption) | throw (-32602, "missing session")
    let some r := (get? msg ["params", "ref"]).bind (·.getNat?.toOption) | throw (-32602, "missing ref")
    if session != doc.session then throw (-32801, "stale session")
    let some sub := doc.table[r]? | throw (-32801, "unknown ref")
    let defn := match sub.kind, sub.name with
      | "const", some n => location srv uri doc n
      | _, _ => Json.null
    let k (ty : Option TT) (tj : TT → Json) : Json :=
      Json.mkObj [("text", sub.term.pretty sub.names), ("kind", sub.kind),
        ("name", match sub.name with | some n => Json.str n | none => Json.null),
        ("type", match ty with | some t => tj t | none => Json.null),
        ("definition", defn), ("session", doc.session)]
    pure (memo s!"sub {r}" (withTable doc ((subtermType st.globals sub).mapM (·.prettyTagged sub.names sub.types)) k))

/-- A code action as JSON: with its edit, or (`resolveId`) with what `codeAction/resolve` needs. -/
def codeAction (uri : String) (doc : Doc) (a : Actions.Action) (resolveId : Option Nat) : Json :=
  let diags := match a.fixes.bind (doc.state.messages[·]?) with
    | some m => [("diagnostics", Json.arr #[diagnostic doc m])]
    | none => []
  let rest := match resolveId with
    | some k => [("data", Json.mkObj [("uri", uri), ("session", doc.session), ("id", k)])]
    | none =>
      let edits := a.edits.map fun e =>
        Json.mkObj [("range", Json.mkObj [("start", toPos doc.text e.start), ("end", toPos doc.text e.stop)]),
                    ("newText", e.text)]
      [("edit", Json.mkObj [("changes", Json.mkObj [(uri, Json.arr edits)])])]
  Json.mkObj ([("title", Json.str a.title), ("kind", Json.str a.kind)] ++ diags ++ rest)

/-- Handle one message; returns the replies (and notifications) to send. -/
def handle (srv : Server) (msg : Json) : Server × Array Json := Id.run do
  let method := getStr msg ["method"]
  let id := (msg.getObjVal? "id").toOption
  let reply (result : Json) : Json :=
    Json.mkObj [("jsonrpc", "2.0"), ("id", id.getD Json.null), ("result", result)]
  let replyError (code : Int) (message : String) : Json :=
    Json.mkObj [("jsonrpc", "2.0"), ("id", id.getD Json.null),
                ("error", Json.mkObj [("code", code), ("message", message)])]
  let uri := getStr msg ["params", "textDocument", "uri"]
  match method with
  | "initialize" =>
    let wants := get? msg ["params", "capabilities", "experimental", "wizElaborated"] == some (Json.bool true)
    let resolve := match get? msg ["params", "capabilities", "textDocument", "codeAction", "resolveSupport", "properties"] with
      | some (.arr ps) => ps.contains (Json.str "edit")
      | _ => false
    ({ srv with elaboratedNotes := wants, resolveEdits := resolve }, #[reply capabilities])
  | "shutdown" => (srv, #[reply Json.null])
  | "textDocument/didOpen" | "textDocument/didChange" =>
    let text := if method == "textDocument/didOpen" then getStr msg ["params", "textDocument", "text"]
      else match get? msg ["params", "contentChanges"] with
        | some (.arr cs) => match cs.back? with
          | some c => getStr c ["text"]
          | none => ""
        | _ => ""
    let version := (get? msg ["params", "textDocument", "version"]).bind (·.getInt?.toOption)
    let old := (srv.docs.get? uri).getD { text }
    let session := srv.sessions + 1
    let doc := elaborate srv { old with text, version, session, table := #[], memo := {}, actions := #[] }
    let note := Json.mkObj [("jsonrpc", "2.0"), ("method", "wiz/elaborated"),
      ("params", Json.mkObj [("uri", uri), ("version", match version with | some v => Json.num v | none => Json.null),
                             ("session", session)])]
    ({ srv with docs := srv.docs.insert uri doc, sessions := session },
     #[diagnostics uri doc] ++ (if srv.elaboratedNotes then #[note] else #[]))
  | "textDocument/didClose" => ({ srv with docs := srv.docs.erase uri }, #[])
  | "textDocument/codeAction" =>
    let some doc := srv.docs.get? uri | return (srv, #[reply (Json.arr #[])])
    let pos (k : String) := ofPos doc.text (getNat msg ["params", "range", k, "line"]) (getNat msg ["params", "range", k, "character"])
    let acts := Actions.actionsAt doc.state doc.text (pos "start") (pos "end")
    let base := doc.actions.size
    let json := acts.mapIdx fun i a => codeAction uri doc a (if srv.resolveEdits then some (base + i) else none)
    ({ srv with docs := srv.docs.insert uri { doc with actions := doc.actions ++ acts } }, #[reply (Json.arr json)])
  | "codeAction/resolve" =>
    let auri := getStr msg ["params", "data", "uri"]
    let some doc := srv.docs.get? auri | return (srv, #[replyError (-32801) "unknown document"])
    let some session := (get? msg ["params", "data", "session"]).bind (·.getNat?.toOption) | return (srv, #[replyError (-32602) "missing session"])
    let some k := (get? msg ["params", "data", "id"]).bind (·.getNat?.toOption) | return (srv, #[replyError (-32602) "missing id"])
    if session != doc.session then return (srv, #[replyError (-32801) "the document changed"])
    let some a := doc.actions[k]? | return (srv, #[replyError (-32801) "unknown action"])
    (srv, #[reply (codeAction auri doc a none)])
  | "wiz/plainGoal" | "wiz/plainTermGoal" | "wiz/interactiveGoals" | "wiz/interactiveTermGoal" | "wiz/subtermInfo" =>
    let some doc := srv.docs.get? uri | return (srv, #[replyError (-32602) s!"unknown document {uri}"])
    match infoview srv uri doc method msg with
    | .ok (doc, j) => ({ srv with docs := srv.docs.insert uri doc }, #[reply j])
    | .error (c, m) => (srv, #[replyError c m])
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
