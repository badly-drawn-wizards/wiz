import Wiz
import Tests.Harness

open Wiz

set_option compiler.extract_closed false

namespace Tests.LSP

abbrev St := CommandState ZeroOneMany

def prelude : IO String := IO.FS.readFile "lib/Prelude.wiz"

/-- Elaborate `src` (which imports the prelude) as the language server does. -/
def elabSrc (src : String) (termInfo : Bool := true) : IO St := do
  let p ← prelude
  let init : St := { trustedModule := Tests.libModule, loader := fun m => if m == "Prelude" then some p else none, termInfo }
  pure (Query.elaborate {} src init).1

/-- The character offset just after the `k`th occurrence of `needle` (plus `delta`). -/
def offAfter (src needle : String) (delta : Int := 0) (k : Nat := 0) : Nat :=
  let pre := (src.splitOn needle).take (k + 1)
  let n := (needle.length * k) + (pre.foldl (· + ·.length) 0) + needle.length
  (n + delta).toNat

def goalsText (s : St) (off : Nat) : String :=
  match Query.goalsAt s off with
  | some (_, _, gs) => if gs.isEmpty then "no goals" else "\n\n".intercalate (gs.map (·.show)).toList
  | none => "none"

def termGoalText (s : St) (off : Nat) : String :=
  match Query.termGoalAt s off with
  | some (_, g) => g.show
  | none => "none"

/-! ## The language server, through `LSP.handle` -/

def req (s : String) : Lean.Json := (Lean.Json.parse s).toOption.get!

def server : IO LSP.Server := do
  pure { libs := ({} : Std.HashMap String (String × String)).insert "Prelude" ("lib/Prelude.wiz", ← prelude),
         trusted := ["Prelude"] }

def lineCol (src : String) (off : Nat) : Nat × Nat :=
  let pre := src.toList.take off
  (pre.count '\n', (pre.reverse.takeWhile (· != '\n')).length)

def posJson (src : String) (off : Nat) : String :=
  let (l, c) := lineCol src off
  s!"\{\"line\":{l},\"character\":{c}}"

/-- Open `src` as `file:///t.wiz`; returns the server and the messages it sent. -/
def openDoc (src : String) (init : Lean.Json := req "{\"jsonrpc\":\"2.0\",\"id\":0,\"method\":\"initialize\",\"params\":{}}") :
    IO (LSP.Server × Array Lean.Json) := do
  let (srv, _) := LSP.handle (← server) init
  let msg := Lean.Json.mkObj [("jsonrpc", "2.0"), ("method", "textDocument/didOpen"),
    ("params", Lean.Json.mkObj [("textDocument", Lean.Json.mkObj [("uri", "file:///t.wiz"), ("version", (1 : Nat)), ("text", src)])])]
  pure (LSP.handle srv msg)

/-- A request at a position; returns the server and the reply's `result` (or `error`). -/
def ask (srv : LSP.Server) (method : String) (src : String) (off : Nat) : LSP.Server × Lean.Json :=
  let (srv, out) := LSP.handle srv (req s!"\{\"jsonrpc\":\"2.0\",\"id\":9,\"method\":\"{method}\",\"params\":\{\"textDocument\":\{\"uri\":\"file:///t.wiz\"},\"position\":{posJson src off}}}")
  (srv, result out[0]!)
where
  result (j : Lean.Json) : Lean.Json :=
    (j.getObjVal? "result").toOption.getD ((j.getObjVal? "error").toOption.getD Lean.Json.null)

def has (j : Lean.Json) (s : String) : Bool := (j.compress.splitOn s).length > 1

/-- Concatenate the text of tagged text. -/
partial def flatten (j : Lean.Json) : String :=
  match (j.getObjVal? "text").toOption, (j.getObjVal? "append").toOption, (j.getObjVal? "tag").toOption with
  | some (.str s), _, _ => s
  | _, some (.arr xs), _ => String.join (xs.toList.map flatten)
  | _, _, some (.arr #[_, t]) => flatten t
  | _, _, _ => "?"

/-- The refs of tagged text, outermost first. -/
partial def refs (j : Lean.Json) : List (Nat × Lean.Json) :=
  match (j.getObjVal? "append").toOption, (j.getObjVal? "tag").toOption with
  | some (.arr xs), _ => xs.toList.flatMap refs
  | _, some (.arr #[t, x]) => ((t.getObjValAs? Nat "ref").toOption.getD 0, t) :: refs x
  | _, _ => []

def tacticSrc : String :=
  "import Prelude\ndef id' : (A : Type) → A → A := by\n  intro A\n  intro x\n  exact x\n"

def group : Group where
  name := "lsp"
  exercise := "Stage 11 (infoview)"
  cases := [
    { name := "modules in isolation are elaborated once per process", run := fun _ => do
        let pre ← prelude
        let size : IO Nat := do pure (← isoCacheZOM.get).size
        isoCacheZOM.set {}
        let msgs (s : St) := s.messages.toList.map (·.text)
        let src := "import Prelude\ndef x : Nat := 1 + 1\ndef bad : Nat := true\n"
        let s₁ := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader := fun m => if m == "Prelude" then some pre else none }
        -- (each state is looked at before the table: that fixes the order)
        check ((msgs s₁).length == 1) s!"{msgs s₁}"
        let n ← size
        check (n ≥ 1) "nothing kept"
        -- again, from a loader that is another closure: the same, from the table
        let s₂ := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader := fun m => if m == "Prelude" then some pre else none }
        checkEq (msgs s₁) (msgs s₂)
        checkEq n (← size)
        checkEq s₁.globals.order.size s₂.globals.order.size
        -- the loader is the file's own after a hit: a module the first loader didn't have
        let loader (m : Name) := if m == "Prelude" then some pre else if m == "Extra" then some "import Prelude\ndef extra : Nat := 3\n" else none
        let s₃ := runFrontend (R := ZeroOneMany) "import Prelude\nimport Extra\ndef y : Nat := extra\n" { loader, trustedModule := Tests.libModule }
        checkEq ([] : List String) (msgs s₃)
        -- another Prelude text, other settings: other entries
        let s₄ := runFrontend (R := ZeroOneMany) "import Prelude\ndef y : Nat := preExtra\n"
          { trustedModule := Tests.libModule, loader := fun m => if m == "Prelude" then some (pre ++ "\ndef preExtra : Nat := 0\n") else none }
        checkEq ([] : List String) (msgs s₄)
        let k₁ ← size
        let s₆ := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader := fun m => if m == "Prelude" then some pre else none, termInfo := true }
        checkEq (msgs s₁) (msgs s₆)
        check ((← size) > k₁) "termInfo shares an entry"
        -- a state that is not initial is not cached; an import cycle isn't either
        isoCacheZOM.set {}
        let s₅ := runFrontend (R := ZeroOneMany) "import A\n" { trustedModule := Tests.libModule, loader := fun m => if m == "A" then some "import B\n" else if m == "B" then some "import A\n" else none }
        check (s₅.messages.size ≥ 1) "no cycle error"
        let s₇ := runFrontend (R := ZeroOneMany) "import Prelude\n" { trustedModule := Tests.libModule, loader := fun m => if m == "Prelude" then some pre else none, pristine := false }
        checkEq ([] : List String) (msgs s₇)
        checkEq 0 (← size) },
    { name := "info tree: hovers are unchanged", run := fun _ => do
        let src := "import Prelude\ndef double (n : Nat) : Nat := n + n\ndef four : Nat := double 2\n"
        for ti in [false, true] do
          let s ← elabSrc src ti
          checkEq "(some (double, Nat → Nat))" (toString (Query.hoverAt s (offAfter src "double 2" (-3))))
          checkEq "(some (n, Nat))" (toString (Query.hoverAt s (offAfter src ":= n" (-1)))) },
    { name := "info tree: tactic states before, between and after tactics", run := fun _ => do
        let s ← elabSrc tacticSrc
        -- on `by`: the goal the block started with
        checkEq "⊢ (A : Type) → A → A" (goalsText s (offAfter tacticSrc ":= by" (-1)))
        checkEq "A : Type\n⊢ A → A" (goalsText s (offAfter tacticSrc "intro A"))
        checkEq "A : Type\n⊢ A → A" (goalsText s (offAfter tacticSrc "intro A" (-3)))
        -- at the start of the next line: still after `intro A`
        checkEq "A : Type\n⊢ A → A" (goalsText s (offAfter tacticSrc "intro A\n"))
        checkEq "A : Type\nx : A\n⊢ A" (goalsText s (offAfter tacticSrc "intro x"))
        checkEq "no goals" (goalsText s (offAfter tacticSrc "exact x"))
        checkEq "none" (goalsText s 3) },
    { name := "info tree: goals survive an error (unsolved goals, a failing tactic)", run := fun _ => do
        let src := "import Prelude\ndef bad : Nat → Bool := by intro n\n"
        let s ← elabSrc src
        checkEq "n : Nat\n⊢ Bool" (goalsText s (offAfter src "intro n"))
        check (s.messages.any (·.code == "unsolved-goals")) "no code on the unsolved goals error"
        let src := "import Prelude\ndef bad : Nat → Nat := by\n  intro n\n  exact true\n"
        let s ← elabSrc src
        checkEq "n : Nat\n⊢ Nat" (goalsText s (offAfter src "exact true")) },
    { name := "info tree: holes and expected types", run := fun _ => do
        let src := "import Prelude\ndef f (n : Nat) (b : Bool) : Nat := Nat.add n _\n"
        for ti in [false, true] do
          let s ← elabSrc src ti
          checkEq "n : Nat\nb : Bool\n⊢ Nat" (termGoalText s (offAfter src "n _" (-1)))
        let s ← elabSrc src
        -- an argument, and the head (an identifier: its type)
        checkEq "n : Nat\nb : Bool\n⊢ Nat" (termGoalText s (offAfter src "add n" (-1)))
        checkEq "⊢ Nat → Nat → Nat" (termGoalText s (offAfter src "Nat.add" (-2)))
        let src := "import Prelude\ndef g : Nat := let k : Nat := 1; ?hole\n"
        let s ← elabSrc src
        checkEq "k : Nat := 1\n⊢ Nat" (termGoalText s (offAfter src "?hole" (-1))) },
    { name := "info tree: matches, unknown identifiers and declarations", run := fun _ => do
        let src := "import Prelude\ninductive T where\n  | a\n  | b (t : T)\n  | c (x y : Nat)\ndef f (t : T) : Nat := match t with\n  | .a => 0\ndef g : T → Nat\n  | .b _ => 1\ndef h := Nat.add 1 2\ndef k : Nat := lenght\n"
        let s ← elabSrc src
        let ms := s.infos.filterMap fun i => match i with
          | .matchCases _ m => some s!"{m.type} {m.covered} {m.catchAll} {m.columns}"
          | _ => none
        checkEq "#[T [a] false 1, T [b] false 1]" (toString ms)
        checkEq 2 (s.messages.filter (·.code == "missing-case")).size
        check (s.messages.any (·.code == "unknown-identifier")) "unknown-identifier code"
        check (s.infos.any fun i => i matches .unknownIdent _ "lenght" _) "no unknown identifier info"
        let ds := s.infos.filterMap fun i => match i with
          | .decl _ n names ty ann _ => some s!"{n} {ty.pretty names} {ann}"
          | _ => none
        check (ds.contains "h Nat false") s!"decl infos: {ds}" },
    { name := "info tree: through the shared cache", run := fun _ => do
        let p ← prelude
        let init : St := { trustedModule := Tests.libModule, loader := fun m => if m == "Prelude" then some p else none, termInfo := true }
        let src := tacticSrc ++ "def f (n : Nat) : Nat := Nat.add n _\ndef h := Nat.add 1 2\n"
        let dir ← IO.FS.createTempDir
        let (cold, _) ← Cache.elaborateCached dir src init 0
        let (warm, hits) ← Cache.elaborateCached dir src init 0
        check (hits > 0) "nothing came from the cache"
        checkEq cold.infos.size warm.infos.size
        for off in [offAfter src "intro A", offAfter src "intro x", offAfter src "n _" (-1), offAfter src "Nat.add 1"] do
          checkEq (goalsText cold off) (goalsText warm off)
          checkEq (termGoalText cold off) (termGoalText warm off) },
    { name := "tagged printing agrees with the printer", run := fun _ => do
        let p ← prelude
        let st := runFrontend (R := ZeroOneMany) "import Prelude" { trustedModule := Tests.libModule, loader := fun _ => some p }
        for n in st.globals.order do
          let some d := st.globals.find? n | continue
          for t in [d.type] ++ d.value.toList do
            let (tt, subs) := (t.prettyTagged [] []).run #[]
            unless tt.flatten == t.pretty do
              throw (IO.userError s!"{n}: {tt.flatten} ≠ {t.pretty}")
            check (subs.size > 0) s!"{n}: no tags" },
    { name := "tagged printing with notation agrees with the printer, and tags the parts (11r)", run := fun _ => do
        let p ← prelude
        let st := runFrontend (R := ZeroOneMany) "import Prelude\ndef t (n : Nat) : List Nat := [n + 2, 3]"
          { trustedModule := Tests.libModule, loader := fun _ => some p }
        let g := st.globals
        for n in g.order do
          let some d := g.find? n | continue
          for t in [d.type] ++ d.value.toList do
            let (tt, _) := (t.prettyTagged [] [] (some g)).run #[]
            unless tt.flatten == t.pretty [] (some g) do
              throw (IO.userError s!"{n}: {tt.flatten} ≠ {t.pretty [] (some g)}")
        let some d := g.find? "t" | throw (IO.userError "no t")
        let some v := d.value | throw (IO.userError "no value")
        let (tt, subs) := (v.prettyTagged [] [] (some g)).run #[]
        checkEq "fun n => [n + 2, 3]" tt.flatten
        -- the variable, the numerals, the sum and the list are subterms of their own
        let shown := subs.toList.map fun sub => sub.term.pretty sub.names (some g)
        for x in ["n", "2", "3", "n + 2", "[n + 2, 3]"] do
          check (shown.contains x) s!"no tag for {x}: {shown}" }
  ]

/-- Apply a `WorkspaceEdit` (for `file:///t.wiz`) to `src`. -/
def applyEdit (src : String) (edit : Lean.Json) : String :=
  let edits := match LSP.get? edit ["changes", "file:///t.wiz"] with
    | some (.arr es) => es
    | _ => #[]
  let at_ (e : Lean.Json) (k : String) : Nat :=
    LSP.ofPos src (LSP.getNat e ["range", k, "line"]) (LSP.getNat e ["range", k, "character"])
  Actions.apply src (edits.map fun e => { start := at_ e "start", stop := at_ e "end", text := LSP.getStr e ["newText"] })

/-- The code actions at an offset of the open document. -/
def codeActions (srv : LSP.Server) (src : String) (off : Nat) : LSP.Server × Array Lean.Json :=
  let p := posJson src off
  let (srv, out) := LSP.handle srv (req s!"\{\"jsonrpc\":\"2.0\",\"id\":5,\"method\":\"textDocument/codeAction\",\"params\":\{\"textDocument\":\{\"uri\":\"file:///t.wiz\"},\"range\":\{\"start\":{p},\"end\":{p}},\"context\":\{\"diagnostics\":[]}}}")
  match (out[0]!.getObjVal? "result").toOption with
  | some (.arr as) => (srv, as)
  | _ => (srv, #[])

def titled (as : Array Lean.Json) (t : String) : Option Lean.Json :=
  as.find? fun a => LSP.getStr a ["title"] == t

/-- The diagnostics' codes after opening `src`. -/
def codes (src : String) : IO (List String) := do
  let (_, out) ← openDoc src
  match LSP.get? out[0]! ["params", "diagnostics"] with
  | some (.arr ds) => pure (ds.toList.map fun d => LSP.getStr d ["code"])
  | _ => pure []

def subtermInfo (srv : LSP.Server) (session ref : Nat) : LSP.Server × Lean.Json :=
  let (srv, out) := LSP.handle srv (req s!"\{\"jsonrpc\":\"2.0\",\"id\":11,\"method\":\"wiz/subtermInfo\",\"params\":\{\"textDocument\":\{\"uri\":\"file:///t.wiz\"},\"session\":{session},\"ref\":{ref}}}")
  (srv, (out[0]!.getObjVal? "result").toOption.getD ((out[0]!.getObjVal? "error").toOption.getD Lean.Json.null))

/-- The body of the infoview socket case. -/
def socketCase : IO Unit := do
        let dir ← IO.FS.createTempDir
        let sock := (dir / "iv.sock").toString
        -- the editor's end of an in-process pipe, and the server on the other end
        let ((srvIn, srvOut), (edIn, edOut)) ← Socket.pair
        let (ed, edW) := (IO.FS.Stream.ofHandle edIn, IO.FS.Stream.ofHandle edOut)
        let done ← IO.asTask (prio := .dedicated)
          (LSP.serveInfoview (← server).libs (IO.FS.Stream.ofHandle srvIn) (IO.FS.Stream.ofHandle srvOut) sock ["Prelude"])
        let next (h : IO.FS.Stream) : IO Lean.Json := do
          let some j ← LSP.readMessage h | throw (IO.userError "the stream ended")
          pure j
        let src := "import Prelude\ndef k : Nat → Bool → Nat := by\n  intro n\n  intro b\n  exact n\n"
        LSP.writeMessage edW (req "{\"jsonrpc\":\"2.0\",\"id\":0,\"method\":\"initialize\",\"params\":{}}")
        check (has (← next ed) "documentHighlightProvider") "documentHighlight not asked for"
        LSP.writeMessage edW (Lean.Json.mkObj [("jsonrpc", "2.0"), ("method", "textDocument/didOpen"),
          ("params", Lean.Json.mkObj [("textDocument", Lean.Json.mkObj [("uri", "file:///t.wiz"), ("version", (1 : Nat)), ("text", src)])])])
        check (has (← next ed) "publishDiagnostics") "no diagnostics"
        -- an infoview connects (retrying, like the clients) and is told where the cursor is
        let rec conn : Nat → IO (IO.FS.Handle × IO.FS.Handle)
          | 0 => Socket.connect sock
          | n + 1 => do try Socket.connect sock catch _ => do IO.sleep 50; conn n
        let (ivIn, ivOut) ← conn 100
        let (iv, ivW) := (IO.FS.Stream.ofHandle ivIn, IO.FS.Stream.ofHandle ivOut)
        let c ← next iv
        checkEq "wiz/infoview/cursor" (LSP.getStr c ["method"])
        checkEq "{\"character\":0,\"line\":0}" (LSP.get? c ["params", "position"]).get!.compress
        let session := LSP.getNat c ["params", "session"]
        -- the editor's cursor moves: a documentHighlight (answered null), then a hover at the same place
        let pos := posJson src (offAfter src "intro n")
        LSP.writeMessage edW (req s!"\{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"textDocument/documentHighlight\",\"params\":\{\"textDocument\":\{\"uri\":\"file:///t.wiz\"},\"position\":{pos}}}")
        checkEq "null" ((← next ed).getObjVal? "result" |>.toOption.get!).compress
        LSP.writeMessage edW (req s!"\{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"textDocument/hover\",\"params\":\{\"textDocument\":\{\"uri\":\"file:///t.wiz\"},\"position\":{pos}}}")
        let _ ← next ed
        let c ← next iv
        checkEq (req pos).compress (LSP.get? c ["params", "position"]).get!.compress
        checkEq session (LSP.getNat c ["params", "session"])
        -- the infoview pulls the goals there, on the socket, and asks about a subterm
        LSP.writeMessage ivW (req s!"\{\"jsonrpc\":\"2.0\",\"id\":7,\"method\":\"wiz/interactiveGoals\",\"params\":\{\"textDocument\":\{\"uri\":\"file:///t.wiz\"},\"position\":{pos}}}")
        let r ← next iv
        checkEq "7" (LSP.get? r ["id"]).get!.compress
        let some (.arr #[g]) := LSP.get? r ["result", "goals"] | throw (IO.userError s!"goals: {r.compress}")
        let ty := (LSP.get? g ["type"]).get!
        checkEq "Bool → Nat" (flatten ty)
        let some (ref, _) := (refs ty).find? fun (_, t) => LSP.getStr t ["name"] == "Bool" | throw (IO.userError "no Bool")
        LSP.writeMessage ivW (Lean.Json.mkObj [("jsonrpc", "2.0"), ("id", (8 : Nat)), ("method", "wiz/subtermInfo"),
          ("params", Lean.Json.mkObj [("textDocument", Lean.Json.mkObj [("uri", "file:///t.wiz")]), ("session", session), ("ref", ref)])])
        checkEq "Bool" (LSP.getStr (← next iv) ["result", "text"])
        -- other methods are refused on the socket
        LSP.writeMessage ivW (req "{\"jsonrpc\":\"2.0\",\"id\":9,\"method\":\"textDocument/hover\",\"params\":{}}")
        check (has (← next iv) "-32601") "hover answered on the socket"
        -- an edit: the infoview hears of the new session at the same cursor
        LSP.writeMessage edW (Lean.Json.mkObj [("jsonrpc", "2.0"), ("method", "textDocument/didChange"),
          ("params", Lean.Json.mkObj [("textDocument", Lean.Json.mkObj [("uri", "file:///t.wiz"), ("version", (2 : Nat))]),
                                      ("contentChanges", Lean.Json.arr #[Lean.Json.mkObj [("text", src ++ "\n")]])])])
        let _ ← next ed
        let c ← next iv
        checkEq (req pos).compress (LSP.get? c ["params", "position"]).get!.compress
        check (LSP.getNat c ["params", "session"] != session) "same session after an edit"
        -- `exit`: the server stops and removes the socket
        LSP.writeMessage edW (req "{\"jsonrpc\":\"2.0\",\"method\":\"exit\"}")
        match ← IO.wait done with
        | .ok () => pure ()
        | .error e => throw e
        check (!(← System.FilePath.pathExists sock)) "the socket file is still there"
        check ((← LSP.readMessage iv).isNone) "the infoview's connection is still open"


/-- The body of the WebSocket case: an editor on stdio (a socket pair), and two
WebSocket clients, one of which edits a document of its own. -/
def wsCase : IO Unit := do
        let ((srvIn, srvOut), (edIn, edOut)) ← Socket.pair
        let (ed, edW) := (IO.FS.Stream.ofHandle edIn, IO.FS.Stream.ofHandle edOut)
        let port ← IO.Promise.new
        let done ← IO.asTask (prio := .dedicated)
          (LSP.serveWith (← server).libs (some (IO.FS.Stream.ofHandle srvIn, IO.FS.Stream.ofHandle srvOut))
            { ws := some (Socket.loopback, 0) } (fun p => port.resolve p) ["Prelude"])
        let port := port.result!.get
        let next (h : IO.FS.Stream) : IO Lean.Json := do
          let some j ← LSP.readMessage h | throw (IO.userError "the stream ended")
          pure j
        let tcp : IO (IO.FS.Stream × IO.FS.Stream) := do
          let (r, w) ← Socket.tcpConnect Socket.loopback port
          pure (IO.FS.Stream.ofHandle r, IO.FS.Stream.ofHandle w)
        let mask := some (ByteArray.mk #[0x37, 0xfa, 0x21, 0x3d])
        let send (w : IO.FS.Stream) (j : Lean.Json) := WebSocket.sendText w j.compress mask
        let recv (r w : IO.FS.Stream) : IO Lean.Json := do
          let some t ← WebSocket.recvText r w (server := false) | throw (IO.userError "the WebSocket closed")
          match Lean.Json.parse t with
          | .ok j => pure j
          | .error e => throw (IO.userError s!"not JSON ({e}): {t}")
        -- a page from another site is refused; so is a plain HTTP request
        let (r, w) ← tcp
        match ← WebSocket.connect r w s!"127.0.0.1:{port}" (origin := some "https://example.com") with
        | .ok () => throw (IO.userError "a foreign origin was let in")
        | .error e => check ((e.splitOn "403").length > 1) s!"refused how: {e}"
        let (r, w) ← tcp
        w.putStr "GET / HTTP/1.1\r\nHost: x\r\n\r\n"; w.flush
        check (((← r.getLine).splitOn "426").length > 1) "a plain GET was not refused"
        -- the editor opens a document
        let src := "import Prelude\ndef k : Nat → Bool → Nat := by\n  intro n\n  intro b\n  exact n\n"
        LSP.writeMessage edW (req "{\"jsonrpc\":\"2.0\",\"id\":0,\"method\":\"initialize\",\"params\":{}}")
        let _ ← next ed
        LSP.writeMessage edW (Lean.Json.mkObj [("jsonrpc", "2.0"), ("method", "textDocument/didOpen"),
          ("params", Lean.Json.mkObj [("textDocument", Lean.Json.mkObj [("uri", "file:///t.wiz"), ("version", (1 : Nat)), ("text", src)])])])
        let _ ← next ed
        -- a local page connects and is told where the cursor is
        let (iv, ivW) ← tcp
        match ← WebSocket.connect iv ivW s!"127.0.0.1:{port}" (origin := some s!"http://127.0.0.1:{port + 1}") with
        | .ok () => pure ()
        | .error e => throw (IO.userError s!"handshake: {e}")
        let c ← recv iv ivW
        checkEq "wiz/infoview/cursor" (LSP.getStr c ["method"])
        -- the editor's cursor moves; the page hears of it and pulls the goals
        let pos := posJson src (offAfter src "intro n")
        LSP.writeMessage edW (req s!"\{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"textDocument/hover\",\"params\":\{\"textDocument\":\{\"uri\":\"file:///t.wiz\"},\"position\":{pos}}}")
        let _ ← next ed
        let c ← recv iv ivW
        checkEq (req pos).compress (LSP.get? c ["params", "position"]).get!.compress
        let session := LSP.getNat c ["params", "session"]
        send ivW (req s!"\{\"jsonrpc\":\"2.0\",\"id\":7,\"method\":\"wiz/interactiveGoals\",\"params\":\{\"textDocument\":\{\"uri\":\"file:///t.wiz\"},\"position\":{pos}}}")
        let r ← recv iv ivW
        checkEq "7" (LSP.get? r ["id"]).get!.compress
        let some (.arr #[g]) := LSP.get? r ["result", "goals"] | throw (IO.userError s!"goals: {r.compress}")
        checkEq "Bool → Nat" (flatten (LSP.get? g ["type"]).get!)
        checkEq session (LSP.getNat r ["result", "session"])
        -- a ping is answered (by the client's `recv`, which skips the pong); then a request
        -- split into two fragments, the second after a ping
        WebSocket.writeFrame ivW WebSocket.opPing "hi".toUTF8 mask
        let msg := (req "{\"jsonrpc\":\"2.0\",\"id\":8,\"method\":\"shutdown\"}").compress.toUTF8
        let half := msg.size / 2
        let frag (fin : Bool) (op : UInt8) (bs : ByteArray) : ByteArray :=
          let f := WebSocket.frameBytes op bs mask
          f.set! 0 (if fin then f.get! 0 else f.get! 0 &&& 0x7f)
        ivW.write (frag false WebSocket.opText (msg.extract 0 half)); ivW.flush
        WebSocket.writeFrame ivW WebSocket.opPing .empty mask
        ivW.write (frag true 0 (msg.extract half msg.size)); ivW.flush
        checkEq "8" (LSP.get? (← recv iv ivW) ["id"]).get!.compress
        -- the page opens a document of its own (a long one: a 16-bit frame length) and gets
        -- its diagnostics, and hovers in it: the cursor moves there, for every infoview
        let mine := "import Prelude\n" ++ String.join ((List.range 40).map fun i => s!"def d{i} : Nat := {i}\n") ++ "def bad : Nat := true\n"
        send ivW (Lean.Json.mkObj [("jsonrpc", "2.0"), ("method", "textDocument/didOpen"),
          ("params", Lean.Json.mkObj [("textDocument", Lean.Json.mkObj [("uri", "file:///w.wiz"), ("version", (1 : Nat)), ("text", mine)])])])
        let d ← recv iv ivW
        checkEq "textDocument/publishDiagnostics" (LSP.getStr d ["method"])
        let some (.arr #[_]) := LSP.get? d ["params", "diagnostics"] | throw (IO.userError s!"diagnostics: {d.compress}")
        let mpos := posJson mine (offAfter mine "def d3 : Na" (-1))
        send ivW (req s!"\{\"jsonrpc\":\"2.0\",\"id\":9,\"method\":\"textDocument/hover\",\"params\":\{\"textDocument\":\{\"uri\":\"file:///w.wiz\"},\"position\":{mpos}}}")
        check (has (← recv iv ivW) "Nat") "no hover"
        let c ← recv iv ivW
        checkEq "file:///w.wiz" (LSP.getStr c ["params", "textDocument", "uri"])
        -- the page's `initialize` sets its own settings only: it asks for `wiz/elaborated`,
        -- and gets it for its edits; the editor (which didn't ask) doesn't for its own
        send ivW (req "{\"jsonrpc\":\"2.0\",\"id\":10,\"method\":\"initialize\",\"params\":{\"capabilities\":{\"experimental\":{\"wizElaborated\":true}}}}")
        check (has (← recv iv ivW) "wizInfoview") "no capabilities"
        send ivW (Lean.Json.mkObj [("jsonrpc", "2.0"), ("method", "textDocument/didChange"),
          ("params", Lean.Json.mkObj [("textDocument", Lean.Json.mkObj [("uri", "file:///w.wiz"), ("version", (2 : Nat))]),
                                      ("contentChanges", Lean.Json.arr #[Lean.Json.mkObj [("text", mine ++ "\n")]])])])
        checkEq "textDocument/publishDiagnostics" (LSP.getStr (← recv iv ivW) ["method"])
        checkEq "wiz/elaborated" (LSP.getStr (← recv iv ivW) ["method"])
        let _ ← recv iv ivW  -- (the cursor's document was elaborated again: its note)
        LSP.writeMessage edW (Lean.Json.mkObj [("jsonrpc", "2.0"), ("method", "textDocument/didChange"),
          ("params", Lean.Json.mkObj [("textDocument", Lean.Json.mkObj [("uri", "file:///t.wiz"), ("version", (2 : Nat))]),
                                      ("contentChanges", Lean.Json.arr #[Lean.Json.mkObj [("text", src ++ "\n")]])])])
        checkEq "textDocument/publishDiagnostics" (LSP.getStr (← next ed) ["method"])
        LSP.writeMessage edW (req "{\"jsonrpc\":\"2.0\",\"id\":3,\"method\":\"shutdown\"}")
        checkEq "3" (LSP.get? (← next ed) ["id"]).get!.compress
        -- a second page connects and hears of the cursor too
        let (iv2, iv2W) ← tcp
        match ← WebSocket.connect iv2 iv2W s!"localhost:{port}" with
        | .ok () => pure ()
        | .error e => throw (IO.userError s!"handshake: {e}")
        checkEq "file:///w.wiz" (LSP.getStr (← recv iv2 iv2W) ["params", "textDocument", "uri"])
        -- a page's `exit` closes its own connection; the editor's stops the server
        send iv2W (req "{\"jsonrpc\":\"2.0\",\"method\":\"exit\"}")
        check ((← WebSocket.recvText iv2 iv2W (server := false)).isNone) "still open after exit"
        LSP.writeMessage edW (req "{\"jsonrpc\":\"2.0\",\"method\":\"exit\"}")
        match ← IO.wait done with
        | .ok () => pure ()
        | .error e => throw e
        check ((← WebSocket.recvText iv ivW (server := false)).isNone) "the page's connection is still open"
        check ((← (try some <$> Socket.tcpConnect Socket.loopback port catch _ => pure none)).isNone) "still listening"

def serverGroup : Group where
  name := "lsp-server"
  exercise := "Stage 11 (infoview, code actions)"
  cases := [
    { name := "infoview methods are advertised", run := fun _ => do
        let (_, out) := LSP.handle (← server) (req "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\",\"params\":{}}")
        for m in ["wiz/plainGoal", "wiz/interactiveGoals", "wiz/subtermInfo", "codeActionProvider", "experimental"] do
          check (has out[0]! m) s!"no {m}" },
    { name := "wiz/plainGoal and wiz/plainTermGoal", run := fun _ => do
        let src := tacticSrc ++ "def f (n : Nat) : Nat := Nat.add n _\n"
        let (srv, _) ← openDoc src
        let (srv, r) := ask srv "wiz/plainGoal" src (offAfter src "intro x")
        checkEq "[\"A : Type\\nx : A\\n⊢ A\"]" (LSP.get? r ["goals"] |>.get!).compress
        checkEq "```wiz\nA : Type\nx : A\n⊢ A\n```" (LSP.getStr r ["rendered"])
        let (srv, r) := ask srv "wiz/plainGoal" src (offAfter src "exact x")
        checkEq "no goals" (LSP.getStr r ["rendered"])
        let (srv, r) := ask srv "wiz/plainGoal" src 2
        checkEq Lean.Json.null r
        let (_, r) := ask srv "wiz/plainTermGoal" src (offAfter src "n _" (-1))
        checkEq "n : Nat\n⊢ Nat" (LSP.getStr r ["goal"])
        check (has r "\"range\"") "no range" },
    { name := "wiz/interactiveGoals: tagged text, refs and wiz/subtermInfo", run := fun _ => do
        let src := "import Prelude\ndef k : Nat → Bool → Nat := by\n  intro n\n  intro b\n  exact n\n"
        let (srv, _) ← openDoc src
        let (srv, r) := ask srv "wiz/interactiveGoals" src (offAfter src "intro n")
        let session := LSP.getNat r ["session"]
        let some (.arr #[g]) := LSP.get? r ["goals"] | throw (IO.userError s!"goals: {r.compress}")
        let some ty := LSP.get? g ["type"] | throw (IO.userError "no type")
        checkEq "Bool → Nat" (flatten ty)
        let some (.arr #[h]) := LSP.get? g ["hyps"] | throw (IO.userError "hyps")
        checkEq "[\"n\"]" (LSP.get? h ["names"]).get!.compress
        checkEq "Nat" (flatten (LSP.get? h ["type"]).get!)
        -- the same request again gives the same refs
        let (srv, r') := ask srv "wiz/interactiveGoals" src (offAfter src "intro n")
        checkEq r.compress r'.compress
        -- `Bool`: a constant from the prelude
        let some (ref, tag) := (refs ty).find? fun (_, t) => LSP.getStr t ["name"] == "Bool"
          | throw (IO.userError s!"no Bool tag in {ty.compress}")
        checkEq "const" (LSP.getStr tag ["kind"])
        let (srv, info) := subtermInfo srv session ref
        checkEq "Bool" (LSP.getStr info ["text"])
        checkEq "Type" (flatten (LSP.get? info ["type"]).get!)
        check ((LSP.getStr info ["definition", "uri"]).endsWith "lib/Prelude.wiz") s!"definition: {info.compress}"
        -- the whole arrow
        let (pref, _) := (refs ty).head!
        let (srv, info) := subtermInfo srv session pref
        checkEq "pi" (LSP.getStr info ["kind"])
        checkEq "Type" (flatten (LSP.get? info ["type"]).get!)
        -- after a change the refs are stale
        let (srv, _) := LSP.handle srv (req "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didChange\",\"params\":{\"textDocument\":{\"uri\":\"file:///t.wiz\",\"version\":2},\"contentChanges\":[{\"text\":\"import Prelude\\n\"}]}}")
        let (srv, err) := subtermInfo srv session ref
        checkEq (-32801 : Int) ((err.getObjValAs? Int "code").toOption.getD 0)
        let (_, out) := LSP.handle srv (req "{\"jsonrpc\":\"2.0\",\"id\":3,\"method\":\"wiz/plainGoal\",\"params\":{\"textDocument\":{\"uri\":\"file:///nope.wiz\"},\"position\":{\"line\":0,\"character\":0}}}")
        check (has out[0]! "-32602") s!"unknown document: {out[0]!.compress}" },
    { name := "wiz/interactiveTermGoal and the wiz/elaborated notification", run := fun _ => do
        let src := "import Prelude\ndef f (n : Nat) : Nat := Nat.add n ?x\n"
        let init := req "{\"jsonrpc\":\"2.0\",\"id\":0,\"method\":\"initialize\",\"params\":{\"capabilities\":{\"experimental\":{\"wizElaborated\":true}}}}"
        let (srv, out) ← openDoc src init
        check (out.any (has · "wiz/elaborated")) "no wiz/elaborated"
        let (_, r) := ask srv "wiz/interactiveTermGoal" src (offAfter src "?x" (-1))
        checkEq "Nat" (flatten (LSP.get? r ["goal", "type"]).get!)
        checkEq "\"x\"" (LSP.get? r ["goal", "userName"]).get!.compress
        let (_, out) ← openDoc src
        check (!(out.any (has · "wiz/elaborated"))) "unasked wiz/elaborated" },
    { name := "code action: did you mean", run := fun _ => do
        let src := "import Prelude\ndef double (n : Nat) : Nat := n + n\ndef four : Nat := doubel 2\n"
        let (srv, out) ← openDoc src
        check (has out[0]! "\"code\":\"unknown-identifier\"") s!"diagnostic: {out[0]!.compress}"
        check (has out[0]! "\"suggestions\":[\"double\"]") s!"data: {out[0]!.compress}"
        let (_, as) := codeActions srv src (offAfter src "doubel" (-2))
        let some a := titled as "Did you mean 'double'?" | throw (IO.userError s!"actions: {as.map (·.compress)}")
        let src' := applyEdit src (LSP.get? a ["edit"]).get!
        checkEq ([] : List String) (← codes src') },
    { name := "code action: add missing cases (match and equations)", run := fun _ => do
        let ty := "import Prelude\ninductive T where\n  | a\n  | b (t : T)\n  | c (x y : Nat)\n"
        for body in ["def f (t : T) : Nat := match t with\n  | .a => 0\n", "def g : T → Nat\n  | .b _ => 1\n"] do
          let src := ty ++ body
          check ((← codes src).contains "missing-case") "no missing-case code"
          let (srv, out) ← openDoc src
          let some (.arr ds) := LSP.get? out[0]! ["params", "diagnostics"] | throw (IO.userError "no diagnostics")
          let some d := ds.find? (LSP.getStr · ["code"] == "missing-case") | throw (IO.userError "no missing-case")
          let off := LSP.ofPos src (LSP.getNat d ["range", "start", "line"]) (LSP.getNat d ["range", "start", "character"])
          let (_, as) := codeActions srv src off
          let some a := titled as "Add missing cases" | throw (IO.userError s!"actions: {as.map (·.compress)}")
          let src' := applyEdit src (LSP.get? a ["edit"]).get!
          check (!((← codes src').contains "missing-case")) s!"still missing cases:\n{src'}"
          check ((src'.splitOn "\n  | .c x y => ?c").length > 1) s!"edited:\n{src'}" },
    { name := "code action: add type ascription (and codeAction/resolve)", run := fun _ => do
        let src := "import Prelude\ndef h := Nat.add 1 2\n"
        let init := req "{\"jsonrpc\":\"2.0\",\"id\":0,\"method\":\"initialize\",\"params\":{\"capabilities\":{\"textDocument\":{\"codeAction\":{\"resolveSupport\":{\"properties\":[\"edit\"]}}}}}}"
        let (srv, _) ← openDoc src init
        let (srv, as) := codeActions srv src (offAfter src "def h" (-1))
        let some a := titled as "Add type ascription" | throw (IO.userError s!"actions: {as.map (·.compress)}")
        check (LSP.get? a ["edit"]).isNone "edit not deferred"
        let resolve (srv : LSP.Server) : LSP.Server × Lean.Json :=
          let (srv, out) := LSP.handle srv (Lean.Json.mkObj [("jsonrpc", "2.0"), ("id", (6 : Nat)), ("method", "codeAction/resolve"), ("params", a)])
          (srv, out[0]!)
        let (srv, r) := resolve srv
        let src' := applyEdit src (LSP.get? r ["result", "edit"]).get!
        checkEq "import Prelude\ndef h : Nat := Nat.add 1 2\n" src'
        checkEq ([] : List String) (← codes src')
        let (srv, _) := LSP.handle srv (req "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didChange\",\"params\":{\"textDocument\":{\"uri\":\"file:///t.wiz\",\"version\":2},\"contentChanges\":[{\"text\":\"import Prelude\\n\"}]}}")
        let (_, r) := resolve srv
        check (has r "-32801") s!"stale resolve: {r.compress}" },
    { name := "11q: go to definition and declaration of syntax, a macro use's hover", run := fun _ => do
        let src := "import Prelude\nsyntax (name := twice) \"twice\" term:max : term\nmacro_rules\n  | `(term| twice $x) => `(term| Nat.add $x $x)\ndef two : Nat := 2\ndef four : Nat := twice two\n"
        let (srv, _) ← openDoc src
        let line (r : Lean.Json) : Nat := LSP.getNat r ["range", "start", "line"]
        let use := offAfter src "twice two" (-7)
        -- definition: the macro rule that expanded it; declaration: the `syntax`
        let (srv, r) := ask srv "textDocument/definition" src use
        checkEq "file:///t.wiz" (LSP.getStr r ["uri"])
        checkEq 3 (line r)
        let (srv, r) := ask srv "textDocument/declaration" src use
        checkEq 1 (line r)
        -- the argument is still an identifier of its own
        let (srv, r) := ask srv "textDocument/definition" src (offAfter src "twice two" (-1))
        checkEq 4 (line r)
        -- the hover: the syntax, its type, where it is declared and what it expands to
        let (srv, r) := ask srv "textDocument/hover" src use
        let md := LSP.getStr r ["contents", "value"]
        for part in ["twice two : Nat", "syntax `term.twice` (this file, line 2)", "by macro rule (this file, line 4)",
                     "expands to\n```wiz\nNat.add two two\n```"] do
          check ((md.splitOn part).length > 1) s!"no {part} in the hover:\n{md}"
        -- the pattern of the rule refers to the syntax too; the template records nothing
        -- (its ranges are the rule's, not the use's)
        let (srv, r) := ask srv "textDocument/declaration" src (offAfter src "term| twice" (-2))
        checkEq 1 (line r)
        let (_, r) := ask srv "textDocument/hover" src (offAfter src "Nat.add $x" (-5))
        checkEq Lean.Json.null r },
    { name := "11q: Prelude notation, syntax categories and imports", run := fun _ => do
        let src := "import Prelude\ndeclare_syntax_cat greeting\nsyntax \"hi\" : greeting\nsyntax \"greet\" greeting : term\ndef three : Nat := 1 + 2\n"
        let (srv, _) ← openDoc src
        let pre ← prelude
        let preLine (needle : String) : Nat := ((pre.splitOn needle).headD "").toList.count '\n'
        -- `+`: the `infixl` in the Prelude (the rule and the syntax are one command)
        for m in ["textDocument/definition", "textDocument/declaration"] do
          let (_, r) := ask srv m src (offAfter src "1 +" (-1))
          check ((LSP.getStr r ["uri"]).endsWith "lib/Prelude.wiz") s!"{m}: {r.compress}"
          checkEq (preLine "infixl:65 \" + \"") (LSP.getNat r ["range", "start", "line"])
        let (srv, r) := ask srv "textDocument/hover" src (offAfter src "1 +" (-1))
        let md := LSP.getStr r ["contents", "value"]
        check ((md.splitOn "Add Nat").length > 1) s!"no instance in the hover:\n{md}"
        check ((md.splitOn "expands to\n```wiz\nAdd.add 1 2").length > 1) s!"no expansion in the hover:\n{md}"
        -- a category's name, where a rule uses it and in the rule's target
        for needle in ["\"greet\" greeting", ": greeting"] do
          let (_, r) := ask srv "textDocument/definition" src (offAfter src needle (-2))
          checkEq 1 (LSP.getNat r ["range", "start", "line"])
        -- the module of an import
        let (srv, r) := ask srv "textDocument/definition" src (offAfter src "import Pre" (-1))
        check ((LSP.getStr r ["uri"]).endsWith "lib/Prelude.wiz") s!"import: {r.compress}"
        let (_, r) := ask srv "textDocument/hover" src (offAfter src "import Pre" (-1))
        check (has r "module `Prelude`") s!"import hover: {r.compress}" },
    { name := "11q: binders, pattern variables, declarations, messages and instances in the infoview", run := fun _ => do
        let src := "import Prelude\ndef pred (n : Nat) : Nat := match n with\n  | .zero => 0\n  | .succ m => m\nstructure P where\n  x : Nat\n  y : Bool\n#check pred 3\ndef six : Nat := 2 * 3\n"
        let (srv, _) ← openDoc src
        -- a binder: its type (hover), its context (the expected type request)
        let (srv, r) := ask srv "textDocument/hover" src (offAfter src "(n" (-1))
        check (has r "n : Nat") s!"binder hover: {r.compress}"
        let (srv, r) := ask srv "wiz/plainTermGoal" src (offAfter src "(n" (-1))
        checkEq "⊢ Nat" (LSP.getStr r ["goal"])
        -- a pattern variable: the arm's context
        let (srv, r) := ask srv "wiz/plainTermGoal" src (offAfter src ".succ m" (-1))
        -- (`m` is the constructor's field, as a definition: `m : Nat := n✝`)
        let g := LSP.getStr r ["goal"]
        check ((g.splitOn "\nm : Nat").length > 1 && g.endsWith "⊢ Nat") s!"pattern variable: {r.compress}"
        let item (r : Lean.Json) (kind : String) : List Lean.Json := match LSP.get? r ["items"] with
          | some (.arr is) => is.toList.filter (LSP.getStr · ["kind"] == kind)
          | _ => []
        -- a command: what it declares (a structure: its constructor and fields)
        let (srv, r) := ask srv "wiz/interactiveInfo" src (offAfter src "structure P" (-1))
        let ds := (item r "declaration").map fun d => s!"{LSP.getStr d ["title"]} : {flatten (LSP.get? d ["type"]).get!}"
        for d in ["P : Type", "P.x : P → Nat", "P.y : P → Bool"] do
          check (ds.contains d) s!"no {d} in {ds}"
        check (ds.any (·.startsWith "P.mk : ")) s!"no constructor in {ds}"
        let (srv, r) := ask srv "wiz/interactiveInfo" src (offAfter src "def pred" (-1))
        checkEq ["pred : Nat → Nat"] ((item r "declaration").map fun d => s!"{LSP.getStr d ["title"]} : {flatten (LSP.get? d ["type"]).get!}")
        -- `#check`: its message
        let (srv, r) := ask srv "wiz/interactiveInfo" src (offAfter src "#check" (-2))
        checkEq ["pred 3 : Nat"] ((item r "message").map (LSP.getStr · ["text"]))
        -- an instance argument, at the notation that needed it; and the syntax
        let (_, r) := ask srv "wiz/interactiveInfo" src (offAfter src "2 *" (-1))
        checkEq ["Mul Nat"] ((item r "instance").map fun i => flatten (LSP.get? i ["type"]).get!)
        check ((item r "syntax").length == 1 && (item r "expansion").length == 1) s!"syntax items: {r.compress}" },
    { name := "inlay hints: the types of fun and let binders written without one", run := fun _ => do
        let src := "import Prelude\ndef f : Nat → Nat := fun x => Nat.succ x\ndef g : Nat := let n := 2\n  Nat.add n n\n" ++
          "def h : Nat → Bool → Nat := fun a b => a\ndef k : Nat → Nat := fun (y : Nat) => y\n"
        let (srv, _) ← openDoc src
        let (_, out) := LSP.handle srv (req s!"\{\"jsonrpc\":\"2.0\",\"id\":7,\"method\":\"textDocument/inlayHint\",\"params\":\{\"textDocument\":\{\"uri\":\"file:///t.wiz\"},\"range\":\{\"start\":{posJson src 0},\"end\":{posJson src src.length}}}}")
        let some (.arr hs) := LSP.get? out[0]! ["result"] | throw (IO.userError s!"{out[0]!.compress}")
        let got := hs.toList.map fun h => (LSP.ofPos src (LSP.getNat h ["position", "line"]) (LSP.getNat h ["position", "character"]), LSP.getStr h ["label"])
        checkEq [(offAfter src "fun x", " : Nat"), (offAfter src "let n", " : Nat"), (offAfter src "fun a", " : Nat"),
                 (offAfter src "fun a b", " : Bool")] got },
    { name := "infoview socket: cursor notifications, requests answered on the socket", run := fun _ => do
        -- a watchdog: a broken server must fail the case, not hang the suite (and since
        -- the process would wait for it, the case ends with an explicit exit)
        let _ ← IO.asTask (prio := .dedicated) (do IO.sleep 60000; IO.eprintln "timed out"; IO.Process.exit 3 : IO Unit)
        try socketCase; IO.Process.exit 0
        catch e => IO.eprintln e; IO.Process.exit 1 },
    { name := "WebSocket: handshake (RFC 6455's example), frames", run := fun _ => do
        checkEq "s3pPLMBiTxaQ9kYGzzhZRbK+xOo=" (WebSocket.acceptKey "dGhlIHNhbXBsZSBub25jZQ==")
        checkEq "2fd4e1c67a2d28fced849ee1bb76e7391b93eb12"
          (String.join ((WebSocket.sha1 "The quick brown fox jumps over the lazy dog".toUTF8).toList.map fun b =>
            let h := Nat.toDigits 16 b.toNat; String.ofList (if h.length < 2 then '0' :: h else h)))
        checkEq "Zm9vYmE=" (WebSocket.base64 "fooba".toUTF8)
        for o in ["null", "http://localhost:8766", "http://127.0.0.1", "vscode-webview://abc"] do
          check (WebSocket.localOrigin o) s!"{o} refused"
        for o in ["https://example.com", "http://localhost.example.com", "http://127.0.0.1.nip.io:80"] do
          check (!WebSocket.localOrigin o) s!"{o} let in"
        -- frames of each length class, masked and not, read back
        let ((r, w), (r', w')) ← Socket.pair
        let (r, w, r', w') := (IO.FS.Stream.ofHandle r, IO.FS.Stream.ofHandle w, IO.FS.Stream.ofHandle r', IO.FS.Stream.ofHandle w')
        for n in [0, 125, 126, 65535, 65536, 200000] do
          let text := String.ofList (List.replicate n 'x')
          WebSocket.sendText w text (some (ByteArray.mk #[9, 8, 7, 6]))
          checkEq (some text) (← WebSocket.recvText r' w')
          WebSocket.sendText w' text
          checkEq (some text) (← WebSocket.recvText r w (server := false))
        -- an unmasked frame from a client breaks the protocol
        WebSocket.sendText w "x"
        checkEq none (← WebSocket.recvText r' w') },
    { name := "WebSocket transport (--ws): infoview requests, editing, origins", run := fun _ => do
        let _ ← IO.asTask (prio := .dedicated) (do IO.sleep 60000; IO.eprintln "timed out"; IO.Process.exit 3 : IO Unit)
        try wsCase; IO.Process.exit 0
        catch e => IO.eprintln e; IO.Process.exit 1 }
  ]

/-- The Neovim plugin (editors/nvim, stage 11p): abbreviations and the infoview, in a
headless nvim against the real `wiz lsp`. Skipped when there is no `nvim` (the dev shell
has one). -/
def nvimGroup : Group where
  name := "nvim"
  exercise := "editors/nvim (stage 11p)"
  cases := [
    { name := "wiz.nvim: abbreviations, and the infoview against wiz lsp (editors/nvim/tests/run.sh)", run := fun _ => do
        let out ← IO.Process.output { cmd := "sh", args := #["editors/nvim/tests/run.sh"] }
        if out.stdout.startsWith "skipped" then skip ((out.stdout.replace "skipped: " "").trimAscii.toString)
        else unless out.exitCode == 0 do
          throw (IO.userError s!"editors/nvim/tests/run.sh failed:\n{out.stdout}{out.stderr}") }
  ]

/-- This module's test groups, which `Tests/Main.lean` runs: one per line, in sorted
order, so that branches adding groups rarely touch the same lines. A new group also
needs a shard in `.github/test-shards.json` (CI checks). -/
def groups : List Group :=
  group ::
  nvimGroup ::
  serverGroup ::
  []

end Tests.LSP
