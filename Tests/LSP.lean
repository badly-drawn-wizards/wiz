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
  pure { libs := ({} : Std.HashMap String (String × String)).insert "Prelude" ("lib/Prelude.wiz", ← prelude) }

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
            check (subs.size > 0) s!"{n}: no tags" }
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
        check (has r "-32801") s!"stale resolve: {r.compress}" }
  ]

end Tests.LSP
