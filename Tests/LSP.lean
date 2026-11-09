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
  let init : St := { loader := fun m => if m == "Prelude" then some p else none, termInfo }
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
        let init : St := { loader := fun m => if m == "Prelude" then some p else none, termInfo := true }
        let src := tacticSrc ++ "def f (n : Nat) : Nat := Nat.add n _\ndef h := Nat.add 1 2\n"
        let dir ← IO.FS.createTempDir
        let (cold, _) ← Cache.elaborateCached dir src init 0
        let (warm, hits) ← Cache.elaborateCached dir src init 0
        check (hits > 0) "nothing came from the cache"
        checkEq cold.infos.size warm.infos.size
        for off in [offAfter src "intro A", offAfter src "intro x", offAfter src "n _" (-1), offAfter src "Nat.add 1"] do
          checkEq (goalsText cold off) (goalsText warm off)
          checkEq (termGoalText cold off) (termGoalText warm off) }
  ]

end Tests.LSP
