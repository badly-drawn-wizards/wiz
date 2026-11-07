import Wiz.Frontend.Frontend

/-!
# Queries: incremental, deterministic elaboration

Elaboration is a pure function of the source text (and the libraries), so its results
can be **memoised by content**. A file is elaborated command by command; the result of
a command (the state after it) is stored under a **key**: a hash chained through every
command up to it,

    key₀ = hash(libraries)        keyᵢ = hash(keyᵢ₋₁, text of command i)

so a command is re-elaborated only if it, or something before it, changed. The
language server keeps one engine per document; after an edit, the commands before it
come from the memo table at no cost.

Queries on the result (`hoverAt`, `definitionAt`, `completionsAt`) read the final
state: the elaborator records identifiers with their types and ranges, and where each
global was declared.
-/

namespace Wiz.Query

variable {R : Type} [QRig R] [DecidableEq R] [ToString R] [QuantitySyntax R]

structure Engine (R : Type) where
  /-- command results, by chained key -/
  memo : Std.HashMap UInt64 (CommandState R) := {}
  /-- how many commands were elaborated (not reused), for tests and statistics -/
  elaborated : Nat := 0

/-- Elaborate `input` from `init`, reusing memoised commands. `key₀` identifies `init`
(for example, a hash of the libraries it can import). -/
partial def elaborate (eng : Engine R) (input : String) (init : CommandState R) (key₀ : UInt64 := 0) :
    CommandState R × Engine R :=
  go input.toList.toArray 0 init key₀ eng
where
  go (chars : Array Char) (pos : Nat) (s : CommandState R) (key : UInt64) (eng : Engine R) : CommandState R × Engine R :=
    if skipWs chars pos ≥ chars.size then (s, eng) else
    match parseCommand chars s.tables pos with
    | .ok (cmd, stop) =>
      let text := String.ofList (chars.extract pos stop).toList
      let key' := mixHash key (hash text)
      match eng.memo.get? key' with
      | some s' => go chars stop s' key' eng
      | none =>
        -- one command, through the ordinary frontend (imports included)
        let s' := elabOne chars pos stop s
        go chars stop s' key' { eng with memo := eng.memo.insert key' s', elaborated := eng.elaborated + 1 }
    | .error _ =>
      -- let the frontend report the parse error and recover
      let s' := runFrontend.go input chars pos s
      (s', eng)
  /-- Elaborate the single command in `[pos, stop)`. -/
  elabOne (chars : Array Char) (pos stop : Nat) (s : CommandState R) : CommandState R :=
    -- run the frontend on exactly this command's text, at its position
    let only := chars.extract 0 stop
    runFrontend.go input only pos s

/-- The innermost identifier at a character offset: its name and type. -/
def hoverAt (s : CommandState R) (off : Nat) : Option (Name × String) :=
  let hits := s.hovers.filter fun (i, _, _) => i.start ≤ off && off < i.stop
  let best := hits.foldl (fun acc h => match acc with
    | none => some h
    | some (i, _, _) => if h.1.stop - h.1.start < i.stop - i.start then some h else acc) none
  best.map fun (_, n, ty) => (n, ty)

/-- Where the global at an offset was declared: its range and module (`""` for this file). -/
def definitionAt (s : CommandState R) (off : Nat) : Option (Name × SourceInfo × String) := do
  let (n, _) ← hoverAt s off
  let (info, m) ← s.declSites.get? n
  pure (n, info, m)

/-- Globals completing the identifier that ends at `off`. -/
def completionsAt (s : CommandState R) (input : String) (off : Nat) : Array Name :=
  let chars := input.toList.toArray
  let rec back (i : Nat) (fuel : Nat) : Nat :=
    match fuel, i with
    | 0, _ => i
    | _, 0 => 0
    | f + 1, i + 1 =>
      let c := chars[i]!
      if c.isAlphanum || c == '_' || c == '.' || c == '\'' then back i f else i + 1
  let start := back off off
  let pre := String.ofList (chars.extract start off).toList
  (s.globals.order.filter fun n => n.startsWith pre && n != pre).qsort (· < ·) |>.extract 0 200

end Wiz.Query
