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

variable {R : Type} [QRig R] [DecidableEq R] [ToString R] [QuantitySyntax R] [IsoCache R]

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
      let s' := runFrontend.go input init chars pos s
      (s', eng)
  /-- Elaborate the single command in `[pos, stop)`. -/
  elabOne (chars : Array Char) (pos stop : Nat) (s : CommandState R) : CommandState R :=
    -- run the frontend on exactly this command's text, at its position
    let only := chars.extract 0 stop
    runFrontend.go input init only pos s

/-- The innermost entry of the info tree satisfying `p` whose range contains `off`
(`start ≤ off < stop`, or `≤ stop` if `endIn`); among equal ranges, the last recorded. -/
def innermost (s : CommandState R) (off : Nat) (p : Info R → Bool) (endIn : Bool := false) : Option (Info R) :=
  s.infos.foldl (fun acc i =>
    let r := i.info
    if p i && r.start ≤ off && (off < r.stop || (endIn && off == r.stop)) then
      match acc with
      | some j => if r.stop - r.start ≤ j.info.stop - j.info.start then some i else acc
      | none => some i
    else acc) none

/-- The innermost identifier at a character offset: its name and type. -/
def identAt (s : CommandState R) (off : Nat) : Option (Info R) :=
  innermost s off (· matches .ident ..)

def hoverAt (s : CommandState R) (off : Nat) : Option (Name × String) := do
  let .ident _ n _ names ty ← identAt s off | none
  pure (n, ty.pretty names)

/-- The tactic state at a character offset: inside a `by` block, the goals after the
innermost tactic containing `off` (its end included); between tactics, after the last one
ending before `off`; before the first, the goals the block started with. Returns a key
for the state (its position in the info tree), the range it belongs to, and the goals. -/
def goalsAt (s : CommandState R) (off : Nat) : Option (Nat × SourceInfo × Array (GoalView R)) := do
  let .tactic blk _ before₀ _ ← innermost s off (· matches .tactic _ true ..) (endIn := true) | none
  let inside := s.infos.zipIdx.filter fun (i, _) => match i with
    | .tactic r false .. => blk.start ≤ r.start && r.stop ≤ blk.stop && r.stop > r.start
    | _ => false
  let size (r : SourceInfo) := r.stop - r.start
  -- the innermost tactic containing the cursor (the last recorded, among equal ranges)
  let containing := inside.foldl (fun acc (i, k) =>
    let r := i.info
    if r.start ≤ off && off ≤ r.stop then
      match acc with
      | some (j, _) => if size r ≤ size j.info then some (i, k) else acc
      | none => some (i, k)
    else acc) none
  -- or the last one before it (the outermost, among those ending at the same place)
  let before := inside.foldl (fun acc (i, k) =>
    let r := i.info
    if r.stop ≤ off then
      match acc with
      | some (j, _) => if r.stop > j.info.stop || (r.stop == j.info.stop && size r ≥ size j.info) then some (i, k) else acc
      | none => some (i, k)
    else acc) none
  match (containing.orElse fun _ => before : Option (Info R × Nat)) with
  | some (.tactic r _ _ after, k) => pure (k, r, after)
  | _ =>
    let k := (s.infos.findIdx? fun i => i.info == blk && i matches .tactic _ true ..).getD 0
    pure (k + s.infos.size, blk, before₀)

/-- The expected type at a character offset: the innermost checked term (or hole) around
it, else the innermost identifier (its type, without hypotheses). -/
def termGoalAt (s : CommandState R) (off : Nat) : Option (SourceInfo × GoalView R) :=
  match innermost s off (· matches .term ..) (endIn := true) with
  | some (.term r g _) =>
    -- an identifier strictly inside the term is more precise
    match identAt s off with
    | some (.ident r' _ _ names ty) =>
      if r'.stop - r'.start < r.stop - r.start then some (r', identGoal names ty) else some (r, g)
    | _ => some (r, g)
  | _ => match identAt s off with
    | some (.ident r _ _ names ty) => some (r, identGoal names ty)
    | _ => none
where
  identGoal (names : List Name) (ty : Term R) : GoalView R :=
    -- the locals it mentions, by name (their types aren't recorded with identifiers)
    { hyps := #[], target := names.foldl (fun t n => t.instantiateAt 0 (.const n [])) ty }

/-- Where the global at an offset was declared: its range and module (`""` for this file). -/
def definitionAt (s : CommandState R) (off : Nat) : Option (Name × SourceInfo × String) := do
  let .ident _ n false _ _ ← identAt s off | none
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
