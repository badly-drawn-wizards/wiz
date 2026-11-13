import Wiz.Query

/-!
# References and rename

The info tree records every identifier the elaborator resolved, with what it resolved
to: a global by its name, a local by its name in its context. **References** to a
global are its identifiers in every document (the open ones and, under `grail lsp`, the
package's other modules), plus the name in its declaration. A local's references are the
identifiers of that name inside the declaration around the cursor that see the same
binder (the last binder of that name before the use: an approximation of scoping).
**Rename** edits the places that spell the whole name; the language server refuses a
global declared in the toolchain's library and a new name that isn't a name. A use
through generalised field notation (`p.norm` for `Point.norm p`) is not edited.
-/

namespace Wiz.Refs

variable {R : Type} [QRig R] [DecidableEq R] [ToString R] [QuantitySyntax R]

/-- What the cursor is on: a global, or a local (its name, and the declaration around it
as a range). -/
inductive Target where
  | global (n : Name)
  | «local» (x : Name) (scope : SourceInfo) (binder : Option SourceInfo)
  deriving BEq, Inhabited

/-- The command (declaration) range around `off`, from the declaration sites. -/
def commandAround (s : CommandState R) (off : Nat) : Option SourceInfo :=
  s.declSites.fold (init := none) fun acc _ (r, m) =>
    if m.isEmpty && r.start ≤ off && off ≤ r.stop then
      match acc with
      | some r' => if r.stop - r.start < r'.stop - r'.start then some r else acc
      | none => some r
    else acc

/-- The binders of the info tree: `recordBinder` pushes a binder's identifier and then
its goal (a `.term` of the same range); a use has its `.term` first. -/
def binders (s : CommandState R) : Array (Name × SourceInfo) := Id.run do
  let mut out : Array (Name × SourceInfo) := #[]
  let mut prev : Option (Name × SourceInfo) := none
  for i in s.infos do
    match i, prev with
    | Info.term r' _ false, some (x, r) => if r' == r && !r.synthetic then out := out.push (x, r)
    | _, _ => pure ()
    prev := match i with
      | Info.ident r x true .. => some (x, r)
      | _ => none
  out

/-- The binder of the local `x` used at `at_` within `scope`: the last binder of `x` in
`scope` starting at or before `at_` (scoping by position: a binder after the use, or one
whose scope ended, is not considered beyond that approximation). -/
def binderOf (bs : Array (Name × SourceInfo)) (scope : SourceInfo) (x : Name) (at_ : Nat) : Option SourceInfo :=
  bs.foldl (fun acc (n, r) =>
    if n == x && scope.start ≤ r.start && r.start ≤ at_ then
      match acc with
      | some r' => if r.start > r'.start then some r else acc
      | none => some r
    else acc) none

/-- The identifier at `off`, as a target, and its range. -/
def targetAt (s : CommandState R) (off : Nat) : Option (Target × SourceInfo) := do
  let .ident r n isLocal .. ← Query.innermost s off (· matches .ident ..) (endIn := true) | none
  if r.synthetic then none
  if !isLocal then return (.global n, r)
  let scope ← commandAround s off
  pure (.local n scope (binderOf (binders s) scope n r.start), r)

/-- Where the name `n` is written in its declaration `cmd` (the first whole-word
occurrence), as a range. -/
def nameInDecl (text : String) (cmd : SourceInfo) (n : Name) : Option SourceInfo := Id.run do
  let chars := text.toList.toArray
  let ns := n.toList.toArray
  let mut i := cmd.start
  while i + ns.size ≤ min cmd.stop chars.size do
    if (List.range ns.size).all (fun k => chars[i + k]! == ns[k]!) &&
       (i == 0 || !(isIdRest chars[i - 1]! || chars[i - 1]! == '.')) &&
       (i + ns.size ≥ chars.size || !(isIdRest chars[i + ns.size]!)) then
      return some { start := i, stop := i + ns.size }
    i := i + 1
  none

/-- The ranges of `t` in a document (`s`, `text`), declaration included (for a global
declared in it). -/
def rangesIn (s : CommandState R) (text : String) (t : Target) : Array SourceInfo := Id.run do
  let mut out : Array SourceInfo := #[]
  match t with
  | .global n =>
    if let some (cmd, "") := s.declSites.get? n then
      if let some r := nameInDecl text cmd n then out := out.push r
    for i in s.infos do
      if let .ident r m false .. := i then
        if m == n && !r.synthetic && r.stop > r.start then out := out.push r
  | .local x scope b =>
    let bs := binders s
    for i in s.infos do
      if let .ident r m true .. := i then
        if m == x && !r.synthetic && scope.start ≤ r.start && r.stop ≤ scope.stop &&
           binderOf bs scope x r.start == b then out := out.push r
  -- (one per range)
  out.foldl (fun acc r => if acc.any (fun r' => r'.start == r.start && r'.stop == r.stop) then acc else acc.push r) #[]
    |>.qsort (·.start < ·.start)

/-- The text of a range of `text`: what an identifier there must read for a rename to
edit it (a qualified name used by its last part, `p.norm`, is not edited). -/
def textAt (text : String) (r : SourceInfo) : String :=
  String.ofList ((text.toList.drop r.start).take (r.stop - r.start))

/-- Is `n` a name a rename may introduce? -/
def validName (n : String) : Bool :=
  !n.isEmpty && (n.splitOn ".").all fun p => !p.isEmpty && isIdStart p.front && p.all isIdRest

end Wiz.Refs
