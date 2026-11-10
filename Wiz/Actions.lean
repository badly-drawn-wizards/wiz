import Wiz.Query

/-!
# Code actions

Fixes the language server offers, computed from the info tree and the messages: each is a
title, a kind, the message it fixes (if any) and text edits (a range of character offsets
and its replacement).

* **Did you mean**: an unknown identifier, and the names in scope (locals and globals)
  within edit distance 2.
* **Add missing cases**: a `match` (or equations) whose first column misses constructors
  of an inductive type gets one alternative per missing constructor, `| .c x y => ?c`,
  indented like the first alternative.
* **Add type ascription**: `def f binders := v` becomes `def f binders : T := v`, with the
  type the elaborator inferred.
-/

namespace Wiz.Actions

variable {R : Type} [QRig R] [DecidableEq R] [ToString R] [QuantitySyntax R]

structure Edit where
  start : Nat
  stop : Nat
  text : String
  deriving Repr, BEq

structure Action where
  title : String
  /-- `quickfix` or `refactor.rewrite` -/
  kind : String
  /-- the index of the message it fixes, in `CommandState.messages` -/
  fixes : Option Nat := none
  edits : Array Edit
  deriving Repr

/-- Levenshtein distance. -/
def editDistance (a b : String) : Nat := Id.run do
  let a := a.toList.toArray
  let b := b.toList.toArray
  let mut prev : Array Nat := Array.range (b.size + 1)
  for i in [0:a.size] do
    let mut cur : Array Nat := #[i + 1]
    for j in [0:b.size] do
      let sub := prev[j]! + (if a[i]! == b[j]! then 0 else 1)
      cur := cur.push (min sub (min (prev[j + 1]! + 1) (cur[j]! + 1)))
    prev := cur
  prev[b.size]!

/-- Names within distance 2 of `x` (closest first, at most 5): locals, then globals. -/
def suggestions (s : CommandState R) (x : Name) (locals : List Name) : Array Name :=
  let cands := (locals.filter (!·.contains '✝')).toArray ++ s.globals.order
  let scored := cands.filterMap fun n =>
    if n == x || (n.length + 2 < x.length) || (x.length + 2 < n.length) then none else
    let d := editDistance x n
    if d ≤ 2 then some (d, n) else none
  let sorted := scored.qsort fun (d, n) (d', n') => d < d' || (d == d' && n < n')
  (sorted.map (·.2)).toList.eraseDups.toArray.extract 0 5

/-- The constructors of an inductive type, with their explicit fields' names. -/
def constructors (g : Globals R) (T : Name) : List (Name × List Name) :=
  match g.find? (T ++ ".desc") with
  | none => []
  | some d =>
    let nΔ := (Elab.piInfos d.type).length
    let body := d.value.map fun v => (List.range nΔ).foldl (fun t _ => match t with
      | .lam _ b => b
      | t => t) v
    match body.bind Term.descTag? with
    | some (ls, _, _) => ls.map fun c =>
      let fields := match g.find? (T ++ "." ++ c) with
        | some cd => (Elab.piInfos cd.type).filterMap fun (x, bi, _) =>
          if bi == .default then some (if x == "_" || x.contains '✝' then "x" else x) else none
        | none => []
      (c, fields)
    | _ => []

/-- The innermost entry of the info tree around a range. -/
def around (s : CommandState R) (info : SourceInfo) (p : Info R → Bool) : Option (Info R) :=
  s.infos.foldl (fun acc i =>
    let r := i.info
    if p i && r.start ≤ info.start && info.stop ≤ r.stop then
      match acc with
      | some j => if r.stop - r.start ≤ j.info.stop - j.info.start then some i else acc
      | none => some i
    else acc) none

/-- The constructors a `match` around `info` misses (in its first column), and where it is. -/
def missingCases (s : CommandState R) (info : SourceInfo) : Option (MatchInfo × List (Name × List Name)) := do
  let .matchCases _ m ← around s info (· matches .matchCases ..) | none
  if m.catchAll then none
  let missing := (constructors s.globals m.type).filter fun (c, _) => !m.covered.contains c
  if missing.isEmpty then none
  pure (m, missing)

/-- The column of a character offset. -/
def column (text : String) (off : Nat) : Nat :=
  ((text.toList.take off).reverse.takeWhile (· != '\n')).length

/-- What to tell the client about a message, for code actions: `(code, data fields)`. -/
def messageData (s : CommandState R) (m : Msg) : List (String × List String) :=
  match m.code with
  | "unknown-identifier" =>
    match around s m.info (· matches .unknownIdent ..) with
    | some (.unknownIdent _ x locals) => [("name", [x]), ("suggestions", (suggestions s x locals).toList)]
    | _ => []
  | "missing-case" =>
    match missingCases s m.info with
    | some (_, missing) => [("missing", missing.map (·.1))]
    | none => []
  | _ => []

/-- The code actions for the range `[start, stop]` of `text`. -/
def actionsAt (s : CommandState R) (text : String) (start stop : Nat) : Array Action := Id.run do
  let mut out : Array Action := #[]
  for m in s.messages, k in [0:s.messages.size] do
    unless m.info.start ≤ stop && start ≤ max m.info.stop (m.info.start + 1) do continue
    match m.code with
    | "unknown-identifier" =>
      if let some (.unknownIdent r x locals) := around s m.info (· matches .unknownIdent ..) then
        for n in suggestions s x locals do
          out := out.push { title := s!"Did you mean '{n}'?", kind := "quickfix", fixes := some k,
                            edits := #[{ start := r.start, stop := r.stop, text := n }] }
    | "missing-case" =>
      if let some (mi, missing) := missingCases s m.info then
        let indent := "".pushn ' ' (column text mi.firstAlt.start)
        let extra := String.join (List.replicate (mi.columns - 1) ", _")
        let alts := missing.map fun (c, fs) =>
          s!"\n{indent}| .{c}{String.join (fs.map (" " ++ ·))}{extra} => ?{c}"
        out := out.push { title := "Add missing cases", kind := "quickfix", fixes := some k,
                          edits := #[{ start := mi.lastAlt.stop, stop := mi.lastAlt.stop, text := String.join alts }] }
    | _ => pure ()
  -- a definition without a type, whose name is in the range
  for i in s.infos do
    if let .decl r _ names ty false at_ := i then
      if r.start ≤ stop && start ≤ r.stop && ty.mvars.isEmpty then
        out := out.push { title := "Add type ascription", kind := "refactor.rewrite",
                          edits := #[{ start := at_, stop := at_, text := s!" : {ty.pretty names}" }] }
  out

/-- Apply edits to a text (offsets in characters; the edits must not overlap). -/
def apply (text : String) (edits : Array Edit) : String := Id.run do
  let cs := text.toList.toArray
  let sorted := edits.qsort (·.start > ·.start)
  let mut out := cs
  for e in sorted do
    out := out.extract 0 e.start ++ e.text.toList.toArray ++ out.extract e.stop out.size
  String.ofList out.toList

end Wiz.Actions
