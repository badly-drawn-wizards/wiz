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
* **Fill a hole** (`_` or `?x`) from its expected type: an inductive type's constructor
  (one action per constructor, `(.c ?x ?y)`), a structure's or Σ type's anonymous
  constructor with one named hole per field (`⟨?px, ?py⟩`), a function type's
  `fun x => ?_`-style lambda.
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
      let fields := match g.find? (ctorConst T c) with
        | some cd => (Elab.piInfos cd.type).filterMap fun (x, bi, _) =>
          if bi == .default then some (if x == "_" || x.contains '✝' then "x" else x) else none
        | none => []
      (c, fields)
    | _ => []

/-- The field names of a Σ telescope. -/
partial def sigmaFields : Term R → List Name
  | .sigma x _ _ snd _ => x :: sigmaFields snd
  | _ => []

/-- The head constant of a type (applied). -/
def typeHead : Term R → Option Name
  | .const n _ => some n
  | .app f _ => typeHead f
  | _ => none

/-- The fields of the type `ty`: of a Σ, or of a definition unfolding to one (a structure). -/
def fieldsOf (g : Globals R) (ty : Term R) : List Name :=
  match ty with
  | .sigma .. => sigmaFields ty
  | _ => match typeHead ty with
    | some T => match g.find? T with
      | some { value := some v, .. } =>
        let rec body : Nat → Term R → Term R
          | 0, t => t
          | k + 1, .lam _ b => body k b
          | _, t => t
        sigmaFields (body 64 v)
      | _ => []
    | none => []

/-- The fields of the type `ty` with their types (printed). -/
def fieldTypes (g : Globals R) (ty : Term R) : List (Name × String) :=
  let rec go (names : List Name) : Nat → Term R → List (Name × String)
    | 0, _ => []
    | k + 1, .sigma x _ A B _ => (x, A.pretty names) :: go (x :: names) k B
    | _, _ => []
  match ty with
  | .sigma .. => go [] 64 ty
  | _ => match typeHead ty with
    | some T => match g.find? T with
      | some { value := some v, .. } =>
        -- (under the structure's parameters)
        let rec body : Nat → List Name → Term R → List Name × Term R
          | 0, ns, t => (ns, t)
          | k + 1, ns, .lam x b => body k (x :: ns) b
          | _, ns, t => (ns, t)
        let (ns, b) := body 64 [] v
        go ns 64 b
      | _ => []
    | none => []

/-- A name usable for a named hole: `x` for an anonymous or inaccessible one. -/
def holeName (x : Name) : Name :=
  if x == "_" || x.contains '✝' || x.isEmpty then "x" else x

/-- Make the names of a list distinct (`x`, `x₂`, …), avoiding `taken`. -/
def distinct (xs : List Name) (taken : List Name := []) : List Name :=
  let sub (k : Nat) : String := String.ofList ((toString k).toList.map fun c => Char.ofNat (c.toNat - '0'.toNat + '₀'.toNat))
  let (out, _) := xs.foldl (fun (out, seen) x =>
    let rec pick (k : Nat) (fuel : Nat) : Name :=
      let c := if k ≤ 1 then x else x ++ sub k
      match fuel with
      | 0 => c
      | f + 1 => if seen.contains c then pick (k + 1) f else c
    let c := pick 1 100
    (out ++ [c], c :: seen)) ([], taken)
  out

/-- The ways to fill a hole of type `ty` (titles and replacement texts). `paren`: the hole
is an argument, so an application needs parentheses. -/
def holeFillings (g : Globals R) (names : List Name) (ty : Term R) (paren : Bool) : List (String × String) :=
  let wrap (t : String) := if paren then s!"({t})" else t
  match ty with
  | .pi x _ _ _ _ _ =>
    let x := holeName x
    [(s!"Fill with 'fun {x} => ?body'", wrap s!"fun {x} => ?body")]
  | _ =>
    let ctors := match typeHead ty with
      | some T => constructors g T
      | none => []
    if !ctors.isEmpty && ctors.length ≤ 12 then
      ctors.map fun (c, fs) =>
        let hs := distinct (fs.map holeName) names
        if hs.isEmpty then (s!"Fill with '.{c}'", s!".{c}")
        else (s!"Fill with '.{c}'", wrap s!".{c} {" ".intercalate (hs.map ("?" ++ ·))}")
    else match fieldsOf g ty with
      | [] => []
      | fs =>
        let hs := distinct (fs.map holeName) names
        [("Fill with an anonymous constructor", s!"⟨{", ".intercalate (hs.map ("?" ++ ·))}⟩")]

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
          s!"\n{indent}| .{ctorShort c}{String.join (fs.map (" " ++ ·))}{extra} => ?{ctorShort c}"
        out := out.push { title := "Add missing cases", kind := "quickfix", fixes := some k,
                          edits := #[{ start := mi.lastAlt.stop, stop := mi.lastAlt.stop, text := String.join alts }] }
    | _ => pure ()
  -- a hole in the range: fill it from its expected type
  let holes := s.infos.filter fun i => match i with
    | .term r _ true => r.start ≤ stop && start ≤ r.stop && !r.synthetic
    | _ => false
  -- (the innermost one)
  let hole : Option (Info R) := holes.foldl (fun acc i => match acc with
    | some j => if i.info.stop - i.info.start < j.info.stop - j.info.start then some i else acc
    | none => some i) none
  if let some (.term r gv _) := hole then
    let ty := gv.target
    if ty.mvars.isEmpty then
      let chars := text.toList.toArray
      -- an argument (right after a term), where an application needs parentheses
      let prev := Id.run do
        let mut i := r.start
        while i > 0 && (chars[i - 1]! == ' ' || chars[i - 1]! == '\t') do i := i - 1
        pure (if i == 0 then ' ' else chars[i - 1]!)
      let paren := isIdRest prev || prev == ')' || prev == '⟩' || prev == '}'
      for (title, t) in holeFillings s.globals gv.names ty paren do
        out := out.push { title, kind := "refactor.rewrite", edits := #[{ start := r.start, stop := r.stop, text := t }] }
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
