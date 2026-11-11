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

Keyed on the error codes (`Wiz/Core/ErrorCode.lean`, `docs/error-codes.md`), with what the
elaborator recorded at the error (`Info.fix`):

* `no-such-field`: **did you mean** a field of the structure, or for a data type a name
  in its namespace (`t.f` is `T.f t`), within edit distance 2;
* `unknown-constructor`: **did you mean** a constructor of the type;
* `unknown-module`: **did you mean** a module the server knows (`modules`);
* `unknown-identifier`: **add the missing import** of a module (of the package or the
  library) that declares the name;
* `wrong-argument-count`, when the count is off by the implicit parameters: **give the
  implicit arguments explicitly** (`f A x` ↦ `@f A x`); and an error inside `@f a…` with
  as many arguments as `f` has explicit parameters: **let them be inferred** (drop the `@`).
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

/-- Where the name `x` is written in `text` within `info`: the first occurrence at
identifier boundaries (`dotted`: right after a `.`, as a field or a constructor `.c`). -/
def findName (text : String) (info : SourceInfo) (x : String) (dotted : Bool := false) : Option (Nat × Nat) := Id.run do
  let cs := text.toList.toArray
  let xs := x.toList.toArray
  let idChar (c : Char) := c.isAlphanum || c == '_' || c == '\'' || c == '!' || c == '?'
  let stop := min (max info.stop (info.start + 1)) cs.size
  let mut i := info.start
  while i + xs.size ≤ stop do
    if (cs.extract i (i + xs.size)) == xs then
      let before := if i == 0 then none else cs[i - 1]?
      let after := cs[i + xs.size]?
      let okBefore := if dotted then before == some '.' else !(before.any idChar)
      if okBefore && !(after.any idChar) then return some (i, i + xs.size)
    i := i + 1
  none

/-- The data an `Info.fix` recorded for a message (same range, same code). -/
def fixData (s : CommandState R) (m : Msg) (code : String) : Option (List (String × List String)) :=
  s.infos.findSome? fun
    | .fix i c d => if c == code && i.start == m.info.start && i.stop == m.info.stop then some d else none
    | _ => none

def one (d : List (String × List String)) (k : String) : Option String := (d.lookup k).bind (·.head?)

/-- The names `t.f` may mean for `t : T`: the fields of a structure `T`, and (generalised
field notation, `T.f t`) the names in `T`'s namespace, without the `T.` (other modules'
private names, and declarations nobody writes by hand, left out). -/
def fieldCandidates (g : Globals R) (T : Name) (fieldsOnly : Bool) : Array String :=
  let fields := (((Elab.structLayout? g T).map (·.fields)).getD []).toArray
  if fieldsOnly then fields else
  let internal := ["desc", "rec", "recN", "casesOn", "casesOnN", "scasesOn", "scasesOnN"]
  let pre := T ++ "."
  let ns := g.order.filterMap fun n =>
    let n := if n.startsWith "_private." then
        if n.startsWith (Globals.privateName g.module "") then Globals.privateBase n else ""
      else n
    if n.startsWith pre then
      let rest := (n.drop pre.length).toString
      if rest.contains '.' || rest.contains '✝' || internal.contains rest then none else some rest
    else none
  (fields ++ ns).toList.eraseDups.toArray

/-- The words of a declaration's first line after its modifiers (`partial (default := w)`,
`sealed`, …), with `depth` parenthesised words still to skip. -/
def skipModifiers : List String → Nat → List String
  | w :: rest, depth + 1 => skipModifiers rest (if w.endsWith ")" then depth else depth + 1)
  | w :: rest, 0 =>
    if ["partial", "sealed", "noncomputable", "unsafe"].contains w then skipModifiers rest 0
    else if w.startsWith "(" then (if w.endsWith ")" then skipModifiers rest 0 else skipModifiers rest 1)
    else w :: rest
  | [], _ => []

/-- Does a module's source declare `x` (not privately)? `def x`, `inductive x`, …, or a
name `T.c` of a type `T` it declares. -/
def declares (src : String) (x : Name) : Bool :=
  let kws := ["def", "theorem", "axiom", "inductive", "coinductive", "structure", "class", "extern",
    "instance", "foreign_type", "abbrev"]
  let declared := (src.splitOn "\n").filterMap fun line =>
    let ws := ((line.trimAsciiStart.toString.splitOn " ").filter (· ≠ ""))
    match skipModifiers ws 0 with
    | kw :: n :: _ =>
      if !kws.contains kw then none else
      let n := String.ofList (n.toList.takeWhile fun c => !" (:{[".contains c)
      let n := ((n.splitOn ".{").headD n)
      if n.isEmpty then none else some n
    | _ => none
  declared.contains x ||
    match x.splitOn "." with
    | _ :: _ :: _ => declared.contains (".".intercalate (x.splitOn ".").dropLast)
    | _ => false

/-- Where an `import` line goes: after the last one at the top of the file (or at its start). -/
def importAt (text : String) : Nat := Id.run do
  let mut off := 0
  let mut at_ := 0
  for line in text.splitOn "\n" do
    let l := line.trimAsciiStart.toString
    if l.startsWith "import " then at_ := off + line.length + 1
    else if !(l.isEmpty || l.startsWith "--") then break
    off := off + line.length + 1
  return min at_ text.length

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

/-- The constructors of `T`, by their short names. -/
def constructorCandidates (g : Globals R) (T : Name) : Array String :=
  let cs := (constructors g T).map (·.1)
  if !cs.isEmpty then cs.toArray else
  -- a structure or a coinductive type: `mk`
  (fieldCandidates g T false).filter (· == "mk")

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

/-- The module an `unknown-module` message is about, and where its name is written. -/
def unknownModule (text : String) (m : Msg) : Option (Name × Nat × Nat) := do
  let name := ((m.text.splitOn "unknown module ").getD 1 "").trimAscii.toString
  if name.isEmpty then none
  let (a, b) ← findName text m.info name
  pure (name, a, b)

/-- The name a quick fix of message `m` would replace, where it is written, and the names
it may mean (closest first), for `no-such-field`, `unknown-constructor` and
`unknown-module`. -/
def misspelt (s : CommandState R) (text : String) (modules : List (Name × String)) (m : Msg) :
    Option (String × (Nat × Nat) × Array String) := do
  match m.code with
  | "no-such-field" =>
    let d ← fixData s m ErrorCode.noSuchField
    let f ← one d "name"
    let T ← one d "type"
    let fieldsOnly := (d.lookup "fieldsOnly").isSome
    -- (a field of a structure update `{ t with f := … }` has no `.` before it)
    let r ← findName text m.info f (dotted := (d.lookup "update").isNone)
    pure (f, r, closest f (fieldCandidates s.globals T fieldsOnly))
  | "unknown-constructor" =>
    let d ← fixData s m ErrorCode.unknownConstructor
    let c ← one d "name"
    let T ← one d "type"
    let r ← (findName text m.info c (dotted := true)) <|> findName text m.info c
    pure (c, r, closest c (constructorCandidates s.globals T))
  | "unknown-module" =>
    let (n, a, b) ← unknownModule text m
    pure (n, (a, b), closest n (modules.map (·.1)).toArray)
  | _ => none

/-- The modules (not imported yet, and not this file) that declare the unknown name `x`. -/
def importsFor (s : CommandState R) (text : String) (modules : List (Name × String)) (x : Name) : List Name :=
  ((modules.filter fun (n, src) => !s.imported.contains n && n != s.module && src != text && declares src x).map (·.1)).mergeSort (· ≤ ·)
    |>.take 3

/-- An `Nat` field of an `Info.fix`'s data. -/
def num (d : List (String × List String)) (k : String) : Nat := ((one d k).bind String.toNat?).getD 0

/-- `wrong-argument-count` off by the implicit parameters: `f` given more arguments than it
has explicit parameters, but no more than it has parameters. -/
def implicitsGiven? (s : CommandState R) (m : Msg) : Option (Name × Nat) := do
  let d ← fixData s m ErrorCode.wrongArgumentCount
  let f ← one d "head"
  if (d.lookup "written").any (!·.isEmpty) then none
  let (e, i, n) := (num d "explicit", num d "implicit", num d "given")
  if i == 0 || n ≤ e || e + i < n then none
  pure (f, num d "at")

/-- An `@f a…` around the message, with as many arguments as `f` has explicit parameters:
`f` and where the `@` is. -/
def explicitApp? (s : CommandState R) (text : String) (m : Msg) : Option (Name × Nat) := do
  let .fix _ _ d ← around s m.info (· matches .fix _ "explicit-app" _) | none
  let f ← one d "head"
  let at_ := num d "at"
  if text.toList[at_]? != some '@' then none
  pure (f, at_)

/-- What to tell the client about a message, for code actions: `(code, data fields)`. -/
def messageData (s : CommandState R) (m : Msg) (text : String := "") (modules : List (Name × String) := []) :
    List (String × List String) :=
  match m.code with
  | "unknown-identifier" =>
    match around s m.info (· matches .unknownIdent ..) with
    | some (.unknownIdent _ x locals) =>
      -- (not the modules that declare it: that scans their sources, so it waits for the
      -- code action request)
      [("name", [x]), ("suggestions", (suggestions s x locals).toList)]
    | _ => []
  | "missing-case" =>
    match missingCases s m.info with
    | some (_, missing) => [("missing", missing.map (·.1))]
    | none => []
  | "no-such-field" | "unknown-constructor" | "unknown-module" =>
    match misspelt s text modules m with
    | some (x, _, ns) => [("name", [x]), ("suggestions", ns.toList)]
    | none => []
  | _ => []

/-- The code actions for the range `[start, stop]` of `text`; `modules` are the modules
`import` can reach, with their sources (for "did you mean" on an import, and "add the
missing import"). -/
def actionsAt (s : CommandState R) (text : String) (start stop : Nat) (modules : List (Name × String) := []) :
    Array Action := Id.run do
  let mut out : Array Action := #[]
  for m in s.messages, k in [0:s.messages.size] do
    unless m.info.start ≤ stop && start ≤ max m.info.stop (m.info.start + 1) do continue
    match m.code with
    | "unknown-identifier" =>
      if let some (.unknownIdent r x locals) := around s m.info (· matches .unknownIdent ..) then
        for n in suggestions s x locals do
          out := out.push { title := s!"Did you mean '{n}'?", kind := "quickfix", fixes := some k,
                            edits := #[{ start := r.start, stop := r.stop, text := n }] }
        let at_ := importAt text
        for md in importsFor s text modules x do
          out := out.push { title := s!"Add `import {md}`", kind := "quickfix", fixes := some k,
                            edits := #[{ start := at_, stop := at_, text := s!"import {md}\n" }] }
    | "no-such-field" | "unknown-constructor" | "unknown-module" =>
      if let some (_, (a, b), ns) := misspelt s text modules m then
        for n in ns do
          out := out.push { title := s!"Did you mean '{n}'?", kind := "quickfix", fixes := some k,
                            edits := #[{ start := a, stop := b, text := n }] }
    | "missing-case" =>
      if let some (mi, missing) := missingCases s m.info then
        let indent := "".pushn ' ' (column text mi.firstAlt.start)
        let extra := String.join (List.replicate (mi.columns - 1) ", _")
        let alts := missing.map fun (c, fs) =>
          s!"\n{indent}| .{c}{String.join (fs.map (" " ++ ·))}{extra} => ?{c}"
        out := out.push { title := "Add missing cases", kind := "quickfix", fixes := some k,
                          edits := #[{ start := mi.lastAlt.stop, stop := mi.lastAlt.stop, text := String.join alts }] }
    | _ => pure ()
    if m.code == ErrorCode.wrongArgumentCount then
      if let some (f, at_) := implicitsGiven? s m then
        out := out.push { title := s!"Give the implicit arguments explicitly: @{Globals.privateBase f}", kind := "quickfix",
                          fixes := some k, edits := #[{ start := at_, stop := at_, text := "@" }] }
    if m.severity == .error then
      if let some (f, at_) := explicitApp? s text m then
        out := out.push { title := s!"Let the implicit arguments of {Globals.privateBase f} be inferred: drop the @",
                          kind := "quickfix", fixes := some k, edits := #[{ start := at_, stop := at_ + 1, text := "" }] }
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
