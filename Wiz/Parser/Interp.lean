import Wiz.Parser.Monad

/-!
# Interpreting grammars

`runDescr` interprets one `ParserDescr`, and `categoryParser` is the Pratt loop for a
syntax category. They are mutually recursive because `cat` descriptors call back into
categories.

## Choosing between parsers

Within a category, *all* applicable leading parsers are tried from the same offset and
the one that consumes the **most input** wins. Ties go to the higher priority, then to
the parser **declared later**, so a user `syntax` declaration can override a built-in
one deterministically. Trailing parsers are chosen the same way.

Longest match makes grammars compose: `(x : A) → B` (a dependent arrow) and `(x : A)`
(a type ascription) both start with `(`. The arrow consumes more, so it wins.

Trying every alternative would be exponential on nested input, so category parses are
memoised by `(category, precedence, offset, saved position)`. This is packrat parsing.
-/

namespace Wiz

open P

/-- Column of an offset, 0-based. -/
def colOf (input : Array Char) (i : Nat) : Nat :=
  go i 0 i
where
  go (j col : Nat) : Nat → Nat
    | 0 => col
    | fuel + 1 => if j > 0 && input[j - 1]! != '\n' then go (j - 1) (col + 1) fuel else col

private def tokSyntax (t : TokInfo) : Syntax :=
  let info := { start := t.start, stop := t.stop }
  match t.tok with
  | .atom v => .atom info v
  | .ident n => .ident info n
  | .num d => .node info Syntax.numKind #[.atom info d]
  | .str s => .node info Syntax.strKind #[.atom info s]

/-- Pack the results of one iteration of `many`/`optional`: a single result stays as
is, otherwise wrap them in a `null` node. -/
def packItems (items : Array Syntax) : Syntax :=
  if h : items.size = 1 then items[0] else Syntax.mkNull items

/-- A successful alternative: what it built, where it stopped, and its rank. -/
structure Candidate where
  stx : Syntax
  stop : Nat
  prec : Nat
  priority : Nat
  index : Nat
  /-- the parser state after it ran (offset, errors, memo) -/
  state : PState

/-- **Exercise 2.5a.** Pick the winning candidate: the furthest `stop`, then the
highest `priority`, then the highest `index` (declared latest). -/
def Candidate.best (cs : Array Candidate) : Option Candidate :=
  sorry

/-- Run `p` from the current state as one alternative among several. On success it
returns the candidate *without* committing to its state; on failure it still keeps the
error and memo information. -/
def tryAlternative (p : P Syntax) (prec priority index : Nat) : P (Option Candidate) :=
  fun c s => match p c s with
    | .ok stx s' => .ok (some { stx, stop := s'.pos, prec, priority, index, state := s' })
        { s with err := s'.err, memo := s'.memo }
    | .error s' => .ok none { s with err := s'.err, memo := s'.memo }

/-- Commit to a candidate's state, keeping the accumulated errors and memo. -/
def commit (cand : Candidate) : P Unit := fun _ s =>
  .ok () { cand.state with err := s.err, memo := s.memo }

mutual

/-- **Exercise 2.4.** Interpret a descriptor, returning the syntax it produced.
Most cases are done; implement `many`, `many1`, `optional`, `sepBy` and `sepBy1`.

* `many p`: repeat `p` (with `try?`) until it fails **or stops making progress**, and
  return a single `null` node of the iterations, each one packed with `packItems`.
* `many1 p`: the same, but at least one iteration is required.
* `optional p`: a `null` node containing `p`'s items, or an empty one.
* `sepBy p sep allowTrailing`: `p (sep p)*` with the separator atoms included in the
  `null` node. With `allowTrailing`, a final `sep` is allowed. Empty input is fine.
* `sepBy1`: at least one `p`. -/
partial def runDescr : ParserDescr → P (Array Syntax)
  | .atom tok => do
    let i ← nextPos
    match ← peekToken with
    | some t@{ tok := .atom v, .. } =>
      if v == tok then setPos t.stop; pure #[tokSyntax t] else failAt i s!"'{tok}'"
    | _ => failAt i s!"'{tok}'"
  | .nonReserved tok => do
    let i ← nextPos
    match ← peekToken with
    | some t@{ tok := .ident v, .. } | some t@{ tok := .atom v, .. } =>
      if v == tok then setPos t.stop; pure #[.atom { start := t.start, stop := t.stop } tok]
      else failAt i s!"'{tok}'"
    | _ => failAt i s!"'{tok}'"
  | .ident => do
    let i ← nextPos
    match ← peekToken with
    | some t@{ tok := .ident _, .. } => setPos t.stop; pure #[tokSyntax t]
    | _ => failAt i "identifier"
  | .num => do
    let i ← nextPos
    match ← peekToken with
    | some t@{ tok := .num _, .. } => setPos t.stop; pure #[tokSyntax t]
    | _ => failAt i "numeral"
  | .str => do
    let i ← nextPos
    match ← peekToken with
    | some t@{ tok := .str _, .. } => setPos t.stop; pure #[tokSyntax t]
    | _ => failAt i "string literal"
  | .cat c prec => return #[← categoryParser c prec]
  | .seq ps => ps.foldlM (fun acc p => return acc ++ (← runDescr p)) #[]
  | .many p => sorry
  | .many1 p => sorry
  | .optional p => sorry
  | .sepBy p sep trailing => sorry
  | .sepBy1 p sep trailing => sorry
  | .orelse p q => runDescr p <|> runDescr q
  | .node k p => do
    let start ← nextPos
    let items ← runDescr p
    let stop := (← state).pos
    return #[.node { start := min start stop, stop } k items]
  | .withPosition p => do
    let i ← nextPos
    withCtx (fun c => { c with savedPos? := some i }) (runDescr p)
  | .withoutPosition p => withCtx (fun c => { c with savedPos? := none }) (runDescr p)
  | .colGt => do
    let c ← ctx
    let i ← nextPos
    match c.savedPos? with
    | some sp =>
      if colOf c.input i > colOf c.input sp then pure #[]
      else failAt i s!"token right of column {colOf c.input sp + 1}"
    | none => pure #[]
  | .colGe => do
    let c ← ctx
    let i ← nextPos
    match c.savedPos? with
    | some sp =>
      if colOf c.input i ≥ colOf c.input sp then pure #[]
      else failAt i s!"token at or right of column {colOf c.input sp + 1}"
    | none => pure #[]
  | .noWs => do
    let s ← state
    if (← nextPos) == s.pos then pure #[] else failAt s.pos "no space before this token"

/-- **Exercise 2.5b.** The Pratt loop for category `c` at minimum precedence `rbp`.

1. Leading: try every leading parser of `c` with `prec ≥ rbp` (as `node kind p`,
   using `tryAlternative`). If none succeeds, fail with `"<c>"` expected. Otherwise
   `commit` to `Candidate.best`. The current left-hand side is now that node, and the
   current `lhsPrec` is that parser's `prec`.
2. Trailing, repeatedly: try every trailing parser with `prec ≥ rbp` and
   `lhsPrec ≤ current lhsPrec`. The result is a node of the trailing parser's kind whose
   children are the current left-hand side followed by the trailing parser's items.
   Ignore alternatives that consume nothing, or the loop would never end. Commit to
   the best one and continue; stop when none applies.

The memoisation around this is already written in `categoryParser`. -/
partial def categoryLoop (c : Name) (rbp : Nat) : P Syntax := do
  let tables := (← ctx).tables
  let some cat := tables.cats[c]? | failAt (← nextPos) s!"declared syntax category {c}"
  sorry

/-- Memoised category parser. -/
partial def categoryParser (c : Name) (rbp : Nat) : P Syntax := do
  let key : MemoKey := { cat := c, prec := rbp, pos := (← state).pos, saved := (← ctx).savedPos? }
  match ← memoLookup key with
  | some (some (stx, stop)) => setPos stop; pure stx
  | some none => failAt (← nextPos) c
  | none =>
    match ← try? (categoryLoop c rbp) with
    | some stx => memoStore key (some (stx, (← state).pos)); pure stx
    | none => memoStore key none; failAt (← nextPos) c

end

/-- Parse one phrase of a category, then require the end of input. Mainly for tests. -/
def parseCategory (tables : ParserTables) (c : Name) (input : String) :
    Except String Syntax :=
  let chars := input.toList.toArray
  let p : P Syntax := do
    let stx ← categoryParser c 0
    let i ← nextPos
    if i < chars.size then failAt i "end of input" else pure stx
  match p.run chars tables with
  | .ok (stx, _) => .ok stx
  | .error e => .error (e.render input)

end Wiz
