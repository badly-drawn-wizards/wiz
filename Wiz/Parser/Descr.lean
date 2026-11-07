import Std.Data.HashMap
import Wiz.Syntax.Basic

/-!
# Grammars as data

Every parser, built in or user-declared, is a `ParserDescr`: a small combinator
language that `Wiz.Parser.Interp` interprets. Keeping grammars as **data** instead of
compiled code means a `syntax` declaration works without a compiler, and parser tables
can be serialised and cached like any other declaration.

Grammars are organised into **syntax categories** (`term`, `command`, user-declared
ones). Each category has

* **leading** parsers, which start a phrase (`fun x => b`, `(t)`, an identifier), and
* **trailing** parsers, which continue a phrase that already has a left-hand side
  (application `f a`, an infix operator `a + b`).

This is Pratt parsing. Precedences follow Lean: higher binds tighter.

* A leading parser has a precedence: the phrase it builds can only appear where at
  least that precedence is allowed.
* `cat c p` parses category `c` at minimum precedence `p`.
* A trailing parser has its own precedence and a `lhsPrec`: it only applies if the
  phrase to its left has at least that precedence.
-/

namespace Wiz

def maxPrec : Nat := 1024
def argPrec : Nat := 1023
def leadPrec : Nat := 1022
def minPrec : Nat := 10

inductive ParserDescr where
  /-- a keyword or symbol token, added to the token table -/
  | atom (tok : String)
  /-- an identifier spelled `tok`, *not* reserved (so `name` stays usable as a variable) -/
  | nonReserved (tok : String)
  | ident
  | num
  | str
  /-- a phrase of category `name` with precedence at least `prec` -/
  | cat (name : Name) (prec : Nat)
  | seq (ps : Array ParserDescr)
  /-- zero or more; result is one `null` node -/
  | many (p : ParserDescr)
  | many1 (p : ParserDescr)
  /-- result is a `null` node, empty if `p` didn't match -/
  | optional (p : ParserDescr)
  /-- `p (sep p)*`, separators included in the `null` node -/
  | sepBy (p : ParserDescr) (sep : String) (allowTrailing : Bool := false)
  | sepBy1 (p : ParserDescr) (sep : String) (allowTrailing : Bool := false)
  /-- ordered choice: try `p`, and only if it fails try `q` -/
  | orelse (p q : ParserDescr)
  /-- wrap the results of `p` in a node of the given kind -/
  | node (kind : Name) (p : ParserDescr)
  /-- remember the position of the next token, for `colGt`/`colGe` inside `p` -/
  | withPosition (p : ParserDescr)
  /-- forget the remembered position (inside brackets, layout doesn't matter) -/
  | withoutPosition (p : ParserDescr)
  /-- the next token is in a column strictly right of the remembered position -/
  | colGt
  | colGe
  /-- no whitespace between the previous token and the next one -/
  | noWs
  /-- succeed only if the enclosing category is being parsed at precedence ≤ `prec`.
  `Type u` uses this so that in `f Type A`, `A` is an argument and not a level. -/
  | checkPrec (prec : Nat)
  deriving Repr, Inhabited, BEq

namespace ParserDescr

instance : Coe String ParserDescr := ⟨atom⟩

/-- All reserved tokens a descriptor mentions. -/
partial def tokens : ParserDescr → List String
  | atom t => [t]
  | seq ps => ps.toList.flatMap tokens
  | many p | many1 p | optional p | node _ p | withPosition p | withoutPosition p => tokens p
  | sepBy p s _ | sepBy1 p s _ => s :: tokens p
  | orelse p q => tokens p ++ tokens q
  | _ => []

end ParserDescr

structure LeadingParser where
  kind : Name
  prec : Nat
  priority : Nat := 0
  p : ParserDescr
  deriving Repr, Inhabited

structure TrailingParser where
  kind : Name
  prec : Nat
  lhsPrec : Nat
  priority : Nat := 0
  p : ParserDescr
  deriving Repr, Inhabited

structure Category where
  leading : Array LeadingParser := #[]
  trailing : Array TrailingParser := #[]
  deriving Inhabited

/-- All grammar state. Lives in the environment once stage 3 introduces one. -/
structure ParserTables where
  cats : Std.HashMap Name Category := {}
  /-- reserved tokens; a list is fine at our scale (see the optional trie exercise) -/
  tokens : Array String := #[]
  /-- every node kind in use, so generated kind names stay unique -/
  kinds : Std.HashMap Name Unit := {}
  deriving Inhabited

namespace ParserTables

def addTokens (t : ParserTables) (toks : List String) : ParserTables :=
  { t with tokens := toks.foldl (fun acc tok => if acc.contains tok then acc else acc.push tok) t.tokens }

def declareCategory (t : ParserTables) (c : Name) : ParserTables :=
  if t.cats.contains c then t else { t with cats := t.cats.insert c {} }

/-- Keywords spelled like identifiers are reserved only by `term` and `command` syntax:
elsewhere (tactics such as `first` or `exact`) they are `nonReserved`, so they stay
usable as names (stage 13). -/
partial def _root_.Wiz.ParserDescr.unreserve : ParserDescr → ParserDescr
  | .atom t => if t != "" && (t.front.isAlpha || t.front == '_') && t.all (fun c => c.isAlphanum || c == '_') then .nonReserved t else .atom t
  | .seq ps => .seq (ps.map unreserve)
  | .many p => .many p.unreserve
  | .many1 p => .many1 p.unreserve
  | .optional p => .optional p.unreserve
  | .sepBy p s tr => .sepBy p.unreserve s tr
  | .sepBy1 p s tr => .sepBy1 p.unreserve s tr
  | .orelse p q => .orelse p.unreserve q.unreserve
  | .node k p => .node k p.unreserve
  | .withPosition p => .withPosition p.unreserve
  | .withoutPosition p => .withoutPosition p.unreserve
  | p => p

def reservesKeywords (c : Name) : Bool := c == "term" || c == "command"

def addLeading (t : ParserTables) (c : Name) (lp : LeadingParser) : ParserTables :=
  let lp := if reservesKeywords c then lp else { lp with p := lp.p.unreserve }
  let cat := t.cats.getD c {}
  { t.addTokens lp.p.tokens with
    cats := t.cats.insert c { cat with leading := cat.leading.push lp }
    kinds := t.kinds.insert lp.kind () }

def addTrailing (t : ParserTables) (c : Name) (tp : TrailingParser) : ParserTables :=
  let tp := if reservesKeywords c then tp else { tp with p := tp.p.unreserve }
  let cat := t.cats.getD c {}
  { t.addTokens tp.p.tokens with
    cats := t.cats.insert c { cat with trailing := cat.trailing.push tp }
    kinds := t.kinds.insert tp.kind () }

end ParserTables

end Wiz
