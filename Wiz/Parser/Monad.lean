import Std.Data.HashMap
import Wiz.Parser.Descr
import Wiz.Parser.Token

/-!
# The parser monad

A parser is a function `PCtx → PState → PResult α`. We write it by hand, not as
`StateT PState (Except _)`, because a *failing* parser still has to return its state:

* the **farthest error**, i.e. the furthest offset any alternative reached together
  with everything that was expected there, which is what produces a useful
  "expected ..." message after backtracking;
* the **memo table** (packrat caching of category parses), so work done inside a
  failed alternative isn't repeated by the next one.

Backtracking is unlimited: `orElse` restores the offset and tries the other branch.
-/

namespace Wiz

structure ParseError where
  pos : Nat := 0
  expected : Array String := #[]
  deriving Repr, Inhabited

def ParseError.render (input : String) (e : ParseError) : String :=
  let (l, c) := lineCol input e.pos
  let exp := if e.expected.isEmpty then "parse error" else
    "expected " ++ ", ".intercalate e.expected.toList
  s!"{l + 1}:{c + 1}: {exp}"

structure MemoKey where
  cat : Name
  prec : Nat
  pos : Nat
  saved : Option Nat
  deriving BEq, Hashable

structure PCtx where
  input : Array Char
  tables : ParserTables
  savedPos? : Option Nat := none
  /-- the precedence the innermost category is being parsed at -/
  prec : Nat := 0
  /-- the words that are not identifiers in the innermost category: the keywords of its
  scope (13j). A function of the category, so the memo key need not mention it. -/
  reserved : Array String := #[]

structure PState where
  pos : Nat := 0
  err : ParseError := {}
  memo : Std.HashMap MemoKey (Option (Syntax × Nat)) := {}
  /-- the token after each offset (where it starts, after whitespace), since alternatives
  look at the same tokens again and again -/
  toks : Std.HashMap Nat (Nat × Except String TokInfo) := {}

inductive PResult (α : Type) where
  | ok (a : α) (s : PState)
  | error (s : PState)

def P (α : Type) : Type := PCtx → PState → PResult α

instance : Monad P where
  pure a := fun _ s => .ok a s
  bind x f := fun c s => match x c s with
    | .ok a s => f a c s
    | .error s => .error s

namespace P

def ctx : P PCtx := fun c s => .ok c s
def state : P PState := fun _ s => .ok s s
def setPos (pos : Nat) : P Unit := fun _ s => .ok () { s with pos }
def withCtx (f : PCtx → PCtx) (p : P α) : P α := fun c s => p (f c) s

/-- Fail at `pos`, recording what was expected there if it is the farthest failure. -/
def failAt (pos : Nat) (expected : String) : P α := fun _ s =>
  let err :=
    if pos > s.err.pos then { pos, expected := #[expected] }
    else if pos == s.err.pos && !s.err.expected.contains expected then
      { s.err with expected := s.err.expected.push expected }
    else s.err
  .error { s with err }

/-- Ordered choice with backtracking. (Only the position is kept for backtracking:
keeping `s` itself while `p` runs would share its memo table with `p`'s state, so that
every `memoStore` in `p` copied the whole table, quadratic in the input's length.) -/
def orElse (p q : P α) : P α := fun c s =>
  let pos := s.pos
  match p c s with
  | .ok a s' => .ok a s'
  | .error s' => q c { s' with pos }

instance : OrElse (P α) := ⟨fun p q => orElse p (q ())⟩

/-- Run `p`; on failure, backtrack and return `none`. -/
def try? (p : P α) : P (Option α) := orElse (some <$> p) (pure none)

def memoLookup (k : MemoKey) : P (Option (Option (Syntax × Nat))) := fun _ s =>
  .ok s.memo[k]? s

def memoStore (k : MemoKey) (v : Option (Syntax × Nat)) : P Unit := fun _ s =>
  .ok () { s with memo := s.memo.insert k v }

/-- Offset of the next significant character. -/
def nextPos : P Nat := do
  let c ← ctx
  let s ← state
  match s.toks[s.pos]? with
  | some (i, _) => pure i
  | none => pure (skipWs c.input s.pos)

/-- Look at the next token without consuming it. `none` at the end of input. -/
def peekToken : P (Option TokInfo) := fun c s =>
  let ((i, r), s) := match s.toks[s.pos]? with
    | some e => (e, s)
    | none =>
      let i := skipWs c.input s.pos
      let e := (i, readToken c.tables.tokens c.input i)
      (e, { s with toks := s.toks.insert s.pos e })
  if i ≥ c.input.size then .ok none s
  else match r with
    | .ok t => .ok (some t) s
    | .error msg => failAt i msg c s

/-- Consume the next token. -/
def nextToken (expected : String) : P TokInfo := do
  match ← peekToken with
  | some t => setPos t.stop; pure t
  | none => failAt (← nextPos) expected

end P

/-- Run a parser on a whole input. -/
def P.run (p : P α) (input : Array Char) (tables : ParserTables) (pos : Nat := 0) :
    Except ParseError (α × Nat) :=
  match p { input, tables } { pos } with
  | .ok a s => .ok (a, s.pos)
  | .error s => .error s.err

end Wiz
