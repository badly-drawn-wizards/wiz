# Stage 13: the language, for programs this size

Writing the lexer and parser in Wiz showed what the language lacked:

* **Recursion on any argument.** The structural argument is the first one the first
  clause matches; parameters before the colon may be passed unchanged or left out.
* **`partial def` and `mutual … end`.** General recursion: the kernel treats the
  definition as opaque, justified by a witness of its type (22f, so no `False`), and its
  implementation (checked against the type) is what `#eval` and compiled code run. The
  parser's core is a mutual block, with no fuel.
* **Mutual inductive types.** `mutual inductive A … inductive B … end` becomes one
  family indexed by a tag type, `A_B : A_B.Tag → Type`, with `def A := A_B .A`.
  Recursion over a family at a concrete index (`SyntaxF .false`) works.
* **`match` without an expected type**, **tuple patterns** `(a, b, c)`, and `x |> f`.
* Keywords of tactic syntax (`first`, `exact` …) are no longer reserved words.
* The prelude has `Nat.lt` (native at runtime), `Nat.le`, `Nat.max`, `Bool.and/or/not`.

## 13a: named arguments ✅

```
class BitPack (A : Type) where
  width : Nat
def bitWidth (0 A : Type) [BitPack A] : Nat := BitPack.width (A := A)
def sub (a b : Nat) : Nat := Nat.sub a b
#eval sub (b := 1) 5                    -- 4
#eval @BitPack.width (A := Bool) _
```

As in Lean, an argument `(x := e)` fills the parameter named `x`, wherever it is:
implicit, instance or explicit. The other arguments fill the explicit parameters in
order (with `@f`, every parameter), and implicit and instance parameters before a named
one get metavariables and instance problems. A named argument after the last positional
one fills its parameter; an explicit parameter before it with no argument is an error
(Lean would abstract it). Unknown and repeated names are errors (`inferAppNamed`,
`Elab/Term.lean`; test group `elabfix`).

## 13b: private declarations and private constructors ✅

```
private def secret : Nat := 42          -- visible only in this module
structure Shr (ρ : Region) (A : Type) where
  private mk ::                         -- only this module makes a `Shr`
  val : A
```

`private` before a command makes every name it declares (a definition, an axiom, a
structure with its constructor and projections, an inductive type with its
constructors and recursors) private to its **module**: other modules get "'x' is
private to module M"; the module itself, including its later declarations, uses the
names as usual. Privacy is per module ([23c](23-grail.md): each module is elaborated in isolation and
under its own name), and the main file is a module of its own.

`private mk ::` right after a structure's `where` keeps the type and its projections
public but makes the constructor private. Types are structural, so a private name
alone would not stop another module from building a value: a tuple `(5, ())`, or a
structure of its own with the same fields, converts to the type. So outside its module
such a structure is also **opaque** to the elaborator: its definition doesn't unfold
(`Globals.elabView`), it is equal only to itself, and `p.val` reads it through the
projection function `S.val` (`p.1` doesn't work). Within the module nothing changes.
Like Lean's, privacy is enforced by the elaborator: the kernel checks every declaration
against the full environment, where an opaque structure is its Σ again (which is sound:
whatever converts with the definition hidden converts with it unfolded).

The motivating use is `lib/Region.wiz` ([22g](22-numbers.md)): the constructors of the borrow handles
`Shr`, `Uniq`, `Mut` and `Lent` are private, so a handle at a region comes only from a
scope or an operation of the library, and hand-written Wiz can't forge one
(`drafts/rust/rejected/forge_handle.wiz`; test group `regions`). `MutOpt`'s constructors
stay public: their fields are handles already.

```
inductive Tok where
  | num (n : Nat)
  | private secret (n : Nat)            -- only this module makes a `.secret`
coinductive Signal (d : Domain) (A : Type) where
  private head : A                      -- only this module observes a signal
  private tail : Signal d A
structure Acct where
  owner : Nat
  private bal : Nat                     -- `Acct.bal` is private; `Acct.mk` isn't
```

The same opacity covers the other declarations with private parts. In each case the
private names are private to the module, and **elsewhere the type is opaque**: it is a
type constant that equals only itself, so the primitives (`con`, `cocon`, `out`, `.1`),
tuples and look-alike types don't convert to it.

* `| private c …` (an `inductive`): `T.c` is private, and so are the recursors `T.rec`,
  `T.casesOn` (and `scasesOn`, `recN`, `casesOnN`). The public constructors stay usable,
  also as `.c` against an expected `T`. Outside the module a `T` can't be **matched**,
  not even on its public constructors with a catch-all: a `match` compiles to
  `T.casesOn`, whose case for `c` hands out `c`'s fields, and the case tree needs `T`'s
  description, which is what the opacity hides. So exhaustiveness never comes up
  there; the module exports the eliminators it wants (`Tok.value`, or a fold). In a
  `mutual` block the types are one indexed family, so a private constructor makes the
  whole family opaque.
* `private f : A` (an observation of a `coinductive`): `T.f` is private, and so is the
  coconstructor `T.mk` (it would build a value from the private observation's value).
  Outside the module a `T` isn't observed through `f` (`s.f`, `T.f s`, `out s`) and
  isn't defined by **copatterns**, which give every observation ("'Signal.head' is
  private to module Signal: a Signal can't be defined by copatterns outside it"); public
  observations are read through their functions, `s.g`.
* `private f : A` (a field of a `structure`): `S.f` is private and `S` is opaque
  elsewhere, as with `private mk ::`; the constructor stays public unless it is
  `private mk ::` too. A class's methods can't be private.
* A type declared `private` (`private inductive T`) is not opaque, but its recursors are
  private, so a value of it that reaches another module (through a public definition)
  isn't matched there either.

All of this is elaboration only, as above: the kernel checks against the full
environment, and whatever the elaborator accepts with `T`'s definition hidden also
checks with it unfolded. The self-hosted frontend parses the `private` markers and
ignores them. The motivating use is the HDL's signals (`drafts/hdl/Signal.wiz`): user
code builds and observes them only through the library's combinators and `sample`
(`drafts/hdl/rejected/observe_signal.wiz`). Tests: group `elabfix`.

## 13g: as-patterns `x@p` ✅

```
def last (A : Type) (d : A) : List A → A
  | .nil => d
  | .cons x .nil => x
  | .cons _ xs@(.cons _ _) => last A d xs     -- `xs` is the tail that was matched
def dup : List Nat → List Nat
  | .nil => .nil
  | l@(.cons x _) => .cons x l
```

`x@p` (no space around the `@`; `p` an atomic pattern, so a constructor with arguments
goes in parentheses) matches `p` and binds `x` to the value that was matched. It may be
nested anywhere a pattern may, on any kind of pattern (`q@(a, b)`, `n@m@(.succ _)`).

`x` is bound exactly as a variable pattern in that position would be (`compileMatch`,
`Elab/Term.lean`): to the scrutinised variable itself, so no constructor is rebuilt,
unless the goal depends on that variable; then it is the constructor applied to the
fields, which is what has the refined type. Because `x` *is* the matched variable, an
as-pattern on a recursive field is structurally smaller: `last A d xs` above is the
induction hypothesis of the tail. (Without the as-pattern one had to write a helper
that takes the head and the tail separately: "recursive call must be on a variable".)

Limits: when the goal depends on the matched variable, `x` is the rebuilt constructor,
and a recursive call on it is not recognised ("not a recursive field"). In a term,
`x@p` is an error ("only allowed in a pattern").

Not solved by as-patterns: recursion over a family at an index that is not a variable.
`Vec.last : Vec A (Nat.succ n) → A` with `| .cons _ xs@(.cons _ _) => Vec.last xs` now
gets as far as the kernel, which rejects it ("expected: n = .succ (.succ n)"): the
induction hypothesis of a definition matched at the index `succ n` is for that same `n`
(the parameters before the colon are fixed), and the tail is a `Vec A n`. `lib/Vec.wiz`
keeps its helper `Vec.lastFrom`, whose index is a variable that the motive generalises.

Syntax: `term.asPat`, a trailing parser at the highest precedence, `x "@" p` with no
whitespace on either side of the `@`. Explicit application is unchanged, `f @g` and
also `f@g`: where both readings are as long, the application wins, so an as-pattern
whose pattern is a bare name (`x@y`, a second name for the same value) is not available;
`x@_` and `x@(y)` are. Tests: `language` ("as-patterns …"),
`parser: terms`.

## 13h: patterns on structures, `⟨…⟩` ✅

```
structure Stats where
  hits : Nat
  misses : Nat
def total (s : Stats) : Nat := match s with
  | .mk h m => Nat.add h m                 -- also `Stats.mk h m` and `⟨h, m⟩`
def total' (s : Stats) : Nat :=
  let ⟨h, m⟩ := s                           -- or `let (.mk h m) := s`
  Nat.add h m
def stats : Stats := ⟨3, 4⟩                 -- `Stats.mk 3 4`, from the expected type
```

A structure is a Σ type, not a data type, so there is no eliminator to split it with
("cannot match on a value of type Nat × Nat × …" before). A constructor pattern on a
scrutinee whose type is a structure `S` (`.mk p…`, `S.mk p…` or `⟨p…⟩`) is now
rewritten to the **tuple pattern** over the components of `S`'s Σ, which binds every
field as a projection of the scrutinee (`let h := s.1; let m := s.2.1; …`); the
sub-patterns are ordinary patterns, so structure patterns nest in constructor and tuple
patterns and the other way round, and mix with as-patterns.

**One place knows the encoding.** How the Σ of a structure is laid out (which
component is which field, and which are not fields at all: today the tail
`(0 fields✝ : …) → Unit` after the last field, 22i) is read from the declaration by
`structLayout?` (`Elab/Struct.lean`), as a list of components, each a field or a marker;
structure patterns, the pattern `let` and structure update (13i) go through it and
nothing else there looks at the Σ. It classifies the components by what the
declaration says (a Σ binder with a phantom name is a marker, the final component is a
field exactly if `S.mk` has a field left for it), so moving the marker to a 0-quantity
component before the last field needs no change here; any other re-encoding is a change
to that one function.

The anonymous constructor `⟨e₁, …, eₙ⟩` is new syntax (`term.anon`), as a term and as a
pattern. Against a structure it is `S.mk e₁ … eₙ`; against a pair, the tuple
`(e₁, …, eₙ)`; against a data type with exactly one constructor, that constructor. It
needs an expected type ("cannot infer the type of an anonymous constructor").

`let pat := e; body` with `pat` an anonymous constructor or any pattern in parentheses
(`term.letPat`) is `match e with | pat => body`, so it also works without an expected
type.

**Linear structures.** A `match` is a case at ω and projections need an unrestricted
pair, so neither takes apart a structure held at quantity 1. With a quantity,
`let 1 ⟨a, b⟩ := s; body` (or `let 1 (.mk a b) := s`) therefore elaborates to nested
splits at that quantity, one per component of the layout, as `let 1 (a, b, c) := t`
does for a tuple (and `let 1 ⟨a, b, c⟩ := t` is accepted on a tuple too); the components
are then names or `_`, and the form is check-mode only. **Today this is rejected for
every structure**: the Σ ends in the marker tail, which is not a field, and the last
split would bind it at quantity 1 and never use it. The elaborator reports that itself
("cannot take a value of the structure Stats apart at quantity 1: the Σ type of a
structure ends in a component that is not a field …") instead of leaving it to the
kernel's usage count. The check is on the layout (a marker that the Σ does not bind at
quantity 0), so once the marker is an erased component the same `let` goes through with
no change here. At quantity ω (`let ω ⟨a, b⟩ := s`) the splits are accepted today.

A structure whose constructor or fields are private to another module (13b) is opaque
there and can't be matched or taken apart ("its constructor is private to module M").

Tests: `language` ("structure patterns …", "anonymous constructors …", "let with a
structure pattern …"), `parser: terms`.
