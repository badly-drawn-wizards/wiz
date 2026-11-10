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

## 13c: `if`, `&&`, `||`, `!` in the Prelude ✅

```
import Prelude
def clamp (n : Nat) : Nat := if Nat.lt n 10 then n else 10
#eval Nat.beq 1 1 && !(Nat.beq 2 3) || Bool.false    -- .true
```

`lib/Prelude.wiz` now declares `if c then a else b` (a macro for
`match c with | .true => a | .false => b`), and `a && b`, `a || b` as macros for
`match a with | .true => b | .false => .false` and `match a with | .true => .true | .false => b`,
so both **short-circuit**: compiled code (and `#eval`) evaluates `b` only when `a` doesn't
decide. `!b` is `Bool.not b`. Precedences are Lean's: `if` is a leading term like `match`,
`||` 30, `&&` 35 (right-associative), `!` binds tightest. The kernel sees the `match`, so
`Bool.true && b` reduces to `b`, as `Bool.and Bool.true b` does, but a stuck `a && b` is a
`match` on `a` and not convertible to `Bool.and a b` (state lemmas about `Bool.and` by
cases on `a`). `if`, `then` and `else` are now reserved words in every program; `not` is
not (constructors and class fields named `not` exist in `lib/Hdl`).

The self-hosted frontend doesn't read `lib/Prelude.wiz`: it embeds its own prelude
(`preludeText`, selfhost/Frontend.wiz) and has had `if` since 19a (an application of `if`,
rewritten to a `match`). It has no `&&`, `||` or `!`, so `selfhost/*.wiz` don't use them.
Tests: group `language`.

## 13d: `Functor` and `Applicative` (`import Functor`) ✅

```
import Functor
#eval Nat.add <$> Option.some 1 <*> Option.some 2          -- .some 3
#eval (fun (a b : Nat) => (a, b)) <$> List.cons 1 (List.cons 2 .nil) <*> List.cons 3 .nil
                                        -- .cons (1, 3) (.cons (2, 3) .nil)
def both : IO (String × String) := (fun (a b : String) => (a, b)) <$> IO.readFile "a" <*> IO.readFile "b"
```

`lib/Functor.wiz` has `class Functor f` (`map`), `class Applicative f` (`pure`, `seq`),
`f <$> x` (`Functor.map`, infixr 100) and `mf <*> x` (`Applicative.seq`, infixl 60), as in
Lean. Two generic instances make **every `Monad` an `Applicative`** (`seq` by two binds)
and **every `Applicative` a `Functor`** (`map g x = pure g <*> x`), so `IO`, `Eff r`,
`Eff1 ω r R`, `StateT`, `ReaderT`, `TacticM` and user monads get `<$>`/`<*>` with no more
declarations. The module also gives `Monad` instances for `Option`, `Except E` and `List`
(nondeterminism: `<*>` takes every combination), with direct `Functor` instances
(`Option.map`, `Except.map`, `List.map`). An instance declared later wins over the
generic ones (7b), which is how a type that isn't a monad (an HDL signal) declares its own
`Applicative`.

`Monad` itself is unchanged (it doesn't extend `Applicative`: classes have no `extends`
yet), so `do`, `Monad1` and `do1` are as before. The module is separate from the Prelude
because programs that import only the Prelude already define `List.map`, a class
`Functor` and `Monad Option` instances of their own (`lib/Hdl/Core.wiz`, the tests).
Tests: group `language`.

