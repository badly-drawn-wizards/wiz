# Stage 6: macros

## 6a: macros by example ✅

```
infixl:65 " + " => add
notation "two" => Nat.succ (Nat.succ Nat.zero)
syntax "if" term "then" term "else" term : term
macro_rules
  | `(term| if $c then $t else $e) => `(term| match $c with | .true => $t | .false => $e)
```

* Every syntax category has **antiquotations** `$x`, and every category `c` has a
  **quotation** `` `(c| …) `` as a term (`Builtin.addMetaParsers`, also run for
  `declare_syntax_cat`).
* `macro_rules` match syntax structurally and instantiate templates
  (`Elab/Macro.lean`). `notation` and `infixl`/`infixr`/`infix` register a syntax rule
  and a macro rule together. User command syntax expands too.
* **Hygiene** via macro scopes: identifiers a template introduces become `x✝n`. Locals
  must match exactly, and globals are found with the scope stripped.

| #   | Where              | What                                      |
|-----|--------------------|-------------------------------------------|
| 6.1 | `Elab/Macro.lean`  | `matchPattern`, `instantiate` (hygiene)   |

## 6b: the prelude, literals and procedural macros ✅

```
import Prelude
#eval 100 * 100 * 100 - 1          -- 999999, computed natively
def t : 2 + 2 = 4 := refl 4         -- the kernel computes on literals too

syntax (name := twice) "twice!" term : term
def twiceMacro : Macro := fun stx => do
  e ← MacroM.pure (Syntax.getArg stx 1);
  MacroM.pure `(term| let y := $e; Nat.add y y)
attribute [macro term.twice] twiceMacro
#eval twice! 21                     -- 42
```

* `import M` loads `lib/M.wiz` (and the `-I DIR` roots; `import A.B` is `A/B.wiz`). `lib/Prelude.wiz` defines `Bool`,
  `Nat`, `List`, `Option`, `Char`, `String`, `Except`, `Syntax`, `MacroM`, and `do`
  notation (written as macros).
* `builtin key := name` registers prelude definitions with the kernel and the runtime
  (as Agda's `BUILTIN`): `nat` and its constructors and operations, and `string`.
* **Literals.** A numeral of the registered `Nat` is a kernel literal `natLit n`. It
  unfolds one step at a time (`0 ↦ zero`, `n+1 ↦ succ (natLit n)`, `vNatView`) when an
  eliminator, `conv`, `unify` or `vEq` looks inside it. Registered operations compute
  natively on literals (`vBuiltin?`, `vNatOp`), and otherwise fall back to their
  definitions. The runtime uses native numbers that look like their unary payloads
  when inspected (`RVal.nat`, `natView`). Strings are `String.mk [Char.mk n, …]`, and
  `#eval` prints numbers and strings as literals.
* **Quotations in terms** build `Syntax` values (`elabQuote`): identifiers are marked
  `x✝`, and `$x` refers to a local `x : Syntax`.
* **Procedural macros** are Wiz functions `Syntax → MacroM Syntax`, where
  `MacroM A := Nat → Except String (A × Nat)` (a supply of fresh scopes, plus failure).
  `attribute [macro k] f` registers `f` for node kind `k`. Expanding a node compiles
  the environment, encodes the node as a runtime value, runs `f` in the interpreter,
  and decodes the result (`Elab/ProcMacro.lean`). The `x✝` marks then get this
  expansion's scope.
* Antiquotations win ties within their category; `$x:term` picks the other reading.
  `match` alternatives must line up (`colGe`), so a nested `match` ends where the
  outer one's next alternative starts.

| #   | Where                  | What                                              |
|-----|------------------------|---------------------------------------------------|
| 6.2 | `Elab/Term.lean`       | `elabQuote`: a quotation as a term building `Syntax` |
| 6.3 | `Elab/ProcMacro.lean`  | `decodeSyntax`: a runtime value back to `Syntax`  |

## 6c: tactics in Wiz ✅

**Infinitary inductives.** Descriptions gain `Desc.hrec q H j D`, a field
`(h : H) → μ D (j h)`: one subtree per `h`, as in W-types. `Desc.elim` takes a fifth
method, `interp`/`All`/`hyps`/`map` have the obvious extra case, and `All` now lives in
`Sort (max (l+1) v)`. `inductive` accepts fields like `(k : Nat → Tree)`, the recursor's
hypothesis for them is `(x : Nat) → motive (k x)`, and structural recursion accepts
`f (k n)`. `Level.equiv` now decides `imax` by splitting on parameters. The tactic monad
needs all of this: it is a free monad, whose continuations are infinitary fields.

If you have already done exercises 4.17–4.21 (the templates, `vDelim`, description
checking and `ctorDesc`), add the `hrec` cases.

**Tactics** (`examples/tactics.wiz`):

```
def ap : (A B : Type) → (A → B) → A → B := by
  intro A; intro B; intro f; intro a
  apply f
  assumption
```

* `by tac₁; tac₂ …` (or one tactic per line) makes a hole of the expected type and runs
  the tactics on it. Leftover goals are reported with their hypotheses.
* A tactic is a **Wiz function** `Syntax → TacticM Unit`, registered for a `tactic`
  syntax kind with `attribute [tactic k] f`. Tactic syntax can also be macros
  (`rfl` is `exact rfl`).
* `TacticM A := (A → Tac) → Tac`, where `Tac` is an inductive type of **requests** to
  the elaborator, each with a continuation (an infinitary field). The elaborator
  interprets them (`runTac`): goals (`getGoals`, `setGoals`, `goalType`, `goalHyps`),
  `intro`, `exact`, `elabInfer`, `assign`, `newGoal`, `isDefEq`, `normalize`,
  `instantiate`, `inferType`, `evalTactic`, and `catch` (which backtracks the elaborator
  state). Tactic code itself stays pure and deterministic. Macros use the same monad
  (`MacroM := TacticM`, requesting only `fresh` and `fail`), so `do` notation serves both.
* Terms are reflected as `Expr` (de Bruijn variables, constants, closed sorts, Π, λ,
  application, numerals). Every other kernel form is an **opaque handle** that
  remembers its depth, and nominal types are shown by name (`Vec A n`).
* The prelude's tactics: `intro`, `exact`, `rfl`, `assumption`, `apply`, `try`,
  `first | t | u`, `( t; u )`, `repeat`, `trace`.
* Macro and tactic code is erased once, on first use, and only what is reachable
  from them (`compileReachable`; `#eval` does the same).

Also fixed along the way: `elabMatch` zonks the expected type, and `checkApp` keeps the
written arguments (not the placeholders' normal forms) and solves placeholders
without quoting.

| #   | Where                 | What                                               |
|-----|-----------------------|----------------------------------------------------|
| 6.4 | `Elab/Tactic.lean`    | `reflect` and `reify`: terms ↔ `Expr` with handles |
| 6.5 | `Elab/Term.lean`      | `runTac`: the request loop                         |
| 6.6 | `lib/Prelude.wiz`     | `TacticM.findHyp`, for `assumption` (in Wiz!)      |

Next: typeclasses with tabled resolution (stage 7), which also make `do` generic.
