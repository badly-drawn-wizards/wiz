# Stage 10: effects

## 10a: effects as a library, commutation as proofs ✅

```
import Eff
def prog : Eff (Row.cons (State Nat) (Row.cons (Exn String) (Row.cons Console Row.nil))) Nat := do
  n ← get;
  println "starting";
  put (n + 1);
  Monad.pure n
def main : IO Unit := do
  r ← runConsole (runExn (runState prog 4))
  …
```

* `lib/Eff.wiz`: an `Effect` is a type of operations with an answer type for each, a
  `Row` lists effects, and `Eff r A` is a free monad over the row's operations (its
  continuations are infinitary fields). `Member e r` (two instances, found by
  resolution) injects an effect's operations into a row; `send` performs one.
* Handlers peel the first effect off a row: `runState`, `runReader`, `runExn`, and
  `runConsole` into `IO` at the bottom.
* **Lowering to a monad**: a `Handler e m` for every effect of a row gives
  `interpret : Eff r A → m A`. **Commutation is a proof obligation**:
  `Commute e₁ e₂ m` asks for a proof (kernel-checked, with the OTT equality) that
  swapping two operations doesn't change the result in `m`; `reorder` needs it. Two
  readers commute (the proof is `rfl`); the kernel rejects the same claim for state.
* This needed more of the elaborator: dependent matching now carries induction
  hypotheses through nested patterns; unification got lazy delta (unfold the later
  definition one step), first-order approximation against variables, projections of
  holes, and non-linear spines; description fields may live in smaller universes;
  `Type` takes a universe argument only right of the enclosing position; types get
  their trailing instance arguments.

## 10b: fusion ✅

Effectful code can be written against classes (`MonadState S m`, `MonadReader E m`,
`MonadConsole m`) and run two ways: as a tree of operations (`Eff r`, whose instances
`send` operations to handlers, so resumptions are general), or **fused**, directly in
a monad (`StateT S IO`, `ReaderT E IO`, `IO`), where every operation is a plain call
and no tree is built. In a 200,000-step state loop the fused version is about 4.5×
faster.

```
def prog {m : Type → Type} [Monad m] [MonadState Nat m] [MonadConsole m] : m Nat := …
runConsole (runState (prog : Eff (Row.cons (State Nat) (Row.cons Console Row.nil)) Nat) 0)   -- tree
(prog : StateT Nat IO Nat) 0                                                                 -- fused
```
