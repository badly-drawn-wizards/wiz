import STC.F0.Sort
import STC.F0.Syntax
import STC.F0.Reducts
import STC.F0.Spec.Fragments
import STC.F0.Laws
import STC.F0.Renaming
import STC.F0.Substitution
import STC.F0.WhRed
import STC.F0.Obligations
import STC.F0.Sorting
import STC.F0.Sanity

/-!
# STC: the F0 specification of the STC track

M0.1 of the design note `/workspace/wiz-notes/stc-m0-spec.md`:

* `F0/Sort`, `F0/Syntax`: the closed three sorts and the F0 terms (`letUnit` included);
* `F0/Spec/`: the four judgments and the rules as data, one file per former; `F0` is
  Core, Π, Σ, Unit, Empty, Enum, let, globals, Eq, **levelled** Eq-Π/Eq-Σ and ULift;
* `F0/Laws`: the renaming/substitution calculus on terms;
* `F0/Renaming`: the renaming lemma for F0 (the first law, proved);
* `F0/Substitution`: the substitution lemma for F0 (the second law, proved), with
  context validity (`F0_ctx`) and the `ty`/`eq`/`red`/`wf` companions;
* `F0/WhRed`: `WhRed` empty at propositions, modulo the sorting lemma `SortUniqueAt`;
* `F0/Sorting`: `SortUniqueAt` reduced to `TyUnique` + `ConvInjSort`, with the exact gap
  (the `trans` case needs normalisation/confluence, not a rule) written down;
* `F0/Obligations`: `Sound(F0)`, `Con(F0)`, `WHN`, `DecConv`, `DecTC` as `Prop`s, and the
  sorting lemma's supporting statements (`TyUnique`, `ConvInj*`);
* `F0/Sanity`: small derivations that witness that the rules are inhabited.

Not a default Lake target; nothing imports it yet. The implementation note is
`/workspace/wiz-notes/stc-m0-impl.md`.
-/
