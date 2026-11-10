import WizMeta.Level
import WizMeta.Syntax
import WizMeta.Templates
import WizMeta.Reducts
import WizMeta.Spec.Fragments
import WizMeta.Checker
import WizMeta.Translate

/-!
# WizMeta: a declarative spec of the Wiz core theory, and a reference checker

Milestone M1c of the metatheory plan. Design, the differences from the kernels, and
what is not done: `/workspace/wiz-notes/wiz-meta.md`.

* `Syntax`, `Level`: the spec's own terms and levels.
* `Spec/`: the rules, one file per former; `Spec/Fragments.lean`: T0, T1, Tprog.
* `Reducts`, `Templates`: the terms the rules build, shared by rules and checker.
* `Checker`: the reference checker. Total; unverified.
* `Translate`: from `Wiz.Term`; fails outside the fragment.

Not a default Lake target: only `Tests/Meta.lean` imports it.
-/
