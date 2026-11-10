import WizMeta
import Tests.Elab

/-!
# The reference checker of `WizMeta` as a third voter

`WizMeta/Checker.lean` is a small checker written from the spec's rules
(`WizMeta/Spec/`). Here it votes on the terms of the differential test
(`Tests/Elab.lean`, "the Wiz kernel agrees with the Lean kernel"): the same samples and
the same 400 generated terms. That case compares `Kernel.wiz` with the Lean kernel; this
group compares the reference checker with the Lean kernel, in process, on the terms that
are in its fragment.
-/

open Wiz

namespace Tests.Meta
open Tests.Elab (MTm leanGlobals)
open WizMeta (Tm Lvl Sig Opts Err)

/-- The rules as today's kernels have them, where the spec differs on purpose: a `Π`/`Σ`
may come without its sort, and equations are formed only above `Prop`. -/
def kernelOpts : Opts := { sortsOptional := true, eqNeverZero := true }

def has (s pat : String) : Bool := (s.splitOn pat).length > 1

/-- The globals of the differential test, in the reference checker. -/
def refSig (opts : Opts := kernelOpts) : Except String Sig :=
  MTm.globalDefs.foldlM (init := []) fun sg (n, ps, v, ty) => do
    let some d := WizMeta.ofDecl { name := n, levelParams := ps, type := ty.toTerm, value := v.map MTm.toTerm }
      | throw s!"global {n} is outside the fragment"
    match WizMeta.addDecl sg d opts with
    | .ok sg => pure sg
    | .error e => throw s!"global {n}: {e}"

inductive Outcome where
  /-- the term is outside the fragment: no vote -/
  | outside
  /-- both accept, and the reference checker finds the two types convertible -/
  | accept
  /-- both accept; the kernel's type is outside the fragment, so it was not compared -/
  | acceptUncompared
  | reject
  /-- the kernel rejects for a usage (quantity) reason, which the reference checker does
  not look at, and the reference checker accepts -/
  | usage
  | fuel
  | disagree (what : String)
  deriving Repr, BEq

/-- One term: the Lean kernel's verdict against the reference checker's. -/
def vote (g : Globals ZeroOneMany) (sg : Sig) (t : MTm) (opts : Opts := kernelOpts) : Outcome :=
  match WizMeta.ofTerm [] t.toTerm with
  | none => .outside
  | some tm =>
    let k := infer (R := ZeroOneMany) { globals := g } t.toTerm
    let r := WizMeta.inferClosed sg tm opts
    match k, r with
    | _, .error .fuel => .fuel
    | .ok (ty, _), .ok T =>
      match WizMeta.ofTerm [] (quote g 0 ty) with
      | none => .acceptUncompared
      | some kT =>
        match WizMeta.convTy { sig := sg, opts } WizMeta.defaultFuel [] T kT with
        | .ok true => .accept
        | .ok false => .disagree "both accept, with types that are not convertible"
        | .error .fuel => .fuel
        | .error (.fail m) => .disagree s!"both accept; comparing the types failed: {m}"
    | .ok _, .error (.fail m) => .disagree s!"the kernel accepts, the reference checker rejects: {m}"
    | .error e, .ok _ =>
      let m := toString e
      if has m "declared with quantity" || has m "cannot project the field" || has m "cannot discard" then .usage
      else .disagree s!"the reference checker accepts, the kernel rejects: {m}"
    | .error _, .error (.fail _) => .reject

/-- The terms of the differential test (`Tests/Elab.lean`): the samples, then 400
generated ones. Keep in step with that case. -/
def diffTerms (n : Nat := 400) : Array MTm := Id.run do
  let mut terms : Array MTm := MTm.samples.toArray
  let mut seed := 42
  for i in [0:n] do
    let (t, s) := MTm.gen seed (2 + i % 3) 0
    terms := terms.push t
    seed := s
  terms

structure Tally where
  outside : Nat := 0
  accept : Nat := 0
  acceptUncompared : Nat := 0
  reject : Nat := 0
  usage : Nat := 0
  fuel : Nat := 0
  disagree : List (Nat × String × String) := []

def Tally.summary (t : Tally) : String :=
  s!"accept {t.accept} (+{t.acceptUncompared} with the type not compared), reject {t.reject}, " ++
  s!"usage-only {t.usage}, out of fuel {t.fuel}, outside the fragment {t.outside}, disagree {t.disagree.length}"

def tally (terms : Array MTm) (opts : Opts := kernelOpts) : Except String Tally := do
  let sg ← refSig opts
  let g := leanGlobals ()
  let mut t : Tally := {}
  let mut i := 0
  for tm in terms do
    match vote g sg tm opts with
    | .outside => t := { t with outside := t.outside + 1 }
    | .accept => t := { t with accept := t.accept + 1 }
    | .acceptUncompared => t := { t with acceptUncompared := t.acceptUncompared + 1 }
    | .reject => t := { t with reject := t.reject + 1 }
    | .usage => t := { t with usage := t.usage + 1 }
    | .fuel => t := { t with fuel := t.fuel + 1 }
    | .disagree w => t := { t with disagree := t.disagree ++ [(i, w, tm.pretty 0)] }
    i := i + 1
  pure t

end Tests.Meta
