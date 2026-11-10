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
def kernelOpts : Opts := { sortsOptional := true, kernelEqFormation := true, payload := .kernel }

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

/-! ## The cases -/

open Tests.Elab.MTm

def kernelAccepts (t : MTm) (g : Globals ZeroOneMany := leanGlobals ()) : Bool :=
  (infer (R := ZeroOneMany) { globals := g } t.toTerm).isOk

/-- The reference checker's verdict on a term: `ok`, `fuel`, `outside`, or the rejection. -/
def refVerdict (t : MTm) (opts : Opts := kernelOpts) (sg : Option Sig := none) : String :=
  match sg.map Except.ok |>.getD (refSig opts) with
  | .error e => s!"signature: {e}"
  | .ok sg =>
    match WizMeta.ofTerm [] t.toTerm with
    | none => "outside"
    | some tm =>
      match WizMeta.inferClosed sg tm opts with
      | .ok _ => "ok"
      | .error .fuel => "fuel"
      | .error (.fail m) => s!"rejected: {m}"

def accepts (t : MTm) (opts : Opts := kernelOpts) (sg : Option Sig := none) : IO Unit :=
  checkEq "ok" (refVerdict t opts sg)
def rejects (t : MTm) (opts : Opts := kernelOpts) (sg : Option Sig := none) : IO Unit :=
  check ((refVerdict t opts sg).startsWith "rejected") s!"expected a rejection, got {refVerdict t opts sg}: {t.pretty 0}"

/-- A term in an erased position (the argument of a `0`-binder), so that the kernel's
usage check does not get in the way of what is being probed. -/
def erased (t T : MTm) : MTm := app (ann (lam star) (piq .zero T (unit 0))) (ann t T)

/-- A level of the differential test, in the spec's syntax (`u`, `v` are parameters 0, 1). -/
def ofMLvl (l : Tests.Elab.MLvl) : WizMeta.Lvl := (WizMeta.ofLevel ["u", "v"] l.toLevel).getD 0

-- audit W1: a constant at two universe instances
def w1Decl : Decl ZeroOneMany :=
  { name := "d", levelParams := ["u"], type := prop.toTerm,
    value := some (pi (sortParam "u") (pi (var 0) (pi (var 1) (pi (pi (var 2) prop) (pi (app (var 0) (var 2)) (app (var 1) (var 2))))))).toTerm }
def w1 (a b : Nat) : MTm :=
  ann (lam (lam (var 0))) (pi (enum 1) (pi (ecase prop (var 0) [const "d" [a]]) (ecase prop (var 1) [const "d" [b]])))

-- model-memo E5b: a payload equation at a field whose type is a variable
def wrapTy (A : MTm) : MTm := mu 0 (unit 0) (darg A (lam (dret star))) star
def wrap (A a : MTm) : MTm := ann (con (pair a (pair star star))) (wrapTy A)
def e5bTy : MTm :=
  pi (univ 0) (pi (var 0) (pi (var 1) (pi (eq (wrapTy (var 2)) (wrap (var 2) (var 1)) (wrap (var 2) (var 0))) (eq (var 3) (var 2) (var 1)))))
def e5b : MTm := erased (lam (lam (lam (lam (fst (var 0)))))) e5bTy

-- model-memo T4: an equation between two Π types whose domains are in different universes
def crossLevel : MTm :=
  let A1 := sorted 1 (pi pfalse (enum 2))
  let A2 := sorted 2 (pi pfalse (univ 0))
  let no := lam (exfalso pfalse (var 0))
  erased (pair (pair (pair no no) no) (lam star)) (eqTy (sorted 2 (pi A1 (univ 0))) (sorted 2 (pi A2 (univ 0))))

def group : Group where
  name := "meta"
  exercise := "WizMeta (metatheory-plan M1c): the reference checker"
  cases := [
    { name := "the reference checker agrees with the Lean kernel on the differential test's terms (samples + 400 generated)", run := fun _ => do
        match tally (diffTerms 400) with
        | .error e => throw (IO.userError e)
        | .ok t =>
          IO.println s!"    {t.summary}"
          unless t.disagree.isEmpty do
            throw (IO.userError ("\n".intercalate (t.disagree.map fun (i, w, tm) => s!"#{i}: {w}\n    {tm}")))
          check (t.fuel == 0) "a term ran out of fuel"
          check (t.accept ≥ 200) s!"too few accepted terms: {t.accept}"
          check (t.reject ≥ 100) s!"too few rejected terms: {t.reject}"
          check (t.acceptUncompared ≤ 10) s!"too many types not compared: {t.acceptUncompared}" },
    { name := "the same with the levelled rule for Π ≡ Π (the corpus does not tell the variants apart)", run := fun _ => do
        match tally (diffTerms 400) { kernelOpts with eqTyLevelled := true } with
        | .error e => throw (IO.userError e)
        | .ok t =>
          unless t.disagree.isEmpty do
            throw (IO.userError ("\n".intercalate (t.disagree.map fun (i, w, tm) => s!"#{i}: {w}\n    {tm}"))) },
    { name := "declarations at symbolic levels: the reference checker agrees with the Lean kernel (216)", run := fun _ => do
        let sg ← match refSig with | .ok sg => pure sg | .error e => throw (IO.userError e)
        let decls := MTm.declSamples ++ MTm.levelPuzzles 200
        let mut oks := 0
        for d in decls do
          let (ps, v, ty) := d
          let k := Tests.Elab.leanDeclVerdict d
          let r := match WizMeta.ofDecl { name := "test", levelParams := ps, type := ty.toTerm, value := v.map MTm.toTerm } with
            | none => "outside"
            | some dd => match WizMeta.addDecl sg dd kernelOpts with
              | .ok _ => "ok"
              | .error .fuel => "fuel"
              | .error _ => "error"
          unless k == r do
            throw (IO.userError s!"kernel {k}, reference checker {r}: {ty.pretty 0} := {v.map (·.pretty 0)}")
          if k == "ok" then oks := oks + 1
        check (oks ≥ 60 && decls.length - oks ≥ 30) s!"unbalanced: {oks} of {decls.length} accepted" },
    { name := "levels: the decision procedure agrees with evaluation (generated pairs, parameters in 0..3)", run := fun _ => do
        let mut s := 11
        let mut equal := 0
        for _ in [0:600] do
          let (a, s1) := Tests.Elab.MLvl.gen s 2
          let (b, s2) := if s1 % 3 == 0 then Tests.Elab.MLvl.rewrite s1 a else Tests.Elab.MLvl.gen s1 2
          s := s2
          let (a, b) := (ofMLvl a, ofMLvl b)
          let grid := (List.range 4).flatMap fun x => (List.range 4).map fun y => (fun i => if i == 0 then x else y : Nat → Nat)
          let same := grid.all fun ρ => a.eval ρ == b.eval ρ
          unless a.equiv b == same do throw (IO.userError s!"equiv {a.pretty} {b.pretty}: {a.equiv b}, by evaluation {same}")
          unless a.neverZero == grid.all (fun ρ => a.eval ρ != 0) do throw (IO.userError s!"neverZero {a.pretty}")
          unless a.isZero == grid.all (fun ρ => a.eval ρ == 0) do throw (IO.userError s!"isZero {a.pretty}")
          if same then equal := equal + 1
        check (equal ≥ 100 && equal ≤ 500) s!"unbalanced: {equal} of 600 equal" },
    { name := "the spec's own rules: a Π/Σ carries its sort, and it is checked", run := fun _ => do
        let spec : Opts := {}
        rejects (ann (lam (lam (var 0))) (pi (univ 0) (pi (var 0) (var 1)))) spec (some [])
        accepts (ann (lam (lam (var 0))) (sorted 2 (pi (univ 0) (sorted 1 (pi (var 0) (var 1)))))) spec (some [])
        rejects (ann (lam (lam (var 0))) (sorted 1 (pi (univ 0) (sorted 1 (pi (var 0) (var 1)))))) spec (some [])
        -- impredicativity: a Π into Prop is in Prop
        accepts (sorted 0 (pi (univ 0) ptrue)) spec (some [])
        rejects (sorted 2 (pi (univ 0) ptrue)) spec (some [])
        accepts (sorted 2 (sigma (univ 0) ptrue)) spec (some []) },
    { name := "the spec's own rules: equations are formed at every sort, and are True at a proposition", run := fun _ => do
        let spec : Opts := {}
        let eqP := eq ptrue star star
        rejects eqP
        check (!kernelAccepts eqP) "the kernel forms an equation at a proposition"
        accepts eqP spec (some [])
        accepts (ann star eqP) spec (some [])
        -- between a proposition and a type that is not one: formed in the spec, and False
        rejects (eqTy ptrue (enum 2))
        accepts (ann (lam (var 0)) (sorted 0 (pi (eqTy ptrue (enum 2)) pfalse))) spec (some []) },
    { name := "T0 against T1: a cast between convertible inert types is its argument only with InReg", run := fun _ => do
        let nat := const "Nat"
        let t := ann (lam (lam (refl nat (var 0)))) (pi (eqTy nat nat) (pi nat (eq nat (cast nat nat (var 1) (var 0)) (var 0))))
        accepts t
        rejects t { kernelOpts with inertReg := false }
        -- a non-inert type (a function type): the cast computes structurally instead; no rule identifies
        -- a cast at a neutral type with its argument
        let v := ann (lam (lam (lam (refl (var 2) (var 0))))) (pi (univ 0) (pi (eqTy (var 0) (var 0)) (pi (var 1) (eq (var 2) (cast (var 2) (var 2) (var 1) (var 0)) (var 0)))))
        rejects v
        check (!kernelAccepts v) "the kernel has regularity at a type variable" },
    { name := "the level premise of ind (audit F3): the index type is in Sort (l+1)", run := fun _ => do
        let bad := ann (lam (ind 1 (unit 0) (ann (dret star) (desc 1 (unit 0))) 0 (lam (lam (enum 2))) (lam (lam (lam (tag 2 0)))) star (var 0))) (pi (univ 0) (enum 2))
        rejects bad
        rejects (desc 1 (unit 0))
        accepts (desc 0 (unit 0)) },
    { name := "audit probes in the fragment: K6 (a variable out of scope), Y4 (a name declared twice), W1 (a constant at two levels)", run := fun _ => do
        -- K6: the Lean kernel on master types an out-of-scope variable as Prop : Prop (not run here: it panics)
        rejects (var 0)
        rejects (ann (var 3) (var 3))
        rejects (ann (lam (var 1)) (pi (univ 0) (univ 0)))
        let sg ← match refSig with | .ok sg => pure sg | .error e => throw (IO.userError e)
        let some d := WizMeta.ofDecl w1Decl | throw (IO.userError "d is outside the fragment")
        let sg1 ← match WizMeta.addDecl sg d kernelOpts with | .ok sg => pure sg | .error e => throw (IO.userError s!"d: {e}")
        -- Y4
        check (match WizMeta.addDecl sg1 d kernelOpts with | .error (.fail m) => has m "already declared" | _ => false)
          "a second declaration of a name is accepted"
        -- W1: `d.{0}` and `d.{1}` under a stuck case are different
        rejects (w1 0 1) kernelOpts (some sg1)
        accepts (w1 1 1) kernelOpts (some sg1)
        let g1 ← match addDecl (leanGlobals ()) w1Decl with | .ok g => pure g | .error e => throw (IO.userError s!"{e}")
        check (!kernelAccepts (w1 0 1) g1 && kernelAccepts (w1 1 1) g1) "the Lean kernel's verdicts on W1 changed" },
    { name := "E5b: a payload equation at a neutral field type, in the three variants (the kernels' rule is not stable under substitution)", run := fun _ => do
        let stuck := { kernelOpts with payload := .stuck }
        let uniform := { kernelOpts with payload := .uniform }
        -- the instance of `e5b` at `A := Enum 2`, `a = b = #0`, and `e5b` applied to them
        let two := enum 2
        let inst := erased (lam (fst (var 0))) (pi (eq (wrapTy two) (wrap two (tag 2 0)) (wrap two (tag 2 0))) (eq two (tag 2 0) (tag 2 0)))
        -- the kernels' rule: the generic term is accepted and its instance is not
        accepts e5b
        rejects inst
        check (kernelAccepts e5b && !kernelAccepts inst) "the Lean kernel's verdicts on E5b changed: update the note"
        -- stuck at a neutral field type: the generic term is rejected
        rejects e5b stuck
        rejects inst stuck
        -- no shortcut: both accepted
        accepts e5b uniform
        accepts inst uniform
        -- at a canonical field type that is not a tag type, all three take the Σ rule
        let F := pi (enum 2) (enum 2)
        let idf := ann (lam (var 0)) F
        let t := erased (lam (fst (var 0))) (pi (eq (wrapTy F) (wrap F idf) (wrap F idf)) (eq F idf idf))
        accepts t
        accepts t stuck
        accepts t uniform
        check (kernelAccepts t) "the kernel rejects the Σ rule at a canonical field" },
    { name := "T4: an equation between Π types with domains in different universes (accepted by the kernels' rule, stuck with the levelled one)", run := fun _ => do
        accepts crossLevel
        rejects crossLevel { kernelOpts with eqTyLevelled := true }
        check (kernelAccepts crossLevel) "the Lean kernel no longer decomposes across levels: update the note" }
  ]

def groups : List Group :=
  group ::
  []

end Tests.Meta
