import Wiz.Elab.Term

/-!
# `inductive` and `structure`

```
inductive Vec (A : Type) : Nat → Type where
  | nil : Vec A .zero
  | cons {0 n : Nat} (x : A) (xs : Vec A n) : Vec A (.succ n)
```

elaborates to ordinary declarations, all checked by the kernel:

* `Vec.desc : (A : Type) → Desc ((n : Nat) × Unit)`: the description, with a tag
  per constructor;
* `Vec : (A : Type) → Nat → Type := fun A n => μ (Vec.desc A) (n, ())`: the nominal
  wrapper, with a display hint so that it prints as `Vec A n`;
* `Vec.nil`, `Vec.cons`: constructors, `con ('cons, n, x, xs, refl …, ())`.

Indices are packed into a Σ ending in `Unit`. Constructor fields are elaborated with
the type itself bound as a *local variable* `T : (indices) → Type l`. A field whose
type is `T j` becomes `Desc.rec`, any other field becomes `Desc.arg`, and the return
type `T j` becomes `Desc.ret j`. Since `T` may occur nowhere else, positivity holds
by construction. Later fields may not depend on recursive ones: `Desc.rec` fields are
non-dependent.

`structure S where x : A; y : B` is `(x : A) × (y : B) × Unit`, with constructor
`S.mk`. Field access `p.x` comes from the Σ binder names.
-/

namespace Wiz.Elab

variable {R : Type} [QRig R] [DecidableEq R] [QuantitySyntax R]

/-- Elaborate binders into a context, returning the context and the binders as
`(name, binder info, quantity, type)`. -/
def elabTelescope (ctx : LocalCtx R) (bs : List BinderView) :
    ElabM R (LocalCtx R × Array (Name × BinderInfo × Term R × Term R)) := do
  let mut ctx := ctx
  let mut tele := #[]
  for b in bs do
    let ty ← match b.type with
      | some s => pure (← checkType ctx s).1
      | none => freshMeta ctx s!"the type of {b.name}"
    let q ← elabQuantity ctx b.bi b.qty
    tele := tele.push (b.name, b.bi, q, ty)
    ctx := ctx.bind b.name (← evalIn ctx ty)
  pure (ctx, tele)

/-- `(a₁, (a₂, …, ()))` -/
def tupleTm (as : List (Term R)) : Term R := as.foldr .pair .tt

def lamsTm (xs : List Name) (b : Term R) : Term R := xs.foldr .lam b

/-- `T`'s arguments at a position where `T` is `var k`: the first `nΔ` must be the
parameters themselves (`var (k + nΔ - j)` for the `j`-th); returns the rest. -/
def paramArgs? (nΔ k : Nat) (args : List (Term R)) : Option (List (Term R)) :=
  if (args.take nΔ) == (List.range nΔ).map (fun j => .var (k + nΔ - j)) then some (args.drop nΔ)
  else none

/-- **Exercise 4.21.** The description of one constructor.

`fields[k] = (name, quantity, type)`, where the type lives in the context
`[f_{k-1}, …, f₀, T, Δ…]` (innermost first, so `T` is `var k`). `target` is the list
of index arguments of the return type, in the context `[f_{n-1}, …, f₀, T, Δ…]`.
Inside its declaration, `T` is applied to the `nΔ` parameters first (`Vec A n`), and
those must be exactly the parameter variables: use `paramArgs? k args` to strip them.
Build the description from the end:

* start with `Desc.ret (tupleTm target)`, in the context with all fields;
* for field `k` (from last to first) with type `F`:
  - if `F` is `T` applied to arguments (`Term.spine` with head `.var k`), strip the
    parameters and produce `Desc.rec q (tupleTm indices) D`. `D` was built *under*
    `f_k`, so remove it with `strengthen? 0`. If that fails, a later field depends on a
    recursive one: error;
  - otherwise produce `Desc.arg q F (.lam name D)`.
* Finally remove `T` itself (`strengthen? 0`). If it still occurs, it was used in a
  non-recursive position: error.

The result lives in the parameter context `Δ`. -/
def ctorDesc (nΔ : Nat) (fields : List (Name × Term R × Term R)) (target : List (Term R)) :
    Except String (Term R) := do
  --<sol
  let n := fields.length
  let mut D : Term R := .dret (tupleTm target)
  for (name, q, F) in fields.reverse, k in (List.range n).reverse do
    match F.spine with
    | (.var i, args) =>
      if i == k then
        let some D' := D.strengthen? 0
          | throw s!"a field may not depend on the recursive field {name}"
        let some js := paramArgs? nΔ k args
          | throw s!"the recursive field {name} must use the same parameters"
        D := .drec q (tupleTm js) D'
      else D := .darg q F (.lam name D)
    | _ => D := .darg q F (.lam name D)
  match D.strengthen? 0 with
  | some D' => pure D'
  | none => throw "the type being defined may only occur as the type of a field or the result"
  --|ex
  --| sorry
  --sol>

/-- Peel a type signature `(ξ₁ : X₁) → … → Type l` into indices and `l`. -/
def peelSignature : Term R → Except String (List (Name × BinderInfo × Term R × Term R) × Level)
  | .pi x bi q X B => do
    let (xs, l) ← peelSignature B
    pure ((x, bi, q, X) :: xs, l)
  | .sort l => match l with
    | .succ l => pure ([], l)
    | l => match l.toNat? with
      | some (n + 1) => pure ([], Level.ofNat n)
      | some 0 => throw "inductive propositions are not supported yet (declare it in Type)"
      | _ => throw s!"the type of an inductive must end in Type u, not Sort {l}"
  | _ => throw "the type of an inductive must be a sequence of arrows ending in Type u"

private def pisTm (bs : List (Name × BinderInfo × Term R × Term R)) (b : Term R) : Term R :=
  bs.foldr (fun (x, bi, q, A) acc => .pi x bi q A acc) b

/-- The variables of an `n`-binder telescope, outermost first, seen from `extra` binders deeper. -/
private def telescopeVars (n extra : Nat) : List (Term R) :=
  (List.range n).map fun j => .var (extra + n - 1 - j)

/-- Elaborate an `inductive` command to its declarations. -/
def elabInductive (cmd : Syntax) (levelParams : List Name) : ElabM R (List (Decl R)) := do
  let T := ((cmd.getArg 1).getId?).getD "_"
  let us := levelParams.map Level.param
  let fail {α} (stx : Syntax) (msg : String) : ElabM R α := throwAt stx.info msg
  -- parameters
  let (ctxΔ, Δ) ← elabTelescope {} ((cmd.getArg 3).args.flatMap binderViews).toList
  let nΔ := Δ.size
  -- signature
  let sig ← match (cmd.getArg 4).args[1]? with
    | some s => pure (← checkType ctxΔ s).1
    | none => pure (.sort 1)
  let sig ← zonk ctxΔ.lvl sig
  let (Ξ, l) ← match peelSignature sig with
    | .ok r => pure r
    | .error e => fail (cmd.getArg 4) e
  let nΞ := Ξ.length
  -- the index type: (ξ₁ : X₁) × … × Unit
  let I : Term R := Ξ.foldr (fun (x, _, q, X) acc => .sigma x q X acc) (.unit (.succ l))
  -- constructors, elaborated with `T` bound locally
  -- inside the declaration `T` takes the parameters too: `T : Δ → Ξ → Type l`
  let ctxT := ctxΔ.bind T (eval (← getGlobals) [] (pisTm Δ.toList sig))
  let ctors := (cmd.getArg 6).args
  let mut names : List Name := []
  let mut descs : List (Term R) := []
  let mut ctorInfo : List (Name × List (Name × BinderInfo × Term R × Term R) × List (Term R)) := []
  for c in ctors do
    let cname := ((c.getArg 1).getId?).getD "_"
    let (ctxF, fs) ← elabTelescope ctxT ((c.getArg 2).args.flatMap binderViews).toList
    let n := fs.size
    let target ← match (c.getArg 3).args[1]? with
      | some s => pure (← checkType ctxF s).1
      | none => pure (.var n)
    -- zonk the fields and the target in their contexts
    let mut fs' := #[]
    for (x, bi, q, A) in fs, k in [0:n] do
      fs' := fs'.push (x, bi, ← zonk (ctxT.lvl + k) q, ← zonk (ctxT.lvl + k) A)
    let target ← zonk ctxF.lvl target
    for (_, _, q, A) in fs' do ensureNoMVars q c.info; ensureNoMVars A c.info
    ensureNoMVars target c.info
    let (head, args) := target.spine
    let some js := paramArgs? nΔ n args
      | fail c s!"constructor {cname} must return {T} applied to its parameters and {nΞ} indices"
    unless head == .var n && js.length == nΞ do
      fail c s!"constructor {cname} must return {T} applied to its parameters and {nΞ} indices"
    let D ← match ctorDesc nΔ (fs'.toList.map fun (x, _, q, A) => (x, q, A)) js with
      | .ok D => pure D
      | .error e => fail c s!"constructor {cname}: {e}"
    names := names ++ [cname]
    descs := descs ++ [D]
    ctorInfo := ctorInfo ++ [(cname, fs'.toList, js)]
  -- the whole description: a tag, then the constructor's description
  let w : Term R := .qlit QuantitySyntax.explicitDefault
  let desc : Term R := .darg w (.enum names)
    (.lam "t" (.ecase "z" ((Term.desc l I).lift 2) (.var 0) (descs.map (·.lift 1))))
  let ΔNames := Δ.toList.map (·.1)
  let ΔBinders := Δ.toList
  let descName := T ++ ".desc"
  let descDecl : Decl R :=
    { name := descName, levelParams := levelParams,
      type := pisTm ΔBinders (.desc l I), value := some (lamsTm ΔNames desc) }
  -- the nominal type
  let ξNames := Ξ.map (·.1)
  let Δvars := telescopeVars nΔ nΞ
  let ξvars := telescopeVars nΞ 0
  let muTm : Term R := .mu l (I.lift nΞ) ((Δvars.foldl .app (.const descName us)))
    (tupleTm ξvars) .szInf (some (T, us, Δvars ++ ξvars))
  let typeDecl : Decl R :=
    { name := T, levelParams := levelParams,
      type := pisTm ΔBinders sig, value := some (lamsTm (ΔNames ++ ξNames) muTm) }
  -- constructors
  let implicitΔ := ΔBinders.map fun (x, _, _, A) => (x, BinderInfo.implicit, (.qlit 0 : Term R), A)
  let mut ctorDecls := []
  for (cname, fs, js) in ctorInfo, tagIx in [0:ctorInfo.length] do
    let n := fs.length
    -- occurrences of the local `T` (already applied to the parameters) become the global
    let Tc : Term R := .const T us
    let fsTy := fs.zipIdx.map fun ((x, bi, q, A), k) => (x, bi, q, A.instantiateAt k Tc)
    let resTy := js.foldl (fun acc j => .app acc (j.instantiateAt n Tc)) ((telescopeVars nΔ n).foldl .app Tc)
    let some js' := js.mapM (·.strengthen? n)
      | fail cmd s!"constructor {cname}: its indices may not mention {T}"
    let fieldVars := telescopeVars n 0
    let payload := Term.pair (.tag names tagIx)
      (fieldVars.foldr .pair (.pair (.refl (I.lift n) (tupleTm js')) .tt))
    let d : Decl R :=
      { name := T ++ "." ++ cname, levelParams := levelParams,
        type := pisTm implicitΔ (pisTm fsTy resTy),
        value := some (lamsTm ΔNames (lamsTm (fs.map (·.1)) (.con payload))) }
    ctorDecls := ctorDecls ++ [d]
  pure ([descDecl, typeDecl] ++ ctorDecls)

/-- Elaborate a `coinductive` command: one "constructor" whose fields are the
observations. `T.desc`, `T := ν (T.desc Δ) ()`, and an observation function per field
(`out x` projected). Returns the declarations and the observation names, with
whether each is recursive. Fields may depend on the parameters only. -/
def elabCoinductive (cmd : Syntax) (levelParams : List Name) :
    ElabM R (List (Decl R) × List (Name × Bool)) := do
  let T := ((cmd.getArg 1).getId?).getD "_"
  let us := levelParams.map Level.param
  let (ctxΔ, Δ) ← elabTelescope {} ((cmd.getArg 3).args.flatMap binderViews).toList
  let nΔ := Δ.size
  let sig ← match (cmd.getArg 4).args[1]? with
    | some s => pure (← checkType ctxΔ s).1
    | none => pure (.sort 1)
  let sig ← zonk ctxΔ.lvl sig
  let l ← match peelSignature sig with
    | .ok ([], l) => pure l
    | .ok _ => throwAt (cmd.getArg 4).info "a coinductive type has no indices (yet)"
    | .error e => throwAt (cmd.getArg 4).info e
  let ctxT := ctxΔ.bind T (eval (← getGlobals) [] (pisTm Δ.toList sig))
  let views : List BinderView := (cmd.getArg 6).args.toList.map fun f =>
    { name := ((f.getArg 1).getId?).getD "_", info := f.info, bi := .default,
      qty := (f.getArg 0).args[0]?, type := some (f.getArg 3) }
  let (_, fs) ← elabTelescope ctxT views
  let mut fs' := #[]
  for (x, bi, q, A) in fs, k in [0:fs.size] do
    let q ← zonk (ctxT.lvl + k) q
    let A ← zonk (ctxT.lvl + k) A
    ensureNoMVars q cmd.info; ensureNoMVars A cmd.info
    fs' := fs'.push (x, bi, q, A)
  let D ← match ctorDesc nΔ (fs'.toList.map fun (x, _, q, A) => (x, q, A)) [] with
    | .ok D => pure D
    | .error e => throwAt cmd.info e
  let I : Term R := .unit (.succ l)
  let ΔNames := Δ.toList.map (·.1)
  let descDecl : Decl R :=
    { name := T ++ ".desc", levelParams := levelParams,
      type := pisTm Δ.toList (.desc l I), value := some (lamsTm ΔNames D) }
  let Δvars := telescopeVars nΔ 0
  let nuTm : Term R := .nu l I (Δvars.foldl .app (.const (T ++ ".desc") us)) .tt .szInf (some (T, us, Δvars))
  let typeDecl : Decl R :=
    { name := T, levelParams := levelParams, type := pisTm Δ.toList sig, value := some (lamsTm ΔNames nuTm) }
  -- observations: T.f : {Δ} → T Δ → F, with F not depending on earlier fields
  let implicitΔ := Δ.toList.map fun (x, _, _, A) => (x, BinderInfo.implicit, (.qlit 0 : Term R), A)
  let mut decls := [descDecl, typeDecl]
  let mut obs := []
  for (x, _, _, A) in fs'.toList, k in [0:fs'.size] do
    -- `A` lives in [f_{k-1} … f₀, T, Δ]: drop the fields, then replace `T`
    let mut A' := A
    for _ in [0:k] do
      match A'.strengthen? 0 with
      | some a => A' := a
      | none => throwAt cmd.info s!"the observation {x} may not depend on earlier observations"
    let isRec := match (Term.spine A').1 with
      | .var 0 => true
      | _ => false
    let F := A'.instantiateAt 0 (.const T us)
    let Tapp : Term R := (telescopeVars nΔ 0).foldl .app (.const T us)
    -- (out x).2…2.1 in context [x, Δ]
    let proj : Term R := .fst ((List.range k).foldl (fun t _ => .snd t) (.out (.var 0)))
    let d : Decl R :=
      { name := T ++ "." ++ x, levelParams := levelParams,
        type := pisTm implicitΔ (.pi "x" .default (.qlit QuantitySyntax.explicitDefault) Tapp (F.lift 1)),
        value := some (lamsTm ΔNames (.lam "x" proj)) }
    decls := decls ++ [d]
    obs := obs ++ [(x, isRec)]
  pure (decls, obs)

/-- Elaborate a `structure` command to the Σ type and its constructor `S.mk`. -/
def elabStructure (cmd : Syntax) (levelParams : List Name) : ElabM R (List (Decl R)) := do
  let S := ((cmd.getArg 1).getId?).getD "_"
  let us := levelParams.map Level.param
  let (ctxΔ, Δ) ← elabTelescope {} ((cmd.getArg 3).args.flatMap binderViews).toList
  let sig ← match (cmd.getArg 4).args[1]? with
    | some s => pure (← checkType ctxΔ s).1
    | none => pure (.sort 1)
  let sig ← zonk ctxΔ.lvl sig
  let l ← match peelSignature sig with
    | .ok ([], l) => pure l
    | .ok _ => throwAt (cmd.getArg 4).info "a structure has no indices"
    | .error e => throwAt (cmd.getArg 4).info e
  let views : List BinderView := (cmd.getArg 6).args.toList.map fun f =>
    { name := ((f.getArg 1).getId?).getD "_", info := f.info, bi := .default,
      qty := (f.getArg 0).args[0]?, type := some (f.getArg 3) }
  let (ctxF, fs) ← elabTelescope ctxΔ views
  let mut fs' := #[]
  for (x, bi, q, A) in fs, k in [0:fs.size] do
    let q ← zonk (ctxΔ.lvl + k) q
    let A ← zonk (ctxΔ.lvl + k) A
    ensureNoMVars q cmd.info; ensureNoMVars A cmd.info
    fs' := fs'.push (x, bi, q, A)
  let _ := ctxF
  let body : Term R := fs'.toList.foldr (fun (x, _, q, A) acc => .sigma x q A acc) (.unit (.succ l))
  let ΔNames := Δ.toList.map (·.1)
  let n := fs'.size
  let Sapp : Term R := (telescopeVars Δ.size n).foldl .app (.const S us)
  let implicitΔ := Δ.toList.map fun (x, _, _, A) => (x, BinderInfo.implicit, (.qlit 0 : Term R), A)
  let sDecl : Decl R :=
    { name := S, levelParams := levelParams, type := pisTm Δ.toList sig,
      value := some (lamsTm ΔNames body) }
  let mkDecl : Decl R :=
    { name := S ++ ".mk", levelParams := levelParams, type := pisTm implicitΔ (pisTm fs'.toList Sapp),
      value := some (lamsTm ΔNames (lamsTm (fs'.toList.map (·.1)) (tupleTm (telescopeVars n 0)))) }
  pure [sDecl, mkDecl]

end Wiz.Elab
