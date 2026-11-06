import Wiz.Elab.Inductive

/-!
# Recursors

For every `inductive T`, generate the Lean-style dependent eliminators

```
T.rec.{us, v} : {Δ} → (motive : (ξ : Ξ) → T Δ ξ → Sort v)
  → (m_c : (fields of c) → (one hypothesis per recursive field) → motive idx_c (T.c fields))…
  → {ξ : Ξ} → (x : T Δ ξ) → motive ξ x
T.casesOn : the same without hypotheses
```

defined with the kernel's `ind`, and checked by the kernel like everything else.
Pattern matching (stage 4e) compiles to these.

The method for `ind` receives `xs : ⟦D⟧ (μ D) i`, which is a tag paired with the rest
of the payload. It branches on the tag with an `ecase` whose motive generalises the
tag (the "convoy pattern"). In the branch for `c`, the payload is
`(f₁, …, fₙ, e, ())` where `e : idx_c = i` is the constructor's index equation, and
the user's method gives `motive idx_c (T.c fields)`. A `cast` along
`transp … e` moves that to `motive i (con xs)`, since proofs are irrelevant and pairs
have η.

## Building terms

`B R := Nat → Term R` builds a term given the depth (number of enclosing binders).
`blam x fun v => …` binds `v` as a builder for the new variable, so de Bruijn
arithmetic is done once, in `bvar`. Type positions are normalised (`bnf`: evaluate,
then quote) so that template applications are β-reduced before the kernel sees them.
-/

namespace Wiz.Elab

variable {R : Type} [QRig R] [DecidableEq R] [QuantitySyntax R]

abbrev B (R : Type) := Nat → Term R

namespace B

def bvar (lvl : Nat) : B R := fun d => .var (d - lvl - 1)
def closed (t : Term R) : B R := fun _ => t
def app (f : B R) (as : List (B R)) : B R := fun d => as.foldl (fun acc a => .app acc (a d)) (f d)
def lam (x : Name) (body : B R → B R) : B R := fun d => .lam x (body (bvar d) (d + 1))
def pi (x : Name) (bi : BinderInfo) (q : B R) (A : B R) (body : B R → B R) : B R :=
  fun d => .pi x bi (q d) (A d) (body (bvar d) (d + 1))
def fst (t : B R) : B R := fun d => .fst (t d)
def snd (t : B R) : B R := fun d => .snd (t d)
def pair (a b : B R) : B R := fun d => .pair (a d) (b d)
def qlit (r : R) : B R := closed (.qlit r)

/-- `t.2.2….1`: the `k`-th component of a right-nested tuple. -/
def proj (t : B R) (k : Nat) : B R := fst ((List.range k).foldl (fun acc _ => snd acc) t)

/-- `(a₁, (a₂, …, ()))` -/
def tuple (as : List (B R)) : B R := as.foldr pair (closed .tt)

/-- A term `t` living under a telescope, with its variables replaced: the `j`-th
variable of the telescope (outermost first) becomes `σ[j]`. -/
partial def ofTele (t : Term R) (σ : Array (B R)) : B R := fun d => go t 0 d
where
  go (t : Term R) (k d : Nat) : Term R :=
    match t with
    | .var i =>
      if i < k then .var i
      else
        let j := i - k
        if h : j < σ.size then (σ[σ.size - 1 - j]!) (d + k) else .var i
    | t => Id.run <| t.mapChildrenM pure (fun k' c => pure (go c (k + k') d))

/-- Normalise: evaluate in an environment of fresh variables and quote back. -/
def norm (g : Globals R) (b : B R) : B R := fun d =>
  let env : Env R := (List.range d).reverse.map Val.var
  quote g d (eval g env (b d))

end B

/-- Peel a Π-telescope: binders (each in the context of the previous ones) and body. -/
def peelPis : Term R → List (Name × BinderInfo × Term R × Term R) × Term R
  | .pi x bi q A b => let (bs, r) := peelPis b; ((x, bi, q, A) :: bs, r)
  | t => ([], t)

open B in
/-- Generate `T.rec` (`withIH := true`) or `T.casesOn`. -/
def mkRecursor (g : Globals R) (T : Name) (ctors : List Name) (withIH : Bool) :
    Except String (Decl R) := do
  let some Td := g.find? T | throw s!"unknown inductive {T}"
  let some descD := g.find? (T ++ ".desc") | throw s!"{T} has no description"
  let ps := Td.levelParams
  let us := ps.map Level.param
  let vName := (["v", "v'", "v''", "w"].find? (!ps.contains ·)).getD "v_rec"
  let v : Level := .param vName
  let (Δ, descTy) := peelPis descD.type
  let .desc l I := descTy | throw "malformed description type"
  let nΔ := Δ.length
  let (tele, _) := peelPis Td.type
  let Ξ := tele.drop nΔ
  let nΞ := Ξ.length
  -- `λ t. ecase …` from `T.desc`'s value: `fun Δ => Desc.arg w (Enum ls) F`
  let some descVal := descD.value | throw "description without value"
  let rec stripLams : Nat → Term R → Term R
    | 0, t => t
    | n + 1, .lam _ b => stripLams n b
    | _, t => t
  let .darg _ (.enum ls) F := stripLams nΔ descVal | throw "unexpected description shape"
  let w : R := QuantitySyntax.explicitDefault
  -- constructor signatures: fields after the Δ binders, and the result's index args
  let mut cinfo : Array (Name × List (Name × BinderInfo × Term R × Term R) × List (Term R)) := #[]
  for c in ctors do
    let some cd := g.find? (T ++ "." ++ c) | throw s!"missing constructor {c}"
    let (bs, res) := peelPis cd.type
    let fields := bs.drop nΔ
    cinfo := cinfo.push (c, fields, (Term.spine res).2.drop nΔ)
  let recName := T ++ (if withIH then ".rec" else ".casesOn")
  -- the shared signature, as a function of the bound variables
  let Tc : B R := closed (.const T us)
  let isRec (A : Term R) : Bool := match (Term.spine A).1 with
    | .const n _ => n == T
    | _ => false
  /- Bind Δ, motive, methods, ξ, x with `binder`, then finish with `k`. -/
  let rec bindTele (binder : Name → BinderInfo → B R → B R → (B R → B R) → B R)
      (bs : List (Name × BinderInfo × Term R × Term R)) (σ : Array (B R))
      (bi? : Option BinderInfo) (q? : Option (B R)) (k : Array (B R) → B R) : B R :=
    match bs with
    | [] => k σ
    | (x, bi, q, A) :: rest =>
      binder x (bi?.getD bi) (q?.getD (ofTele q σ)) (ofTele A σ) fun xv =>
        bindTele binder rest (σ.push xv) bi? q? k
  let build (binder : Name → BinderInfo → B R → B R → (B R → B R) → B R) (body : Array (B R) → B R → Array (B R) → Array (B R) → B R → B R) : B R :=
    bindTele binder Δ #[] (some .implicit) (some (qlit 0)) fun Δv =>
    -- motive : (ξ : Ξ) → T Δ ξ → Sort v
    let motiveTy : B R :=
      bindTele (fun x bi q A k => B.pi x bi q A k) Ξ Δv none none fun σ =>
        B.pi "x" .default (qlit w) (app Tc (σ.toList)) fun _ => closed (.sort v)
    binder "motive" .default (qlit 0) motiveTy fun mot =>
    -- methods
    let rec methods (cs : List (Name × List (Name × BinderInfo × Term R × Term R) × List (Term R)))
        (ms : Array (B R)) : B R :=
      match cs with
      | [] =>
        bindTele binder Ξ Δv (some .implicit) (some (qlit 0)) fun σ =>
          binder "x" .default (qlit w) (app Tc σ.toList) fun xv =>
            body Δv mot ms (σ.extract nΔ σ.size) xv
      | (c, fields, idx) :: rest =>
        let mTy : B R :=
          bindTele (fun x bi q A k => B.pi x bi q A k) fields Δv none none fun σ =>
            let fs := σ.extract nΔ σ.size
            let recs := (fields.zip fs.toList).zipIdx.filterMap fun (((_, _, _, A), f), k) =>
              if isRec A then some (A, f, k) else none
            let rec ihs (rs : List (Term R × B R × Nat)) (σ' : Array (B R)) : B R :=
              match rs with
              | [] => app mot ((idx.map (ofTele · σ)) ++ [app (closed (.const (T ++ "." ++ c) us)) σ.toList])
              | (A, f, k) :: rs' =>
                -- `A` lives in the context of Δ and the fields before it
                let js := (Term.spine A).2.drop nΔ
                let σk := σ.extract 0 (nΔ + k)
                B.pi "ih" .default (qlit w) (app mot ((js.map (ofTele · σk)) ++ [f])) fun _ => ihs rs' σ'
            if withIH then ihs recs σ else ihs [] σ
        binder ("m_" ++ c) .default (qlit w) mTy fun m => methods rest (ms.push m)
    methods cinfo.toList #[]
  -- the type
  let ty := build (fun x bi q A k => B.pi x bi q A k) fun _ mot _ ξ xv => app mot (ξ.toList ++ [xv])
  -- the value
  let val := build (fun x _ _ _ k => B.lam x k) fun Δv mot ms ξ xv =>
    let Iv := ofTele I Δv
    let Dv := app (closed (.const (T ++ ".desc") us)) Δv.toList
    let X := B.lam "j" fun j => fun d => .mu l (Iv d) (Dv d) (j d) none
    let unpack (i : B R) : List (B R) := (List.range nΞ).map (proj i)
    let P := B.lam "i" fun i => B.lam "y" fun y => app mot (unpack i ++ [y])
    let Fv := ofTele F Δv
    let M := B.lam "i" fun i => B.lam "xs" fun xs => B.lam "ih" fun ih =>
      let interpOf (Dz : B R) := app (closed (Templates.interpTm l)) [Iv, Dz, X, i]
      let allOf (Dz r : B R) := app (closed (Templates.allTm l v)) [Iv, Dz, X, P, i, r]
      let motiveZ : B R := fun d =>
        -- under the ecase binder `z`, which is variable `d - 1` at depth `d`
        let z := bvar (d - 1)
        let Dz := app Fv [z]
        norm g (B.pi "rest" .default (qlit w) (interpOf Dz) fun r =>
          B.pi "h" .default (qlit w) (allOf Dz r) fun _ =>
            app P [i, fun d => .con (.pair (z d) (r d))]) d
      let branches : List (B R) := cinfo.toList.zipIdx.map fun ((c, fields, idx), ci) =>
        B.lam "rest" fun r => B.lam "h" fun h =>
          let n := fields.length
          let fs := (List.range n).map (proj r)
          let e := proj r n
          let recIx := (fields.zipIdx.filter fun ((_, _, _, A), _) => isRec A).length
          let ihs := (List.range recIx).map (proj h)
          let σ := Δv ++ fs.toArray
          let idxB := idx.map (ofTele · σ)
          let ctorApp := app (closed (.const (T ++ "." ++ c) us)) (Δv.toList ++ fs)
          let A := norm g (app mot (idxB ++ [ctorApp]))
          let tag : B R := closed (.tag ls ci)
          let Bty := norm g (app mot (unpack i ++ [fun d => .con (.pair (tag d) (r d))]))
          -- Q j e' := A = motive j (con (tag, f…, e', ()))
          let Q := B.lam "j" fun j => B.lam "e" fun e' => fun d =>
            .eqTy (A d) ((norm g (app mot (unpack j ++
              [fun d => .con (.pair (tag d) ((fs ++ [e']).foldr pair (closed .tt) d))]))) d)
          let prf : B R := fun d => .transp (Iv d) (tuple idxB d) (Q d) (.reflTy (A d)) (i d) (e d)
          let inner := app (ms[ci]!) (fs ++ (if withIH then ihs else []))
          fun d => .cast (A d) (Bty d) (prf d) (inner d)
      fun d => .app (.app (.ecase "z" (motiveZ (d + 1)) (.fst (xs d)) (branches.map (· d)))
        (.snd (xs d))) (ih d)
    fun d => .ind l (Iv d) (Dv d) v (P d) (M d) (tuple ξ.toList d) (xv d)
  pure { name := recName, levelParams := ps ++ [vName], type := ty 0, value := some (val 0) }

end Wiz.Elab
