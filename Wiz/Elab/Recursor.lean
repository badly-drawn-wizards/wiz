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
  fun d => .pi x bi (q d) (A d) (body (bvar d) (d + 1)) none
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
  | .pi x bi q A b _ => let (bs, r) := peelPis b; ((x, bi, q, A) :: bs, r)
  | t => ([], t)

/-- Does the inductive `T` have indices (beyond its parameters)? -/
def isIndexed (g : Globals R) (T : Name) : Bool :=
  match g.find? T, g.find? (T ++ ".desc") with
  | some Td, some descD => (peelPis Td.type).1.length > (peelPis descD.type).1.length
  | _, _ => false

open B in
/-- Generate `T.rec` (`withIH := true`) or `T.casesOn`. With `nondep`, `T.recN` or
`T.casesOnN`: the motive is a type `M : Sort v` instead of a family over the indices
and the value. Their branches need no cast along the constructor's index equation (both
sides are `M`), so they compute on a constructor without regularity; the match compiler
uses them when its motive doesn't depend on the scrutinee. -/
def mkRecursor (g : Globals R) (T : Name) (ctors : List Name) (withIH : Bool) (sized : Bool := false)
    (nondep : Bool := false) : Except String (Decl R) := do
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
  -- index tuples end in `()`, or in the value of a phantom tail (`phantomTail`), which is
  -- closed: read it off `T`'s definition, `fun Δ ξ => μ … (ξ…, tail)`
  let rec stripN : Nat → Term R → Term R
    | 0, t => t
    | n + 1, .lam _ b => stripN n b
    | _, t => t
  let rec dropPairs : Nat → Term R → Term R
    | 0, t => t
    | n + 1, .pair _ b => dropPairs n b
    | _, t => t
  let tailTm : Term R := match Td.value.map (stripN (nΔ + nΞ)) with
    | some (.mu _ _ _ idx _ _) => dropPairs nΞ idx
    | _ => .tt
  let tuple (as : List (B R)) : B R := as.foldr pair (closed tailTm)
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
  let recName := T ++ (if sized then ".scasesOn" else if withIH then ".rec" else ".casesOn") ++
    (if nondep then "N" else "")
  let motApp (mot : B R) (args : List (B R)) : B R := if nondep then mot else app mot args
  -- the shared signature, as a function of the bound variables
  let Tc : B R := closed (.const T us)
  -- a recursive field `T Δ js`, or an infinitary one `(h : H) → T Δ js` (`js` under `h`)
  let recView (A : Term R) : Option (Option (Name × Term R) × List (Term R)) :=
    match Term.spine A with
    | (.const n _, args) => if n == T then some (none, args.drop nΔ) else none
    | (.pi h _ _ H Bd _, []) => match Term.spine Bd with
      | (.const n _, args) => if n == T then some (some (h, H), args.drop nΔ) else none
      | _ => none
    | _ => none
  let isRec (A : Term R) : Bool := (recView A).isSome
  /- Bind Δ, motive, methods, ξ, x with `binder`, then finish with `k`. -/
  let rec bindTele (binder : Name → BinderInfo → B R → B R → (B R → B R) → B R)
      (bs : List (Name × BinderInfo × Term R × Term R)) (σ : Array (B R))
      (bi? : Option BinderInfo) (q? : Option (B R)) (k : Array (B R) → B R)
      (tyOf : Term R → Array (B R) → B R := ofTele) : B R :=
    match bs with
    | [] => k σ
    | (x, bi, q, A) :: rest =>
      binder x (bi?.getD bi) (q?.getD (ofTele q σ)) (tyOf A σ) fun xv =>
        bindTele binder rest (σ.push xv) bi? q? k tyOf
  -- `T Δ js` at size `sz`, keeping the display hint
  let sizedT (Δv : Array (B R)) (js : List (B R)) (sz : B R) : B R := fun d =>
    .mu l ((ofTele I Δv) d) ((app (closed (.const (T ++ ".desc") us)) Δv.toList) d) (tuple js d) (sz d)
      (some (T, us, (Δv.toList ++ js).map (· d)))
  let build (binder : Name → BinderInfo → B R → B R → (B R → B R) → B R)
      (body : Option (B R) → Array (B R) → B R → Array (B R) → Array (B R) → B R → B R) : B R :=
    bindTele binder Δ #[] (some .implicit) (some (qlit 0)) fun Δv =>
    let withSize (k : Option (B R) → B R) : B R :=
      if sized then binder "s" .implicit (qlit 0) (closed .size) fun sv => k (some sv) else k none
    withSize fun sv? =>
    -- motive : (ξ : Ξ) → T Δ ξ → Sort v
    let motiveTy : B R := if nondep then closed (.sort v) else
      bindTele (fun x bi q A k => B.pi x bi q A k) Ξ Δv none none fun σ =>
        B.pi "x" .default (qlit w) (app Tc (σ.toList)) fun _ => closed (.sort v)
    binder "motive" .default (qlit 0) motiveTy fun mot =>
    -- methods
    let rec methods (cs : List (Name × List (Name × BinderInfo × Term R × Term R) × List (Term R)))
        (ms : Array (B R)) : B R :=
      match cs with
      | [] =>
        bindTele binder Ξ Δv (some .implicit) (some (qlit 0)) fun σ =>
          let xTy := match sv? with
            | some sv => sizedT Δv (σ.extract nΔ σ.size).toList sv
            | none => app Tc σ.toList
          binder "x" .default (qlit w) xTy fun xv =>
            body sv? Δv mot ms (σ.extract nΔ σ.size) xv
      | (c, fields, idx) :: rest =>
        let fieldsTy (jv? : Option (B R)) : B R :=
          bindTele (fun x bi q A k => B.pi x bi q A k) fields Δv none none (tyOf := fun A σ =>
            match jv? with
            | some jv => match recView A with
              | some (none, js) => sizedT Δv (js.map (ofTele · σ)) jv
              | some (some (h, H), js) =>
                B.pi h .default (qlit w) (ofTele H σ) fun hv => sizedT Δv (js.map (ofTele · (σ.push hv))) jv
              | none => ofTele A σ
            | none => ofTele A σ) fun σ =>
            let fs := σ.extract nΔ σ.size
            let recs := (fields.zip fs.toList).zipIdx.filterMap fun (((_, _, _, A), f), k) =>
              if isRec A then some (A, f, k) else none
            let rec ihs (rs : List (Term R × B R × Nat)) (σ' : Array (B R)) : B R :=
              match rs with
              | [] => motApp mot ((idx.map (ofTele · σ)) ++ [app (closed (.const (T ++ "." ++ c) us)) σ.toList])
              | (A, f, k) :: rs' =>
                -- `A` lives in the context of Δ and the fields before it
                let σk := σ.extract 0 (nΔ + k)
                let ihTy : B R := match recView A with
                  | some (some (h, H), js) =>
                    -- infinitary: one hypothesis per `h`
                    B.pi h .default (qlit w) (ofTele H σk) fun hv =>
                      motApp mot ((js.map (ofTele · (σk.push hv))) ++ [app f [hv]])
                  | some (none, js) => motApp mot ((js.map (ofTele · σk)) ++ [f])
                  | none => motApp mot [f]
                B.pi "ih" .default (qlit w) ihTy fun _ => ihs rs' σ'
            if withIH then ihs recs σ else ihs [] σ
        let mTy : B R := match sv? with
          | some sv => B.pi "j" .default (qlit 0) (fun d => .sizeLt (sv d)) fun jv => fieldsTy (some jv)
          | none => fieldsTy none
        binder ("m_" ++ c) .default (qlit w) mTy fun m => methods rest (ms.push m)
    methods cinfo.toList #[]
  -- the type
  let ty := build (fun x bi q A k => B.pi x bi q A k) fun _ _ mot _ ξ xv => motApp mot (ξ.toList ++ [xv])
  -- the value
  let val := build (fun x _ _ _ k => B.lam x k) fun sv? Δv mot ms ξ xv =>
    let Iv := ofTele I Δv
    let Dv := app (closed (.const (T ++ ".desc") us)) Δv.toList
    let familyAt (sz : B R) : B R := B.lam "j" fun j => fun d => .mu l (Iv d) (Dv d) (j d) (sz d) none
    let unpack (i : B R) : List (B R) := (List.range nΞ).map (proj i)
    let P := B.lam "i" fun i => B.lam "y" fun y => motApp mot (unpack i ++ [y])
    let Fv := ofTele F Δv
    -- the method of `ind` (`fun i xs ih`) or of `scase` (`fun j i xs`, no hypotheses)
    let methodBody (jv? : Option (B R)) (i xs : B R) (ih? : Option (B R)) : B R :=
      let X := familyAt (jv?.getD (closed .szInf))
      -- `con payload` at index `idx`: in sized mode it is a value of size `↑j`, so say so
      -- (it then subtypes into the motive's `μ^∞`)
      let conAt (idx payload : B R) : B R := fun d =>
        match jv? with
        | some jv => .ann (.con (payload d)) (.mu l (Iv d) (Dv d) (idx d) (.szSuc (jv d)) none)
        | none => .con (payload d)
      let interpOf (Dz : B R) := app (closed (Templates.interpTm l)) [Iv, Dz, X, i]
      let allOf (Dz r : B R) := app (closed (Templates.allTm l v)) [Iv, Dz, X, P, i, r]
      let motiveZ : B R := fun d =>
        -- under the ecase binder `z`, which is variable `d - 1` at depth `d`
        let z := bvar (d - 1)
        let Dz := app Fv [z]
        -- normalise only the template parts: evaluation would drop `conAt`'s annotation
        (B.pi "rest" .default (qlit w) (norm g (interpOf Dz)) fun r =>
          let goal := motApp mot (unpack i ++ [conAt i (pair z r)])
          if ih?.isSome then B.pi "h" .default (qlit w) (norm g (allOf Dz r)) fun _ => goal else goal) d
      let branches : List (B R) := cinfo.toList.zipIdx.map fun ((c, fields, idx), ci) =>
        let withH (k : B R → B R) : B R := if ih?.isSome then B.lam "h" k else k (closed .tt)
        B.lam "rest" fun r => withH fun h =>
          let n := fields.length
          let fs := (List.range n).map (proj r)
          let e := proj r n
          let recIx := (fields.zipIdx.filter fun ((_, _, _, A), _) => isRec A).length
          let ihs := (List.range recIx).map (proj h)
          let σ := Δv ++ fs.toArray
          let idxB := idx.map (ofTele · σ)
          let ctorApp := app (closed (.const (T ++ "." ++ c) us)) (Δv.toList ++ fs)
          let A := norm g (motApp mot (idxB ++ [ctorApp]))
          let tag : B R := closed (.tag ls ci)
          let Bty := motApp mot (unpack i ++ [conAt i (pair tag r)])
          -- Q j e' := A = motive j (con (tag, f…, e', ()))
          let Q := B.lam "j" fun j => B.lam "e" fun e' => fun d =>
            .eqTy (A d) ((motApp mot (unpack j ++
              [conAt j (pair tag ((fs ++ [e']).foldr pair (closed .tt)))])) d)
          let prf : B R := fun d => .transp (Iv d) (tuple idxB d) (Q d) (.reflTy (A d)) (i d) (e d)
          let inner := app (ms[ci]!) ((jv?.toList) ++ fs ++ (if withIH then ihs else []))
          -- without indices the two motives agree (`con (tag, r)` is the constructor
          -- applied to `r`'s fields, by η), so no cast: then the recursor computes on a
          -- constructor even at a neutral motive, without regularity
          if nΞ == 0 || nondep then inner else
          fun d => .cast (A d) (Bty d) (prf d) (inner d)
      fun d =>
        let e := Term.app (.ecase "z" (motiveZ (d + 1)) (.fst (xs d)) (branches.map (· d))) (.snd (xs d))
        match ih? with
        | some ih => .app e (ih d)
        | none => e
    match sv? with
    | some sv =>
      let M := B.lam "j" fun j => B.lam "i" fun i => B.lam "xs" fun xs => methodBody (some j) i xs none
      fun d => .scase l (Iv d) (Dv d) v (P d) (M d) (sv d) (tuple ξ.toList d) (xv d)
    | none =>
      -- (`casesOn` ignores the hypotheses: then the compiler can skip computing them)
      let M := B.lam "i" fun i => B.lam "xs" fun xs => B.lam "ih" fun ih =>
        methodBody none i xs (if withIH then some ih else none)
      fun d => .ind l (Iv d) (Dv d) v (P d) (M d) (tuple ξ.toList d) (xv d)
  pure { name := recName, levelParams := ps ++ [vName], type := ty 0, value := some (val 0) }

end Wiz.Elab
