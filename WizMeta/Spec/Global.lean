import WizMeta.Spec.Rule

/-!
# Global constants

A signature is a list of closed declarations, each with a number of level parameters
(prenex universe polymorphism). A constant is used at a list of levels; a definition
unfolds (δ). There is no recursion: a declaration is checked in the signature before it
(`Fragments.lean`, `Sig.WF`).
-/

namespace WizMeta.Spec

inductive Global (sg : Sig) : Rules
  | const {Γ : Ctx} {us : List Lvl} {c : String} {d : Decl} : sg.find? c = some d → us.length = d.nparams →
      Global sg ⟨[.wf Γ], Γ ⊢ .const c us ∶ d.type.instL us⟩
  | delta {Γ : Ctx} {v : Tm} {us : List Lvl} {c : String} {d : Decl} : sg.find? c = some d → us.length = d.nparams → d.value = some v →
      Global sg ⟨[.wf Γ], Γ ⊢ .const c us ⟶ v.instL us ∶ d.type.instL us⟩
  | cong {Γ : Ctx} {us us' : List Lvl} {c : String} {d : Decl} : sg.find? c = some d → us.length = d.nparams → us.length = us'.length → (∀ p ∈ us.zip us', p.1.Equiv p.2) →
      Global sg ⟨[.wf Γ], Γ ⊢ .const c us ≡ .const c us' ∶ d.type.instL us⟩

end WizMeta.Spec
