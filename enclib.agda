open import core public

size   : Ty → ℕ
toBool : Ty → List Ty

encode : (τ : Ty) → Ty⟦ τ ⟧ → Vals (toBool τ)
decode : (τ : Ty) → Vals (toBool τ) → Ty⟦ τ ⟧
------------------------
toBools : List Ty → List Ty

data Vals′ : (τs : List Ty) → Vals (toBools τs) → Set

splitVals  : {σs : List Ty} {τs : List Ty} (valστ : Vals (σs ++ τs))
           → Σ[ valσ ∈ Vals σs ] Σ[ valτ ∈ Vals τs ] (valστ ≡ valσ ++Vl valτ)
toVals′  : (τs : List Ty) (bvals : Vals (toBools τs)) → Vals′ τs bvals
decodes′ : (τs : List Ty) (bvals : Vals (toBools τs))
         → Vals′ τs bvals → Vals τs

------------------------
encodes : (τs : List Ty) → Vals τs → Vals (toBools τs)
decodes : (τs : List Ty) → Vals (toBools τs) → Vals τs

encodeVar  : σ ∈ Γ → Vars (toBools Γ) (toBool σ)
encodeVars : Vars Γ Δ → Vars (toBools Γ) (toBools Δ)

------------------------
toBools-++ : toBools Γ ++ toBools Γ′ ≡ toBools (Γ ++ Γ′)

data Circ′ : List Ty → List Ty → Set

Cr′⟦_⟧ : Circ′ Γ Δ → Vals Γ → Vals Δ

toCirc′ : Circ Γ Δ → Circ′ Γ Δ

sufCirc′ : (Γ′ : List Ty) → Circ′ Γ Δ → Circ′ (Γ ++ Γ′) Δ

------------------------------------------------
size bool = 1
size tri  = 2
toBool τ  = replicate (size τ) bool

encode bool b     = [ b ]
encode tri  true  = [ false , true  ]
encode tri  false = [ false , false ]
encode tri  dc    = [ true  , false ]
decode bool [ b ] = b
decode tri  [ false , true  ] = true
decode tri  [ false , false ] = false
decode tri  [ true  , _     ] = dc

------------------------
toBools = concatMap toBool

data Vals′ where
  nil  : Vals′ [] []
  cons : {τ : Ty} {τs : List Ty}
       → (bval : Vals (toBool τ)) (bvals : Vals (toBools τs))
       → Vals′ τs bvals → Vals′ (τ ∷ τs) (bval ++Vl bvals)


splitVals {[]}     valτ = ⟨ _ , ⟨ valτ , refl ⟩ ⟩
splitVals {σ ∷ σs} (val ∷ vals) with splitVals {σs} vals
...                                | ⟨ val′ , ⟨ valτ , pf ⟩ ⟩ = ⟨ val ∷ val′ , ⟨ valτ , cong (val ∷_) pf ⟩ ⟩


toVals′ []       []    = nil
toVals′ (τ ∷ τs) bvals                with splitVals {toBool τ} {toBools τs} bvals
toVals′ (τ ∷ τs) .(bvalτ ++Vl bvalτs) | ⟨ bvalτ , ⟨ bvalτs , refl ⟩ ⟩
                       = cons {τ} {τs} bvalτ bvalτs (toVals′ τs bvalτs)

decodes′ []       ._                 nil                     = []
decodes′ (τ ∷ τs) .(bval ++Vl bvals) (cons bval bvals vals′) = decode τ bval ∷ decodes′ τs bvals vals′

------------------------
encodes []       [] = []
encodes (τ ∷ τs) (val ∷ vals) = encode τ val ++Vl encodes τs vals

decodes τs bvals = decodes′ τs bvals (toVals′ τs bvals)


encodeVar {σ} {σ ∷ σs} here      = sufVars (toBools σs) (iniVars (toBool σ))
encodeVar {σ} {x ∷ σs} (there l) with encodeVar {σ} {σs} l
...                                 | evar
                                 = preVars (toBool x) evar

encodeVars []          = []
encodeVars (vr ∷ vars) = encodeVar vr ++Vr encodeVars vars

------------------------
toBools-++ {[]} = refl
toBools-++ {σ ∷ σs} {Γ′} =
  begin
    toBools (σ ∷ σs) ++ toBools Γ′
  ≡⟨⟩
    (toBool σ ++ toBools σs) ++ toBools Γ′
  ≡⟨ ++-assoc (toBool σ) (toBools σs) (toBools Γ′) ⟩
    toBool σ ++ (toBools σs ++ toBools Γ′)
  ≡⟨ cong (toBool σ ++_) (toBools-++ {σs} {Γ′}) ⟩
    toBool σ ++ toBools (σs ++ Γ′)
  ≡⟨⟩
    toBools ((σ ∷ σs) ++ Γ′)
  ∎


data Circ′ where
  ret  : Vars Γ Δ → Circ′ Γ Δ
  oper : Op Γ τ   → Circ′ Γ [ τ ]
  comp : Vars Γ Θ → Circ′ Θ Θ′ → Circ′ (Θ′ ++ Γ) Δ → Circ′ Γ Δ

  enc  : (Γ : List Ty) → Circ′ Γ (toBools Γ)
  dec  : (Γ : List Ty) → Circ′ (toBools Γ) Γ

Cr′⟦ ret vars ⟧ vals = lookup vars vals
Cr′⟦ oper op  ⟧ vals = [ Op⟦ op ⟧ vals ]
Cr′⟦ comp vars c k ⟧ vals = Cr′⟦ k ⟧ (Cr′⟦ c ⟧ (lookup vars vals) ++Vl vals)

Cr′⟦ enc Γ ⟧  = encodes Γ
Cr′⟦ dec Γ ⟧  = decodes Γ


toCirc′ (ret vars) = ret vars
toCirc′ (oper op)  = oper op
toCirc′ (comp vars c k) = comp vars (toCirc′ c) (toCirc′ k)

sufCirc′ {Γ} {Δ} Γ′ circ = comp pick₁ circ (ret pick₂)
                         where pick₁ = sufVars Γ′ (iniVars Γ)
                               pick₂ = sufVars (Γ ++ Γ′) (iniVars Δ)
