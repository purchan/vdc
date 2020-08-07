open import core public

size   : Ty → ℕ
toBool : Ty → List Ty

encode : (τ : Ty) → Ty⟦ τ ⟧ → Vals (toBool τ)
decode : (τ : Ty) → Vals (toBool τ) → Ty⟦ τ ⟧

------------------------
toBools : List Ty → List Ty

data Vals′ : (τs : List Ty) → Vals (toBools τs) → Set

splitVals  : (valστ : Vals (σs ++ τs))
           → Σ[ valσ ∈ Vals σs ] Σ[ valτ ∈ Vals τs ] (valστ ≡ valσ ++Vl valτ)
toVals′  : (τs : List Ty) (bvals : Vals (toBools τs)) → Vals′ τs bvals
decodes′ : (τs : List Ty) (bvals : Vals (toBools τs)) → Vals′ τs bvals → Vals τs

_++bVl_ : Vals (toBools Γ) → Vals (toBools Γ′) → Vals (toBools (Γ ++ Γ′))
------------------------
encodes : (τs : List Ty) → Vals τs → Vals (toBools τs)
decodes : (τs : List Ty) → Vals (toBools τs) → Vals τs

encodeVar  : σ ∈ Γ → Vars (toBools Γ) (toBool σ)
encodeVars : Vars Γ Δ → Vars (toBools Γ) (toBools Δ)

------------------------

data Circ′ : List Ty → List Ty → Set

Cr′⟦_⟧ : Circ′ Γ Δ → Vals (toBools Γ) → Vals (toBools Δ)

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


_++bVl_ {[]}     {Γ′} []                   bvalΓ′ = bvalΓ′
_++bVl_ {σ ∷ σs} {Γ′} bvalΓ                bvalΓ′ with splitVals {toBool σ} {toBools σs} bvalΓ
_++bVl_ {σ ∷ σs} {Γ′} .(bvalσ ++Vl bvalσs) bvalΓ′    | ⟨ bvalσ , ⟨ bvalσs , refl ⟩ ⟩
                                                  = bvalσ ++Vl (_++bVl_ {σs} {Γ′} bvalσs bvalΓ′)

------------------------
encodes []       [] = []
encodes (τ ∷ τs) (val ∷ vals) = encode τ val ++Vl encodes τs vals

decodes τs bvals = decodes′ τs bvals (toVals′ τs bvals)


encodeVar {σ} {σ ∷ σs} here      = sufVars (toBools σs) (iniVars (toBool σ))
encodeVar {σ} {x ∷ σs} (there l) = preVars (toBool x) (encodeVar {σ} {σs} l)

encodeVars []          = []
encodeVars (vr ∷ vars) = encodeVar vr ++Vr encodeVars vars

------------------------
data Circ′ where
  ret  : Vars Γ Δ → Circ′ Γ Δ
  oper : Op Γ τ   → Circ′ Γ [ τ ]
  comp : Vars Γ Θ → Circ′ Θ Θ′ → Circ′ (Θ′ ++ Γ) Δ → Circ′ Γ Δ

Cr′⟦ ret vars ⟧        bvals = lookup (encodeVars vars) bvals
Cr′⟦ oper {Γ} {τ} op ⟧ bvals = encodes [ τ ] [ Op⟦ op ⟧ (decodes Γ bvals) ]
Cr′⟦ comp {Γ} {Θ} {Θ′} {Δ} vars c k ⟧ bvals =
  Cr′⟦ k ⟧ (_++bVl_ {Θ′} {Γ} bvalΘ′ bvals)
  where bvalΘ′ = Cr′⟦ c ⟧ (lookup (encodeVars vars) bvals)
