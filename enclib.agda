open import core public

size   : Ty → ℕ
toBool : Ty → List Ty

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
decodes : (τs : List Ty) → Vals (toBools τs) → Vals τs

encodeVar  : σ ∈ Γ → Vars (toBools Γ) (toBool σ)
encodeVars : Vars Γ Δ → Vars (toBools Γ) (toBools Δ)

------------------------------------------------
size bool = 1
size tri  = 2
toBool τ  = replicate (size τ) bool

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
decodes τs bvals = decodes′ τs bvals (toVals′ τs bvals)

encodeVar {σ} {σ ∷ σs} here      = sufVars (toBools σs) (iniVars (toBool σ))
encodeVar {σ} {x ∷ σs} (there l) = preVars (toBool x) (encodeVar {σ} {σs} l)

encodeVars []          = []
encodeVars (vr ∷ vars) = encodeVar vr ++Vr encodeVars vars

------------------------
preCirc : (Γ′ : List Ty) → Circ Γ Δ → Circ (Γ′ ++ Γ) Δ
preCirc {Γ} {Δ} Γ′ circ = comp pick₁ circ (ret pick₂)
                        where pick₁ = preVars Γ′ (iniVars Γ)
                              pick₂ = sufVars (Γ′ ++ Γ) (iniVars Δ)

sufCirc : (Γ′ : List Ty) → Circ Γ Δ → Circ (Γ ++ Γ′) Δ
sufCirc {Γ} {Δ} Γ′ circ = comp pick₁ circ (ret pick₂)
                         where pick₁ = sufVars Γ′ (iniVars Γ)
                               pick₂ = sufVars (Γ ++ Γ′) (iniVars Δ)

retOp : Vars Γ Γ′ → Op Γ′ τ → Circ Γ [ τ ]
retOp {Γ} vars op = comp (iniVars Γ) (ret vars) (sufCirc Γ (oper op))

preCirc′ : (Γ′ : List Ty) → Circ Γ Δ → Circ (Γ′ ++ Γ) (Γ′ ++ Δ)
preCirc′ {Γ} {Δ} Γ′ circ = comp pick₁ circ (ret pick₂)
                         where pick₁ = preVars Γ′ (iniVars Γ)

                               pick₂₁ = preVars Δ (sufVars Γ (iniVars Γ′))
                               pick₂₂ = sufVars (Γ′ ++ Γ) (iniVars Δ)
                               pick₂ = pick₂₁ ++Vr pick₂₂

_++Cr_ : Circ Γ Δ → Circ Γ Δ′ → Circ Γ (Δ ++ Δ′)
_++Cr_ {Γ} {Δ} {Δ′} c₁ c₂ = comp (iniVars Γ) c₁ (preCirc′ Δ c₂)

encodeOp : Op Γ τ → Circ (toBools Γ) (toBools [ τ ])
encodeOp andT = γ ++Cr c
              where α+β = retOp (here ∷ there (there here) ∷ []) orB
                    α+a = retOp (here ∷ there here ∷ []) orB
                    β+b = retOp (there (there here) ∷ there (there (there here)) ∷ []) orB

                    tb   = toBools [ tri , tri ]
                    reto = retOp (sufVars tb (iniVars [ bool , bool ])) andB

                    γ₁₂ = comp (iniVars tb) (α+β ++Cr α+a) reto
                    γ   = comp (iniVars tb) (γ₁₂ ++Cr β+b) reto

                    c   = retOp (there here ∷ there (there (there here)) ∷ []) andB
encodeOp ≡C   = c
              where tb   = toBools [ tri , tri ]
                    reto = retOp (sufVars tb (iniVars [ bool , bool ])) andB

                    α+β′   = comp (there (there here) ∷ []) (oper notB) (retOp (here ∷ there here ∷ []) orB)

                    α+b′ = comp (there (there (there here)) ∷ []) (oper notB) (retOp (here ∷ there here ∷ []) orB)
                    α+a+b′ = comp (iniVars tb) α+b′ (retOp (here ∷ there (there here) ∷ []) orB)

                    α+a′ = comp (there here ∷ []) (oper notB) (retOp (here ∷ there here ∷ []) orB)
                    α+a′+b = comp (iniVars tb) α+a′ (retOp (here ∷ there (there (there (there here))) ∷ []) orB)

                    c₁₂ = comp (iniVars tb) (α+β′ ++Cr α+a+b′) reto
                    c   = comp (iniVars tb) (c₁₂  ++Cr α+a′+b) reto

encodeOp andB = oper andB
encodeOp orB  = oper orB
encodeOp notB = oper notB
