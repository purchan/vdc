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
preCirc′ : (Γ′ : List Ty) → Circ Γ Δ → Circ (Γ′ ++ Γ) (Γ′ ++ Δ)
preCirc′ {Γ} {Δ} Γ′ circ = comp pick₁ circ (ret pick₂)
                         where pick₁ = preVars Γ′ (iniVars Γ)

                               pick₂₁ = preVars Δ (sufVars Γ (iniVars Γ′))
                               pick₂₂ = sufVars (Γ′ ++ Γ) (iniVars Δ)
                               pick₂ = pick₂₁ ++Vr pick₂₂

_++Cr_ : Circ Γ Δ → Circ Γ Δ′ → Circ Γ (Δ ++ Δ′)
_++Cr_ {Γ} {Δ} {Δ′} c₁ c₂ = comp (iniVars Γ) c₁ (preCirc′ Δ c₂)

--------------------------
data Lit Γ : Set where
  pos : bool ∈ toBools Γ → Lit Γ
  neg : bool ∈ toBools Γ → Lit Γ

data Cls Γ : Set where
  triv : Lit Γ → Cls Γ
  disj : Lit Γ → Cls Γ → Cls Γ

data Cnf Γ : Set where
  triv : Cls Γ → Cnf Γ
  conj : Cls Γ → Cnf Γ → Cnf Γ

litCirc : Lit Γ → Circ (toBools Γ) [ bool ]
litCirc     (pos i) = ret [ i ]
litCirc {Γ} (neg i) = comp [ i ] (oper notB) (ret pick)
                    where pick = sufVars (toBools Γ) (iniVars [ bool ])

clsCirc : Cls Γ → Circ (toBools Γ) [ bool ]
clsCirc     (triv l)   = litCirc l
clsCirc {Γ} (disj l c) = comp pick₁ (litCirc l ++Cr clsCirc c) (comp pick₂ (oper orB) (ret pick₃))
                       where pick₁ = iniVars (toBools Γ)
                             pick₂ = sufVars (toBools Γ) (iniVars [ bool , bool ])
                             pick₃ = sufVars (bool ∷ bool ∷ toBools Γ) (iniVars [ bool ])

cnfCirc : Cnf Γ → Circ (toBools Γ) [ bool ]
cnfCirc     (triv c)   = clsCirc c
cnfCirc {Γ} (conj c n) = comp pick₁ (clsCirc c ++Cr cnfCirc n) (comp pick₂ (oper andB) (ret pick₃))
                       where pick₁ = iniVars (toBools Γ)
                             pick₂ = sufVars (toBools Γ) (iniVars [ bool , bool ])
                             pick₃ = sufVars (bool ∷ bool ∷ toBools Γ) (iniVars [ bool ])

pattern i11 = here
pattern i12 = there here
pattern i21 = there (there here)
pattern i22 = there (there (there here))
--------------------------

encodeOp : Op Γ τ → Circ (toBools Γ) (toBools [ τ ])
encodeOp andT = cnfCirc {[ tri , tri ]} γn ++Cr cnfCirc {[ tri , tri ]} cn
              where γn = conj (disj (pos i11) (triv (pos i21)))
                         (conj (disj (pos i11) (triv (pos i12)))
                         (triv (disj (pos i21) (triv (pos i22)))))

                    cn = conj (triv (pos i12))
                         (triv (triv (pos i22)))
encodeOp ≡C   = cnfCirc {[ tri , tri ]} cn
              where cn = conj (disj (pos i11) (triv (neg i21)))
                         (conj (disj (pos i11) (disj (pos i12) (triv (neg i22))))
                         (triv (disj (pos i11) (disj (neg i12) (triv (pos i22))))))

encodeOp andB = oper andB
encodeOp orB  = oper orB
encodeOp notB = oper notB
