open import core public

size   : Ty → ℕ
toBool : Ty → List Ty

decode : (τ : Ty) → Vals (toBool τ) → Ty⟦ τ ⟧

------------------------
toBools : List Ty → List Ty
toBools-∷ : (σ : Ty) (σs : List Ty) (pf : Θ ≡ σ ∷ σs)
           → toBools Θ ≡ toBool σ ++ toBools σs
toBools-++ : (Γ Γ′ : List Ty) (pf : Θ ≡ Γ ++ Γ′)
           → toBools Θ ≡ toBools Γ ++ toBools Γ′

splitVals : (valστ : Vals Ω) (pf : Ω ≡ σs ++ τs)
           → Σ[ valσ ∈ Vals σs ] Σ[ valτ ∈ Vals τs ] (valστ ≡ ++Vlp valσ valτ pf)
------------------------
decodes : (τs : List Ty) → Vals (toBools τs) → Vals τs

encodeVar  : σ ∈ Γ → Vars (toBools Γ) (toBool σ)
encodeVars : Vars Γ Δ → Vars (toBools Γ) (toBools Δ)

------------------------
preCirc′ : (Γ′ : List Ty) → Circ Γ Δ → Circ (Γ′ ++ Γ) (Γ′ ++ Δ)
_++Cr_ : Circ Γ Δ → Circ Γ Δ′ → Circ Γ (Δ ++ Δ′)

data Lit Γ : Set
data Cls Γ : Set
data Cnf Γ : Set

litCirc : Lit Γ → Circ (toBools Γ) [ bool ]
clsCirc : Cls Γ → Circ (toBools Γ) [ bool ]
cnfCirc : Cnf Γ → Circ (toBools Γ) [ bool ]

encodeOp : Op Γ τ → Circ (toBools Γ) (toBools [ τ ])
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
toBools-∷ σ σs refl = refl

toBools-++ []       Γ′ refl = refl
toBools-++ (σ ∷ σs) Γ′ refl =
  begin
    toBools (σ ∷ σs ++ Γ′)
  ≡⟨⟩
    toBool σ ++ toBools (σs ++ Γ′)
  ≡⟨ cong (toBool σ ++_) (toBools-++ σs Γ′ refl) ⟩
    toBool σ ++ (toBools σs ++ toBools Γ′)
  ≡⟨ sym (++-assoc (toBool σ) (toBools σs) (toBools Γ′)) ⟩
    (toBool σ ++ toBools σs) ++ toBools Γ′
  ≡⟨⟩
    toBools (σ ∷ σs) ++ toBools Γ′
  ∎

splitVals {σs = []}     valτ         refl = ⟨ _ , ⟨ valτ , refl ⟩ ⟩
splitVals {σs = σ ∷ σs} (val ∷ vals) refl with splitVals {σs = σs} vals refl
...                                           | ⟨ val″ , ⟨ valτ , pf″ ⟩ ⟩ = ⟨ val ∷ val″ , ⟨ valτ , cong (val ∷_) pf″ ⟩ ⟩
------------------------
decodes []       []    = []
decodes (τ ∷ τs) bvals                                       with splitVals {σs = toBool τ} {τs = toBools τs} bvals (toBools-∷ τ τs refl)
decodes (τ ∷ τs) .(++Vlp bvalτ bvalτs (toBools-∷ τ τs refl))    | ⟨ bvalτ , ⟨ bvalτs , refl ⟩ ⟩ = decode τ bvalτ ∷ decodes τs bvalτs

encodeVar {σ} {σ ∷ σs} here      = sufVars (toBools σs) (iniVars (toBool σ))
encodeVar {σ} {x ∷ σs} (there l) = preVars (toBool x) (encodeVar {σ} {σs} l)

encodeVars []          = []
encodeVars (vr ∷ vars) = encodeVar vr ++Vr encodeVars vars

------------------------

preCirc′ {Γ} {Δ} Γ′ circ = comp pick₁ circ refl (ret pick₂)
                         where pick₁ = preVars Γ′ (iniVars Γ)

                               pick₂₁ = preVars Δ (sufVars Γ (iniVars Γ′))
                               pick₂₂ = sufVars (Γ′ ++ Γ) (iniVars Δ)
                               pick₂ = pick₂₁ ++Vr pick₂₂

_++Cr_ {Γ} {Δ} {Δ′} c₁ c₂ = comp (iniVars Γ) c₁ refl (preCirc′ Δ c₂)

data Lit Γ where
  pos   : bool ∈ toBools Γ → Lit Γ
  neg   : bool ∈ toBools Γ → Lit Γ

data Cls Γ where
  triv : Lit Γ → Cls Γ
  disj : Lit Γ → Cls Γ → Cls Γ

data Cnf Γ where
  triv : Cls Γ → Cnf Γ
  conj : Cls Γ → Cnf Γ → Cnf Γ


litCirc     (pos i) = ret [ i ]
litCirc {Γ} (neg i) = comp [ i ] (oper notB) refl (ret pick)
                    where pick = sufVars (toBools Γ) (iniVars [ bool ])

clsCirc     (triv l)   = litCirc l
clsCirc {Γ} (disj l c) = comp pick₁ (litCirc l ++Cr clsCirc c) refl (comp pick₂ (oper orB) refl  (ret pick₃))
                       where pick₁ = iniVars (toBools Γ)
                             pick₂ = sufVars (toBools Γ) (iniVars [ bool , bool ])
                             pick₃ = sufVars (bool ∷ bool ∷ toBools Γ) (iniVars [ bool ])

cnfCirc     (triv c)   = clsCirc c
cnfCirc {Γ} (conj c n) = comp pick₁ (clsCirc c ++Cr cnfCirc n) refl (comp pick₂ (oper andB) refl (ret pick₃))
                       where pick₁ = iniVars (toBools Γ)
                             pick₂ = sufVars (toBools Γ) (iniVars [ bool , bool ])
                             pick₃ = sufVars (bool ∷ bool ∷ toBools Γ) (iniVars [ bool ])

------------------------

pattern i11 = here
pattern i12 = there here
pattern i21 = there (there here)
pattern i22 = there (there (there here))

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
