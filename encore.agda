open import enclib public

Circ′-++ : (Γ′ : List Ty) → Circ′ Γ Δ → Circ′ (Γ ++ Γ′) Δ

compile : Circ Γ Δ → Circ′ (toBools Γ) (toBools Δ)
correctness : (c : Circ Γ Δ) (bvals : Vals (toBools Γ))
            → Cr⟦ c ⟧ (decodes Γ bvals) ≡ decodes Δ (Cr′⟦ compile c ⟧ bvals)

------------------------------------------------
Circ′-++ {Γ} {Δ} Γ′ circ = comp pick₁ circ (ret pick₂)
                         where pick₁ = sufVars Γ′ (iniVars Γ)
                               pick₂ = sufVars (Γ ++ Γ′) (iniVars Δ)

Circ′-toBools-++ : Circ′ (toBools (Γ ++ Γ′)) Δ ≡ Circ′ (toBools Γ ++ toBools Γ′) Δ
Circ′-toBools-++ {Γ} {Γ′} rewrite toBools-++ {Γ} {Γ′} = refl

compile (ret vars)        = ret (encodeVars vars)
compile (oper {Γ} {τ} op) = comp pick O∘D (Circ′-++ (toBools Γ) (enc [ τ ]))
                          where pick = iniVars (toBools Γ)
                                O∘D   = comp pick (dec Γ) (Circ′-++ (toBools Γ) (oper op))
compile (comp {Γ} {Θ} {Θ′} {Δ} vars c k) = comp (encodeVars vars) (compile c) (subst id pf (compile k))
                                         where pf = Circ′-toBools-++ {Θ′} {Γ} {toBools Δ}
