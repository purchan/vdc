open import enclib public

compile : Circ Γ Δ → Circ (toBools Γ) (toBools Δ)
correctness : (c : Circ Γ Δ) (bvals : Vals (toBools Γ))
            → Cr⟦ c ⟧ (decodes Γ bvals) ≡ decodes Δ (Cr⟦ compile c ⟧ bvals)

------------------------------------------------

compile (ret vars)        = ret (encodeVars vars)
compile (oper {Γ} {τ} op) = comp pickall (comp pickall (decodeCirc Γ) matchOp) matchEnc
                          where pickall   = allVars (toBools Γ)
                                matchOp   = buildCirc [] Γ (toBools Γ) [ τ ] (oper op)
                                matchEnc  = buildCirc [] [ τ ] (toBools Γ) (toBools [ τ ]) (encodeCirc [ τ ])

compile (comp {Γ} {Θ} {Θ′} {Δ} vars c k) = comp (encodeVars vars) (compile c) (Circ-++′ {Θ′} {Γ} (compile k))
