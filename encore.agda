open import encprf public

compile : Circ Γ Δ → Circ′ Γ Δ
compile (ret vars)      = ret vars
compile (oper op)       = oper op
compile (comp vars c k) = comp vars (compile c) (compile k)


correctness : (c : Circ Γ Δ) (bvals : Vals (toBools Γ))
            → Cr⟦ c ⟧ (decodes Γ bvals) ≡ decodes Δ (Cr′⟦ compile c ⟧ bvals)
correctness {Γ} {τs} (ret vars) bvals =
  begin
    Cr⟦ ret vars ⟧ (decodes Γ bvals)
  ≡⟨⟩
    lookup vars (decodes Γ bvals)
  ≡⟨ lookup-dec vars bvals ⟩
    decodes τs (lookup (encodeVars vars) bvals)
  ≡⟨⟩
    decodes τs (Cr′⟦ compile (ret vars) ⟧ bvals)
  ∎

correctness (oper {Γ} {τ} op) bvals =
  begin
    Cr⟦ oper op ⟧ (decodes Γ bvals)
  ≡⟨⟩
    [ Op⟦ op ⟧ (decodes Γ bvals) ]
  ≡⟨ sym (decs-encs {[ τ ]} [ Op⟦ op ⟧ (decodes Γ bvals) ]) ⟩
    decodes [ τ ] (encodes [ τ ] [ Op⟦ op ⟧ (decodes Γ bvals) ])
  ≡⟨⟩
    decodes [ τ ] (Cr′⟦ compile (oper op) ⟧ bvals)
  ∎

correctness (comp {Γ} {Θ} {Θ′} {Δ} vars c k) bvals =
  begin
    Cr⟦ comp vars c k ⟧ (decodes Γ bvals)
  ≡⟨⟩
    Cr⟦ k ⟧ (Cr⟦ c ⟧ (lookup vars (decodes Γ bvals)) ++Vl decodes Γ bvals)
  ≡⟨ cong (λ{pf → Cr⟦ k ⟧ (Cr⟦ c ⟧ pf ++Vl decodes Γ bvals)}) (lookup-dec vars bvals) ⟩
    Cr⟦ k ⟧ (Cr⟦ c ⟧ (decodes Θ leb) ++Vl decodes Γ bvals)
  ≡⟨ cong (λ{pf → Cr⟦ k ⟧ (pf ++Vl decodes Γ bvals)}) (correctness c leb) ⟩
    Cr⟦ k ⟧ (decodes Θ′ bvalΘ′ ++Vl decodes Γ bvals)
  ≡⟨ cong Cr⟦ k ⟧ (decs-++Vl {Θ′} {Γ} bvalΘ′ bvals) ⟩
    Cr⟦ k ⟧ (decodes (Θ′ ++ Γ) (_++bVl_ {Θ′} {Γ} bvalΘ′ bvals))
  ≡⟨ correctness k (_++bVl_ {Θ′} {Γ} bvalΘ′ bvals) ⟩
    decodes Δ (Cr′⟦ compile k ⟧ (_++bVl_ {Θ′} {Γ} bvalΘ′ bvals))
  ≡⟨⟩
    decodes Δ (Cr′⟦ compile (comp vars c k) ⟧ bvals)
  ∎
  where leb = lookup (encodeVars vars) bvals
        bvalΘ′ = Cr′⟦ compile c ⟧ leb
