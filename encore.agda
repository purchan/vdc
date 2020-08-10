open import encprf public

Cr′⟦_⟧ : Circ Γ Δ → Vals (toBools Γ) → Vals (toBools Δ)

Cr′⟦ ret vars ⟧        bvals = lookup (encodeVars vars) bvals
Cr′⟦ oper {Γ} {τ} op ⟧ bvals = encodes [ τ ] [ Op⟦ op ⟧ (decodes Γ bvals) ]
Cr′⟦ comp {Γ} {Θ} {Θ′} {Δ} vars c k ⟧ bvals =
  Cr′⟦ k ⟧ (_++bVl_ {Θ′} {Γ} bvalΘ′ bvals)
  where bvalΘ′ = Cr′⟦ c ⟧ (lookup (encodeVars vars) bvals)


correctness : (c : Circ Γ Δ) (bvals : Vals (toBools Γ))
            → Cr⟦ c ⟧ (decodes Γ bvals) ≡ decodes Δ (Cr′⟦ c ⟧ bvals)
correctness {Γ} {τs} (ret vars) bvals =
  begin
    Cr⟦ ret vars ⟧ (decodes Γ bvals)
  ≡⟨⟩
    lookup vars (decodes Γ bvals)
  ≡⟨ lookup-dec vars bvals ⟩
    decodes τs (lookup (encodeVars vars) bvals)
  ≡⟨⟩
    decodes τs (Cr′⟦ ret vars ⟧ bvals)
  ∎

correctness (oper {Γ} {τ} op) bvals =
  begin
    Cr⟦ oper op ⟧ (decodes Γ bvals)
  ≡⟨⟩
    [ Op⟦ op ⟧ (decodes Γ bvals) ]
  ≡⟨ sym (decs-encs {[ τ ]} [ Op⟦ op ⟧ (decodes Γ bvals) ]) ⟩
    decodes [ τ ] (encodes [ τ ] [ Op⟦ op ⟧ (decodes Γ bvals) ])
  ≡⟨⟩
    decodes [ τ ] (Cr′⟦ oper op ⟧ bvals)
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
    decodes Δ (Cr′⟦ k ⟧ (_++bVl_ {Θ′} {Γ} bvalΘ′ bvals))
  ≡⟨⟩
    decodes Δ (Cr′⟦ comp vars c k ⟧ bvals)
  ∎
  where leb = lookup (encodeVars vars) bvals
        bvalΘ′ = Cr′⟦ c ⟧ leb
