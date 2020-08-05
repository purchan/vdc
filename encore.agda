open import encprf public

Circ′-toBools-++ : Circ′ (toBools (Γ ++ Γ′)) Δ ≡ Circ′ (toBools Γ ++ toBools Γ′) Δ
Circ′-toBools-++ {Γ} {Γ′} rewrite toBools-++ {Γ} {Γ′} = refl

compile : Circ Γ Δ → Circ′ (toBools Γ) (toBools Δ)
compile (ret vars)        = ret (encodeVars vars)
compile (oper {Γ} {τ} op) = comp pick O∘D (sufCirc′ (toBools Γ) (enc [ τ ]))
                          where pick = iniVars (toBools Γ)
                                O∘D  = comp pick (dec Γ) (sufCirc′ (toBools Γ) (oper op))
compile (comp {Γ} {Θ} {Θ′} {Δ} vars c k) = comp (encodeVars vars) (compile c) (subst id pf (compile k))
                                         where pf = Circ′-toBools-++ {Θ′} {Γ} {toBools Δ}

correctness : (c : Circ Γ Δ) (bvals : Vals (toBools Γ))
            → Cr⟦ c ⟧ (decodes Γ bvals) ≡ decodes Δ (Cr′⟦ compile c ⟧ bvals)

correctness              (ret [])          bvals = refl
correctness {Γ} {τ ∷ τs} (ret (vr ∷ vars)) bvals =
  begin
    Cr⟦ ret (vr ∷ vars) ⟧ (decodes Γ bvals)
  ≡⟨⟩
    lookup (vr ∷ vars) (decodes Γ bvals)
  ≡⟨⟩
    look vr (decodes Γ bvals) ∷ lookup vars (decodes Γ bvals)
  ≡⟨ cong (look vr (decodes Γ bvals) ∷_) (correctness (ret vars) bvals) ⟩
    look vr (decodes Γ bvals) ∷ decodes τs (lookup (encodeVars vars) bvals)
  ≡⟨ cong (_∷ decodes τs (lookup (encodeVars vars) bvals)) (look-dec vr bvals) ⟩
    decode τ (lookup (encodeVar vr) bvals) ∷ decodes τs (lookup (encodeVars vars) bvals)
  ≡⟨ dec-s-lookup (encodeVar vr) (encodeVars vars) bvals ⟩
    decodes (τ ∷ τs) (lookup (encodeVars (vr ∷ vars)) bvals)
  ≡⟨⟩
    decodes (τ ∷ τs) (Cr′⟦ ret (encodeVars (vr ∷ vars)) ⟧ bvals)
  ∎

correctness (oper {Γ} {τ} op) bvals =
  begin
    Cr⟦ oper op ⟧ (decodes Γ bvals)
  ≡⟨⟩
    Op⟦ op ⟧ (decodes Γ bvals) ∷ []
  ≡⟨⟩
    Cr′⟦ oper op ⟧ (Cr′⟦ dec Γ ⟧ bvals)
  ≡⟨ cong (λ{pf → Cr′⟦ oper op ⟧ (Cr′⟦ dec Γ ⟧ pf)}) (cong-app (sym (lookup-ini)) bvals) ⟩
    Cr′⟦ oper op ⟧ (Cr′⟦ dec Γ ⟧ (lookup pick bvals))
  ≡⟨ sym (Circ′-++-≡ (toBools Γ) (oper op) (Cr′⟦ dec Γ ⟧ (lookup pick bvals)) bvals) ⟩
    Cr′⟦ sufCirc′ (toBools Γ) (oper op) ⟧ (Cr′⟦ dec Γ ⟧ (lookup pick bvals) ++Vl bvals)
  ≡⟨⟩
    Cr′⟦ O∘D ⟧ bvals
  ≡⟨ cong-app (sym dec∘enc-s) (Cr′⟦ O∘D ⟧ bvals) ⟩
    decodes [ τ ] (encodes [ τ ] (Cr′⟦ O∘D ⟧ bvals))
  ≡⟨⟩
    decodes [ τ ] (Cr′⟦ enc [ τ ] ⟧ (Cr′⟦ O∘D ⟧ bvals))
  ≡⟨ cong (λ{pf → decodes [ τ ] (Cr′⟦ enc [ τ ] ⟧ (Cr′⟦ O∘D ⟧ pf))}) (cong-app (sym (lookup-ini)) bvals) ⟩
    decodes [ τ ] (Cr′⟦ enc [ τ ] ⟧ (Cr′⟦ O∘D ⟧ (lookup pick bvals)))
  ≡⟨ cong (decodes [ τ ]) (sym (Circ′-++-≡ (toBools Γ) (enc [ τ ]) (Cr′⟦ O∘D ⟧ (lookup pick bvals)) (bvals))) ⟩
    decodes [ τ ] (Cr′⟦ sufCirc′ (toBools Γ) (enc [ τ ]) ⟧ (Cr′⟦ O∘D ⟧ (lookup pick bvals) ++Vl bvals))
  ≡⟨⟩
    decodes [ τ ] (Cr′⟦ comp pick O∘D (sufCirc′ (toBools Γ) (enc [ τ ])) ⟧ bvals)
  ∎
  where pick = iniVars (toBools Γ)
        O∘D  = comp pick (dec Γ) (sufCirc′ (toBools Γ) (oper op))

correctness (comp {Γ} {Θ} {Θ′} {Δ} vars c k) bvals =
  begin
    Cr⟦ comp vars c k ⟧ (decodes Γ bvals)
  ≡⟨⟩
    Cr⟦ k ⟧ (Cr⟦ c ⟧ (lookup vars (decodes Γ bvals)) ++Vl (decodes Γ bvals))
  ≡⟨ {!!} ⟩
    decodes Δ (Cr′⟦ (subst id pf (compile k))⟧ (Cr′⟦ compile c ⟧ (lookup (encodeVars vars) bvals) ++Vl bvals))
  ≡⟨⟩
    decodes Δ (Cr′⟦ comp (encodeVars vars) (compile c) (subst id pf (compile k))⟧ bvals)
  ∎
  where pf = Circ′-toBools-++ {Θ′} {Γ} {toBools Δ}
