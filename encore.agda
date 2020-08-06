open import encprf public

compile : Circ Γ Δ → Circ′ Γ Δ
compile (ret vars)      = ret vars
compile (oper op)       = oper op
compile (comp vars c k) = comp vars (compile c) (compile k)


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
    decodes (τ ∷ τs) (Cr′⟦ compile (ret (vr ∷ vars)) ⟧ bvals)
  ∎

correctness (oper {Γ} {τ} op) bvals =
  begin
    Cr⟦ oper op ⟧ (decodes Γ bvals)
  ≡⟨⟩
    [ Op⟦ op ⟧ (decodes Γ bvals) ]
  ≡⟨ sym (cong-app (dec∘enc-s {[ τ ]}) [ Op⟦ op ⟧ (decodes Γ bvals) ]) ⟩
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
  ≡⟨ cong Cr⟦ k ⟧ (decodes-++Vl {Θ′} {Γ} bvalΘ′ bvals) ⟩
    Cr⟦ k ⟧ (decodes (Θ′ ++ Γ) (_++bVl_ {Θ′} {Γ} bvalΘ′ bvals))
  ≡⟨ correctness k (_++bVl_ {Θ′} {Γ} bvalΘ′ bvals) ⟩
    decodes Δ (Cr′⟦ compile k ⟧ (_++bVl_ {Θ′} {Γ} bvalΘ′ bvals))
  ≡⟨⟩
    decodes Δ (Cr′⟦ compile (comp vars c k) ⟧ bvals)
  ∎
  where leb = lookup (encodeVars vars) bvals
        bvalΘ′ = Cr′⟦ compile c ⟧ leb

        ++Vl-++bVl : {σ : Ty} {σs Γ′ : List Ty}
                   → (bvalσ : Vals (toBool σ)) (bvalσs : Vals (toBools σs)) (bvalΓ′ : Vals (toBools Γ′))
                   → bvalσ ++Vl (_++bVl_ {σs} {Γ′} bvalσs bvalΓ′)
                   ≡ _++bVl_ {σ ∷ σs} {Γ′} (bvalσ ++Vl bvalσs) bvalΓ′
        ++Vl-++bVl {σ} {σs} {Γ′} bvalσ bvalσs bvalΓ′ = {!!}

          -- sym (trans (trans pf₁ pf₂) pf₃)
          {-
          where pf₁ = cong Vals (sym (toBools-++ {σ ∷ σs} {Γ′}))
                -- Vals (toBools (σ ∷ σs ++ Γ′)) ≡ Vals (toBools (σ ∷ σs) ++ toBools Γ′)
                pf₂ = cong Vals (++-assoc (toBool σ) (toBools σs) (toBools Γ′))
                -- Vals ((toBool σ ++ toBools σs) ++ toBools Γ′) ≡ Vals (toBool σ ++ toBools σs ++ toBools Γ′)
                pf₃ = cong (λ{pf → Vals (toBool σ ++ pf)}) ((toBools-++ {σs} {Γ′}))
                -- Vals (toBool σ ++ toBools σs ++ toBools Γ′) ≡ Vals (toBool σ ++ toBools (σs ++ Γ′))
          -}

        decodes-++Vl : {Γ Γ′ : List Ty}
                     → (bvalΓ : Vals (toBools Γ)) (bvalΓ′ : Vals (toBools Γ′))
                     → decodes Γ bvalΓ ++Vl decodes Γ′ bvalΓ′
                     ≡ decodes (Γ ++ Γ′) (_++bVl_ {Γ} {Γ′} bvalΓ bvalΓ′)

        decodes-++Vl {[]}     {Γ′} []    bvalΓ′ = refl
        decodes-++Vl {σ ∷ σs} {Γ′} bvalΓ                bvalΓ′ with splitVals {toBool σ} {toBools σs} bvalΓ
        decodes-++Vl {σ ∷ σs} {Γ′} .(bvalσ ++Vl bvalσs) bvalΓ′    | ⟨ bvalσ , ⟨ bvalσs , refl ⟩ ⟩
          rewrite decodes-++Vl {σs} {Γ′} bvalσs bvalΓ′
                | decode-++Vl {σ} {σs ++ Γ′} bvalσ (_++bVl_ {σs} {Γ′} bvalσs bvalΓ′)
                | ++Vl-++bVl {σ} {σs} {Γ′} bvalσ bvalσs bvalΓ′ = refl
