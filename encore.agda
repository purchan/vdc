open import encprf public

compile : Circ Γ Δ → Circ (toBools Γ) (toBools Δ)
compile (ret vars) = ret (encodeVars vars)
compile (oper op)  = encodeOp op
compile (comp {Γ} {Θ} {Θ′} {Δ} vars c pf k)
                   = comp (encodeVars vars) (compile c) (toBools-++ Θ′ Γ pf) (compile k)


correctness : (c : Circ Γ Δ) (bvals : Vals (toBools Γ))
            → Cr⟦ c ⟧ (decodes Γ bvals) ≡ decodes Δ (Cr⟦ compile c ⟧ bvals)
correctness {Γ} {τs} (ret vars) bvals =
  begin
    Cr⟦ ret vars ⟧ (decodes Γ bvals)
  ≡⟨⟩
    lookup vars (decodes Γ bvals)
  ≡⟨ lookup-dec vars bvals ⟩
    decodes τs (lookup (encodeVars vars) bvals)
  ≡⟨⟩
    decodes τs (Cr⟦ compile (ret vars) ⟧ bvals)
  ∎

correctness (oper andT) [ false , false , false , i₂₂   ] = refl
correctness (oper andT) [ false , true  , false , i₂₂   ] = refl
correctness (oper andT) [ false , false , true  , i₂₂   ] = refl
correctness (oper andT) [ false , true  , true  , i₂₂   ] = refl
correctness (oper andT) [ true  , false , false , false ] = refl
correctness (oper andT) [ true  , true  , false , false ] = refl
correctness (oper andT) [ true  , i₁₂   , false , true  ] = refl
correctness (oper andT) [ true  , i₁₂   , true  , i₂₂   ] = refl

correctness (oper orT) [ false , false , false , i₂₂   ] = refl
correctness (oper orT) [ false , true  , false , i₂₂   ] = refl
correctness (oper orT) [ false , false , true  , i₂₂   ] = refl
correctness (oper orT) [ false , true  , true  , i₂₂   ] = refl
correctness (oper orT) [ true  , i₁₂   , false , false ] = refl
correctness (oper orT) [ true  , false , false , true  ] = refl
correctness (oper orT) [ true  , true  , false , true  ] = refl
correctness (oper orT) [ true  , i₁₂   , true  , i₂₂   ] = refl

correctness (oper ≡C) [ false , false , false , false ] = refl
correctness (oper ≡C) [ false , false , false , true  ] = refl
correctness (oper ≡C) [ false , true  , false , false ] = refl
correctness (oper ≡C) [ false , true  , false , true  ] = refl
correctness (oper ≡C) [ false , false , true  , i₂₂   ] = refl
correctness (oper ≡C) [ false , true  , true  , i₂₂   ] = refl
correctness (oper ≡C) [ true  , false , false , false ] = refl
correctness (oper ≡C) [ true  , false , false , true  ] = refl
correctness (oper ≡C) [ true  , true  , false , false ] = refl
correctness (oper ≡C) [ true  , true  , false , true  ] = refl
correctness (oper ≡C) [ true  , false , true  , false ] = refl
correctness (oper ≡C) [ true  , false , true  , true  ] = refl
correctness (oper ≡C) [ true  , true  , true  , false ] = refl
correctness (oper ≡C) [ true  , true  , true  , true  ] = refl

correctness (oper andB) [ i₁ , i₂ ] = refl
correctness (oper orB)  [ i₁ , i₂ ] = refl
correctness (oper notB) [ i ]       = refl

correctness (comp {Γ} {Θ} {Θ′} {Δ} vars c {Γ′} pf k) bvals =
  begin
    Cr⟦ comp vars c pf k ⟧ (decodes Γ bvals)
  ≡⟨⟩
    Cr⟦ k ⟧ (++Vlp (Cr⟦ c ⟧ (lookup vars (decodes Γ bvals))) (decodes Γ bvals) pf)
  ≡⟨ cong (λ{pf′ → Cr⟦ k ⟧ (++Vlp (Cr⟦ c ⟧ pf′) (decodes Γ bvals) pf)}) (lookup-dec vars bvals) ⟩
    Cr⟦ k ⟧ (++Vlp (Cr⟦ c ⟧ (decodes Θ leb)) (decodes Γ bvals) pf)
  ≡⟨ cong (λ{pf′ → Cr⟦ k ⟧ (++Vlp pf′ (decodes Γ bvals) pf)}) (correctness c leb) ⟩
    Cr⟦ k ⟧ (++Vlp (decodes Θ′ bvalΘ′) (decodes Γ bvals) pf)
  ≡⟨ cong Cr⟦ k ⟧ (decs-++Vlp {Θ′} {Γ} bvalΘ′ bvals pf tBpf) ⟩
    Cr⟦ k ⟧ (decodes Γ′ (++Vlp bvalΘ′ bvals tBpf))
  ≡⟨ correctness k (++Vlp bvalΘ′ bvals tBpf) ⟩
    decodes Δ (Cr⟦ compile k ⟧ (++Vlp bvalΘ′ bvals tBpf))
  ≡⟨⟩
    decodes Δ (Cr⟦ compile (comp vars c pf k) ⟧ bvals)
  ∎
  where leb    = lookup (encodeVars vars) bvals
        bvalΘ′ = Cr⟦ compile c ⟧ leb

        tBpf = toBools-++ Θ′ Γ pf
