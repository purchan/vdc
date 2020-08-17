open import encprf public

Cr′⟦_⟧ : Circ Γ Δ → Vals (toBools Γ) → Vals (toBools Δ)

Cr′⟦ ret vars ⟧        bvals = lookup (encodeVars vars) bvals
Cr′⟦ oper {Γ} {τ} op ⟧ bvals = Cr⟦ encodeOp op ⟧ bvals
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

correctness (oper {.([ tri , tri ])} {.tri} andT) [ false , false , false , b₂₂   ] = refl
correctness (oper {.([ tri , tri ])} {.tri} andT) [ false , true  , false , b₂₂   ] = refl
correctness (oper {.([ tri , tri ])} {.tri} andT) [ false , false , true  , b₂₂   ] = refl
correctness (oper {.([ tri , tri ])} {.tri} andT) [ false , true  , true  , b₂₂   ] = refl
correctness (oper {.([ tri , tri ])} {.tri} andT) [ true  , false , false , false ] = refl
correctness (oper {.([ tri , tri ])} {.tri} andT) [ true  , true  , false , false ] = refl
correctness (oper {.([ tri , tri ])} {.tri} andT) [ true  , b₁₂   , false , true  ] = refl
correctness (oper {.([ tri , tri ])} {.tri} andT) [ true  , b₁₂   , true  , b₂₂   ] = refl

correctness (oper {.([ tri , tri ])} {.bool} ≡C) [ false , false , false , false ] = refl
correctness (oper {.([ tri , tri ])} {.bool} ≡C) [ false , false , false , true  ] = refl
correctness (oper {.([ tri , tri ])} {.bool} ≡C) [ false , true  , false , false ] = refl
correctness (oper {.([ tri , tri ])} {.bool} ≡C) [ false , true  , false , true  ] = refl
correctness (oper {.([ tri , tri ])} {.bool} ≡C) [ false , false , true  , b₂₂   ] = refl
correctness (oper {.([ tri , tri ])} {.bool} ≡C) [ false , true  , true  , b₂₂   ] = refl
correctness (oper {.([ tri , tri ])} {.bool} ≡C) [ true  , false , false , false ] = refl
correctness (oper {.([ tri , tri ])} {.bool} ≡C) [ true  , false , false , true  ] = refl
correctness (oper {.([ tri , tri ])} {.bool} ≡C) [ true  , true  , false , false ] = refl
correctness (oper {.([ tri , tri ])} {.bool} ≡C) [ true  , true  , false , true  ] = refl
correctness (oper {.([ tri , tri ])} {.bool} ≡C) [ true  , false , true  , false ] = refl
correctness (oper {.([ tri , tri ])} {.bool} ≡C) [ true  , false , true  , true  ] = refl
correctness (oper {.([ tri , tri ])} {.bool} ≡C) [ true  , true  , true  , false ] = refl
correctness (oper {.([ tri , tri ])} {.bool} ≡C) [ true  , true  , true  , true  ] = refl

correctness (oper {.([ bool , bool ])} {.bool} andB) [ b₁ , b₂ ] = refl
correctness (oper {.([ bool , bool ])} {.bool} orB)  [ b₁ , b₂ ] = refl
correctness (oper {.([ bool ])}        {.bool} notB) [ b ]       = refl

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
