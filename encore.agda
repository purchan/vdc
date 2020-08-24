open import encprf public
{-
Cr′⟦_⟧ : Circ Γ Δ → Vals (toBools Γ) → Vals (toBools Δ)

Cr′⟦ ret vars ⟧        bvals = lookup (encodeVars vars) bvals
Cr′⟦ oper {Γ} {τ} op ⟧ bvals = Cr⟦ encodeOp op ⟧ bvals
Cr′⟦ comp {Γ} {Θ} {Θ′} {Δ} vars c k ⟧ bvals =
  Cr′⟦ k ⟧ (_++bVl_ {Θ′} {Γ} bvalΘ′ bvals)
  where bvalΘ′ = Cr′⟦ c ⟧ (lookup (encodeVars vars) bvals)
-}
postulate
  cc : (pf : Γ′ ≡ Θ′ ++ Γ) → toBools Γ′ ≡ toBools Θ′ ++ toBools Γ

  decs-++Vl′ : (bvalΘ′ : Vals (toBools Θ′)) (bvals : Vals (toBools Γ))
           → (pf : Γ′ ≡ Θ′ ++ Γ) (pf′ : toBools Γ′ ≡ toBools Θ′ ++ toBools Γ)
           → ++Vl′ (decodes Θ′ bvalΘ′) (decodes Γ bvals) pf
           ≡ decodes Γ′ (++Vl′ bvalΘ′ bvals pf′)


compile : Circ Γ Δ → Circ (toBools Γ) (toBools Δ)
compile (ret vars) = ret (encodeVars vars)
compile (oper op) = encodeOp op
compile (comp {Γ} {Θ} {Θ′} {Δ} vars c pf k) = comp (encodeVars vars) (compile c) (cc {Θ′ = Θ′} {Γ = Γ} pf) (compile k)


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

correctness (comp {Γ} {Θ} {Θ′} {Δ} vars c {Γ′} pf k) bvals =
  begin
    Cr⟦ comp vars c pf k ⟧ (decodes Γ bvals)
  ≡⟨⟩
    Cr⟦ k ⟧ (++Vl′ (Cr⟦ c ⟧ (lookup vars (decodes Γ bvals))) (decodes Γ bvals) pf)
  ≡⟨ cong (λ{pf′ → Cr⟦ k ⟧ (++Vl′ (Cr⟦ c ⟧ pf′) (decodes Γ bvals) pf)}) (lookup-dec vars bvals) ⟩
    Cr⟦ k ⟧ (++Vl′ (Cr⟦ c ⟧ (decodes Θ leb)) (decodes Γ bvals) pf)
  ≡⟨ cong (λ{pf′ → Cr⟦ k ⟧ (++Vl′ pf′ (decodes Γ bvals) pf)}) (correctness c leb) ⟩
    Cr⟦ k ⟧ (++Vl′ (decodes Θ′ bvalΘ′) (decodes Γ bvals) pf)
  ≡⟨ cong Cr⟦ k ⟧ (decs-++Vl′ {Θ′} {Γ} bvalΘ′ bvals pf (cc {Γ′} {Θ′} {Γ} pf)) ⟩
    Cr⟦ k ⟧ (decodes Γ′  (++Vl′ bvalΘ′ bvals (cc {Γ′} {Θ′} {Γ} pf)))
  ≡⟨ correctness k (++Vl′ bvalΘ′ bvals (cc {Γ′} {Θ′} {Γ} pf)) ⟩
    decodes Δ (Cr⟦ compile k ⟧ (++Vl′ bvalΘ′ bvals (cc {Γ′} {Θ′} {Γ} pf)))
  ≡⟨⟩
    decodes Δ (Cr⟦ compile (comp vars c pf k) ⟧ bvals)
  ∎
  where leb = lookup (encodeVars vars) bvals
        bvalΘ′ = Cr⟦ compile c ⟧ leb
