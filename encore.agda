open import enclib public

Circ′-++ : (Γ′ : List Ty) → Circ′ Γ Δ → Circ′ (Γ ++ Γ′) Δ

compile : Circ Γ Δ → Circ′ (toBools Γ) (toBools Δ)

------------------------
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

------------------------
postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g
  ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀(x : A) → B x}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

Circ′-++-≡ : (Γ′ : List Ty) (circ : Circ′ Γ Δ) (bval : Vals Γ) (bvalΓ′ : Vals Γ′)
           → Cr′⟦ Circ′-++ Γ′ circ ⟧ (bval ++Vl bvalΓ′) ≡ Cr′⟦ circ ⟧ bval
Circ′-++-≡ Γ′ circ bval bvalΓ′ =
  begin
    Cr′⟦ Circ′-++ Γ′ circ ⟧ (bval ++Vl bvalΓ′)
  ≡⟨ {!!} ⟩
    Cr′⟦ circ ⟧ bval
  ∎

lookup-mapThere : (vars : Vars Γ Δ) (vl : Ty⟦ τ ⟧) (vals : Vals Γ)
                → lookup (mapThere vars) (vl ∷ vals) ≡ lookup vars vals
lookup-mapThere []          vl vals = refl
lookup-mapThere (vr ∷ vars) vl vals =
  begin
    lookup (mapThere (vr ∷ vars)) (vl ∷ vals)
  ≡⟨⟩
    lookup (there vr ∷ mapThere vars) (vl ∷ vals)
  ≡⟨⟩
    look vr vals ∷ lookup (mapThere vars) (vl ∷ vals)
  ≡⟨ cong (look vr vals ∷_) (lookup-mapThere vars vl vals) ⟩
    lookup (vr ∷ vars) vals
  ∎

lookup-ini : lookup (iniVars Γ) ≡ id
lookup-ini {[]}     = extensionality λ{[] → refl}
lookup-ini {σ ∷ σs} = extensionality λ{(vl ∷ vals) →
  begin
    lookup (iniVars (σ ∷ σs)) (vl ∷ vals)
  ≡⟨⟩
    lookup (here ∷ mapThere (iniVars σs)) (vl ∷ vals)
  ≡⟨⟩
    vl ∷ lookup (mapThere (iniVars σs)) (vl ∷ vals)
  ≡⟨ cong (vl ∷_) (lookup-mapThere (iniVars σs) vl vals) ⟩
    vl ∷ lookup (iniVars σs) vals
  ≡⟨ cong (vl ∷_) (cong-app (lookup-ini {σs}) vals) ⟩
    id (vl ∷ vals)
  ∎}

dec∘enc : decode τ ∘ encode τ ≡ id
dec∘enc {bool} = extensionality λ{b → refl}
dec∘enc {tri } = extensionality λ{ true  → refl
                                 ; false → refl
                                 ; dc    → refl
                                 }

dec∘enc-s : decodes τs ∘ encodes τs ≡ id
dec∘enc-s {[]}     = extensionality λ{[] → refl}
dec∘enc-s {σ ∷ σs} = extensionality λ{(vl ∷ vals) → pf σ σs vl vals}
  where
    split-bv : (σ : Ty) (σs : List Ty) (vl : Ty⟦ σ ⟧) (vals : Vals σs)
             → splitVals {toBool σ} {toBools σs} (encode σ vl ++Vl encodes σs vals) ≡ ⟨ encode σ vl , ⟨ encodes σs vals , refl ⟩ ⟩
    split-bv σ σs vl vals = {!!}

    pf : (σ : Ty) (σs : List Ty) (vl : Ty⟦ σ ⟧ ) (vals : Vals σs)
       → (decodes (σ ∷ σs) ∘ (encodes (σ ∷ σs))) (vl ∷ vals) ≡ vl ∷ vals
    pf σ σs vl vals rewrite split-bv σ σs vl vals =
      begin
        decode σ (encode σ vl) ∷ decodes′ σs (encodes σs vals) (toVals′ σs (encodes σs vals))
      ≡⟨ cong (_∷ decodes′ σs (encodes σs vals) (toVals′ σs (encodes σs vals))) (cong-app dec∘enc vl) ⟩
        vl ∷ decodes′ σs (encodes σs vals) (toVals′ σs (encodes σs vals))
      ≡⟨ cong (vl ∷_) (cong-app dec∘enc-s vals) ⟩
        id (vl ∷ vals)
      ∎

dec∘enc-Crd : decodes Γ ∘ Cr′⟦ comp (iniVars (toBools Γ)) (dec Γ) (Circ′-++ (toBools Γ) (enc Γ)) ⟧ ≡ decodes Γ
dec∘enc-Crd {Γ} = extensionality λ{bvals →
  begin
    (decodes Γ ∘ Cr′⟦ comp (iniVars (toBools Γ)) (dec Γ) (Circ′-++ (toBools Γ) (enc Γ)) ⟧) bvals
  ≡⟨⟩
    (decodes Γ ∘ Cr′⟦ Circ′-++ (toBools Γ) (enc Γ) ⟧) (Cr′⟦ dec Γ ⟧ (lookup (iniVars (toBools Γ)) bvals) ++Vl bvals)
  ≡⟨ cong (decodes Γ)
     (Circ′-++-≡ (toBools Γ) (enc Γ) (Cr′⟦ dec Γ ⟧ (lookup (iniVars (toBools Γ)) bvals)) bvals) ⟩
    (decodes Γ ∘ Cr′⟦ enc Γ ⟧) (Cr′⟦ dec Γ ⟧ (lookup (iniVars (toBools Γ)) bvals))
  ≡⟨⟩
    (decodes Γ ∘ encodes Γ) (decodes Γ (lookup (iniVars (toBools Γ)) bvals))
  ≡⟨ cong-app dec∘enc-s ((decodes Γ (lookup (iniVars (toBools Γ)) bvals))) ⟩
    (decodes Γ ∘ lookup (iniVars (toBools Γ))) bvals
  ≡⟨ cong (decodes Γ) (cong-app lookup-ini bvals) ⟩
    decodes Γ bvals
  ∎
  }

correctness c bvals = {!!}
