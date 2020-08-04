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

look-∈-suf : (vr : σ ∈ Γ) (vals : Vals Γ) (vals′ : Vals Γ′)
            → look (∈-suf vr) (vals ++Vl vals′) ≡ look vr vals
look-∈-suf here       (σ ∷ _)    _     = refl
look-∈-suf (there pf) (_ ∷ vals) vals′ = look-∈-suf pf vals vals′

lookup-suf : (vars : Vars Γ Δ) (valΓ : Vals Γ) (valΓ′ : Vals Γ′)
           → lookup (sufVars Γ′ vars) (valΓ ++Vl valΓ′) ≡ lookup vars valΓ
lookup-suf {[]}     {Γ′ = Γ′} []          []          valΓ′ = refl
lookup-suf {σ ∷ σs} {Γ′ = Γ′} []          (vl ∷ vals) valΓ′ = refl
lookup-suf {σ ∷ σs} {Γ′ = Γ′} (vr ∷ vars) (vl ∷ vals) valΓ′ =
  begin
    lookup (sufVars Γ′ (vr ∷ vars)) ((vl ∷ vals) ++Vl valΓ′)
  ≡⟨ cong (_∷ lookup (sufVars Γ′ vars) (vl ∷ (vals ++Vl valΓ′))) (look-∈-suf vr (vl ∷ vals) valΓ′) ⟩
    look vr (vl ∷ vals) ∷ lookup (sufVars Γ′ vars) ((vl ∷ vals) ++Vl valΓ′)
  ≡⟨ cong (look vr (vl ∷ vals) ∷_) (lookup-suf vars (vl ∷ vals) valΓ′) ⟩
    look vr (vl ∷ vals) ∷ lookup vars (vl ∷ vals)
  ≡⟨⟩
    lookup (vr ∷ vars) (vl ∷ vals)
  ∎

lookup-sufini : (valΓ : Vals Γ) (valΓ′ : Vals Γ′)
              → lookup (sufVars Γ′ (iniVars Γ)) (valΓ ++Vl valΓ′) ≡ valΓ
lookup-sufini {Γ} {Γ′} valΓ valΓ′ =
  begin
    lookup (sufVars Γ′ (iniVars Γ)) (valΓ ++Vl valΓ′)
  ≡⟨ lookup-suf (iniVars Γ) valΓ valΓ′ ⟩
    lookup (iniVars Γ) valΓ
  ≡⟨ cong-app lookup-ini valΓ ⟩
    valΓ
  ∎

Circ′-++-≡ : (Γ′ : List Ty) (circ : Circ′ Γ Δ) (bvalΓ : Vals Γ) (bvalΓ′ : Vals Γ′)
           → Cr′⟦ Circ′-++ Γ′ circ ⟧ (bvalΓ ++Vl bvalΓ′) ≡ Cr′⟦ circ ⟧ bvalΓ
Circ′-++-≡ {Γ} {Δ} Γ′ circ bvalΓ bvalΓ′ =
  begin
    Cr′⟦ Circ′-++ Γ′ circ ⟧ (bvalΓ ++Vl bvalΓ′)
  ≡⟨⟩
    Cr′⟦ comp (sufVars Γ′ (iniVars Γ)) circ (ret (sufVars (Γ ++ Γ′) (iniVars Δ))) ⟧ (bvalΓ ++Vl bvalΓ′)
  ≡⟨⟩
    Cr′⟦ ret (sufVars (Γ ++ Γ′) (iniVars Δ)) ⟧ (Cr′⟦ circ ⟧ (lookup (sufVars Γ′ (iniVars Γ)) (bvalΓ ++Vl bvalΓ′)) ++Vl (bvalΓ ++Vl bvalΓ′))
  ≡⟨ cong (λ pf → Cr′⟦ ret (sufVars (Γ ++ Γ′) (iniVars Δ)) ⟧ (Cr′⟦ circ ⟧ pf ++Vl (bvalΓ ++Vl bvalΓ′))) (lookup-sufini bvalΓ bvalΓ′)  ⟩
    Cr′⟦ ret (sufVars (Γ ++ Γ′) (iniVars Δ)) ⟧ (Cr′⟦ circ ⟧  bvalΓ ++Vl (bvalΓ ++Vl bvalΓ′))
  ≡⟨⟩
    lookup (sufVars (Γ ++ Γ′) (iniVars Δ)) (Cr′⟦ circ ⟧ bvalΓ ++Vl (bvalΓ ++Vl bvalΓ′))
  ≡⟨ lookup-sufini (Cr′⟦ circ ⟧ bvalΓ) (bvalΓ ++Vl bvalΓ′) ⟩
    Cr′⟦ circ ⟧ bvalΓ
  ∎

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
    split-ri : (vals : Vals Γ) → splitVals (vals ++Vl []) ≡ ⟨ vals , ⟨ [] , refl ⟩ ⟩
    split-ri [] = refl
    split-ri (vl ∷ vals) rewrite split-ri vals = refl

    split-rc : (vals : Vals Γ) (vals₁ : Vals Θ) (vals₂ : Vals Θ′)
             → splitVals (vals ++Vl (vals₁ ++Vl vals₂)) ≡ ⟨ vals , ⟨ vals₁ ++Vl vals₂ , refl ⟩ ⟩
    split-rc []          vals₁ vals₂ = refl
    split-rc (vl ∷ vals) vals₁ vals₂ rewrite split-rc vals vals₁ vals₂ = refl

    split-bv : (σ : Ty) (σs : List Ty) (vl : Ty⟦ σ ⟧) (vals : Vals σs)
             → splitVals {toBool σ} {toBools σs} (encode σ vl ++Vl encodes σs vals) ≡ ⟨ encode σ vl , ⟨ encodes σs vals , refl ⟩ ⟩
    split-bv σ []        vl []           = split-ri (encode σ vl)
    split-bv σ (σ′ ∷ σs) vl (vl′ ∷ vals) = split-rc (encode σ vl) (encode σ′ vl′) (encodes σs vals)

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
