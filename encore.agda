open import enclib public

Circ′-++ : (Γ′ : List Ty) → Circ′ Γ Δ → Circ′ (Γ ++ Γ′) Δ
Circ′-++ {Γ} {Δ} Γ′ circ = comp pick₁ circ (ret pick₂)
                         where pick₁ = sufVars Γ′ (iniVars Γ)
                               pick₂ = sufVars (Γ ++ Γ′) (iniVars Δ)

Circ′-toBools-++ : Circ′ (toBools (Γ ++ Γ′)) Δ ≡ Circ′ (toBools Γ ++ toBools Γ′) Δ
Circ′-toBools-++ {Γ} {Γ′} rewrite toBools-++ {Γ} {Γ′} = refl

compile : Circ Γ Δ → Circ′ (toBools Γ) (toBools Δ)
compile (ret vars)        = ret (encodeVars vars)
compile (oper {Γ} {τ} op) = comp pick O∘D (Circ′-++ (toBools Γ) (enc [ τ ]))
                          where pick = iniVars (toBools Γ)
                                O∘D  = comp pick (dec Γ) (Circ′-++ (toBools Γ) (oper op))
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

split-ri : (vals : Vals Γ) → splitVals (vals ++Vl []) ≡ ⟨ vals , ⟨ [] , refl ⟩ ⟩
split-ri [] = refl
split-ri (vl ∷ vals) rewrite split-ri vals = refl

split-rc : (vals : Vals Γ) (vals₁ : Vals Θ) (vals₂ : Vals Θ′)
         → splitVals (vals ++Vl (vals₁ ++Vl vals₂)) ≡ ⟨ vals , ⟨ vals₁ ++Vl vals₂ , refl ⟩ ⟩
split-rc []          vals₁ vals₂ = refl
split-rc (vl ∷ vals) vals₁ vals₂ rewrite split-rc vals vals₁ vals₂ = refl

split-bv : (σ : Ty) (σs : List Ty) (vl : Ty⟦ σ ⟧) (vals : Vals σs)
         → splitVals {toBool σ} {toBools σs} (encode σ vl ++Vl encodes σs vals)
         ≡ ⟨ encode σ vl , ⟨ encodes σs vals , refl ⟩ ⟩
split-bv σ []        vl []           = split-ri (encode σ vl)
split-bv σ (σ′ ∷ σs) vl (vl′ ∷ vals) = split-rc (encode σ vl) (encode σ′ vl′) (encodes σs vals)

split-bv′ : (σ : Ty) (σs : List Ty) (bval : Vals (toBool σ)) (bvals : Vals (toBools σs))
          → splitVals {toBool σ} {toBools σs} (bval ++Vl bvals)
          ≡ ⟨ bval , ⟨ bvals , refl ⟩ ⟩
split-bv′ σ []        bval []    = split-ri bval
split-bv′ σ (σ′ ∷ σs) bval bvals                 with splitVals {toBool σ′} {toBools σs} bvals
split-bv′ σ (σ′ ∷ σs) bval .(bvalσ′ ++Vl bvalσs) | ⟨ bvalσ′ , ⟨ bvalσs , refl ⟩ ⟩ = split-rc bval bvalσ′ bvalσs

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

lookup-pre : (vars : Vars Γ Δ) (valΓ : Vals Γ) (valΓ′ : Vals Γ′)
           → lookup (preVars Γ′ vars) (valΓ′ ++Vl valΓ) ≡ lookup vars valΓ
lookup-pre               vars valΓ []           = refl
lookup-pre {Γ′ = τ ∷ τs} vars valΓ (vl ∷ valΓ′) =
  begin
    lookup (preVars (τ ∷ τs) vars) ((vl ∷ valΓ′) ++Vl valΓ)
  ≡⟨ lookup-mapThere (preVars τs vars) vl (valΓ′ ++Vl valΓ) ⟩
    lookup (preVars τs vars) (valΓ′ ++Vl valΓ)
  ≡⟨ lookup-pre vars valΓ valΓ′ ⟩
    lookup vars valΓ
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

------------------------
look-dec : (vr : σ ∈ Γ) (bvals : Vals (toBools Γ))
         → look vr (decodes Γ bvals) ≡ decode σ (lookup (encodeVar vr) bvals)
look-dec {σ} {σ ∷ σs} here bvals               with splitVals {toBool σ} {toBools σs} bvals
look-dec {σ} {σ ∷ σs} here .(bvalσ ++Vl bvalσs)   | ⟨ bvalσ , ⟨ bvalσs , refl ⟩ ⟩
  rewrite lookup-sufini bvalσ bvalσs = refl

look-dec {σ} {x ∷ σs} (there l) bvals                with encodeVar {σ} {σs} l | inspect (encodeVar {σ} {σs}) l | splitVals {toBool x} {toBools σs} bvals
look-dec {σ} {x ∷ σs} (there l) .(bvalx ++Vl bvalσs) | evar                    | In[ pf ]                       | ⟨ bvalx , ⟨ bvalσs , refl ⟩ ⟩ =
  begin
    look l (decodes σs bvalσs)
  ≡⟨ trans (look-dec l bvalσs) (cong (λ{evar → decode σ (lookup evar bvalσs)}) pf) ⟩
    decode σ (lookup evar bvalσs)
  ≡⟨ cong (decode σ) (sym (lookup-pre evar bvalσs bvalx)) ⟩
    decode σ (lookup (preVars (toBool x) evar) (bvalx ++Vl bvalσs))
  ∎


lookup-++Vr : (vars₁ : Vars Γ Δ) (vars₂ : Vars Γ Δ′) (vals : Vals Γ)
            → lookup vars₁ vals ++Vl lookup vars₂ vals ≡ lookup (vars₁ ++Vr vars₂) vals
lookup-++Vr []           vars₂ vals = refl
lookup-++Vr (vr ∷ vars₁) vars₂ vals rewrite lookup-++Vr vars₁ vars₂ vals = refl

decode-++Vl : (bvalσ : Vals (toBool σ)) (bvalσs : Vals (toBools σs))
            → decode σ bvalσ ∷ decodes σs bvalσs ≡ decodes (σ ∷ σs) (bvalσ ++Vl bvalσs)
decode-++Vl {σ} {σs} bvalσ bvalσs rewrite split-bv′ σ σs bvalσ bvalσs = refl


dec-s-lookup : (vars₁ : Vars Γ (toBool σ)) (vars₂ : Vars Γ (toBools σs)) (vals : Vals Γ)
             → decode σ (lookup vars₁ vals) ∷ decodes σs (lookup vars₂ vals)
             ≡ decodes (σ ∷ σs) (lookup (vars₁ ++Vr vars₂) vals)
dec-s-lookup {Γ} {σ} {σs} vars₁ vars₂ vals =
  begin
    decode σ (lookup vars₁ vals) ∷ decodes σs (lookup vars₂ vals)
  ≡⟨ decode-++Vl (lookup vars₁ vals) (lookup vars₂ vals) ⟩
    decodes (σ ∷ σs) (lookup vars₁ vals ++Vl lookup vars₂ vals)
  ≡⟨ cong (decodes (σ ∷ σs)) (lookup-++Vr vars₁ vars₂ vals) ⟩
    decodes (σ ∷ σs) (lookup (vars₁ ++Vr vars₂) vals)
  ∎
------------------------
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
    Cr′⟦ Circ′-++ (toBools Γ) (oper op) ⟧ (Cr′⟦ dec Γ ⟧ (lookup pick bvals) ++Vl bvals)
  ≡⟨⟩
    Cr′⟦ O∘D ⟧ bvals
  ≡⟨ cong-app (sym dec∘enc-s) (Cr′⟦ O∘D ⟧ bvals) ⟩
    decodes [ τ ] (encodes [ τ ] (Cr′⟦ O∘D ⟧ bvals))
  ≡⟨⟩
    decodes [ τ ] (Cr′⟦ enc [ τ ] ⟧ (Cr′⟦ O∘D ⟧ bvals))
  ≡⟨ cong (λ{pf → decodes [ τ ] (Cr′⟦ enc [ τ ] ⟧ (Cr′⟦ O∘D ⟧ pf))}) (cong-app (sym (lookup-ini)) bvals) ⟩
    decodes [ τ ] (Cr′⟦ enc [ τ ] ⟧ (Cr′⟦ O∘D ⟧ (lookup pick bvals)))
  ≡⟨ cong (decodes [ τ ]) (sym (Circ′-++-≡ (toBools Γ) (enc [ τ ]) (Cr′⟦ O∘D ⟧ (lookup pick bvals)) (bvals))) ⟩
    decodes [ τ ] (Cr′⟦ Circ′-++ (toBools Γ) (enc [ τ ]) ⟧ (Cr′⟦ O∘D ⟧ (lookup pick bvals) ++Vl bvals))
  ≡⟨⟩
    decodes [ τ ] (Cr′⟦ comp pick O∘D (Circ′-++ (toBools Γ) (enc [ τ ])) ⟧ bvals)
  ∎
  where pick = iniVars (toBools Γ)
        O∘D  = comp pick (dec Γ) (Circ′-++ (toBools Γ) (oper op))

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
