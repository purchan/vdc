open import enclib public

split-ri : (vals : Vals Γ) → splitVals (vals ++Vl []) ≡ ⟨ vals , ⟨ [] , refl ⟩ ⟩
split-rc : (vals : Vals Γ) (vals₁ : Vals Θ) (vals₂ : Vals Θ′)
         → splitVals (vals ++Vl (vals₁ ++Vl vals₂)) ≡ ⟨ vals , ⟨ vals₁ ++Vl vals₂ , refl ⟩ ⟩
split-bv : (σ : Ty) (σs : List Ty) (bval : Vals (toBool σ)) (bvals : Vals (toBools σs))
         → splitVals {toBool σ} {toBools σs} (bval ++Vl bvals)
         ≡ ⟨ bval , ⟨ bvals , refl ⟩ ⟩

------------------------
lookup-mapThere : (vars : Vars Γ Δ) (vl : Ty⟦ τ ⟧) (vals : Vals Γ)
                → lookup (mapThere vars) (vl ∷ vals) ≡ lookup vars vals

lookup-ini : (vals : Vals Γ) → lookup (iniVars Γ) vals ≡ vals

look-suf : (vr : σ ∈ Γ) (valΓ : Vals Γ) (valΓ′ : Vals Γ′)
            → look (∈-suf vr) (valΓ ++Vl valΓ′) ≡ look vr valΓ
lookup-suf : (vars : Vars Γ Δ) (valΓ : Vals Γ) (valΓ′ : Vals Γ′)
           → lookup (sufVars Γ′ vars) (valΓ ++Vl valΓ′) ≡ lookup vars valΓ

lookup-pre : (vars : Vars Γ Δ) (valΓ : Vals Γ) (valΓ′ : Vals Γ′)
           → lookup (preVars Γ′ vars) (valΓ′ ++Vl valΓ) ≡ lookup vars valΓ

lookup-++Vr : (vars₁ : Vars Γ Δ) (vars₂ : Vars Γ Δ′) (vals : Vals Γ)
            → lookup vars₁ vals ++Vl lookup vars₂ vals ≡ lookup (vars₁ ++Vr vars₂) vals
------------------------
++Vl-++bVl : (bvalσ : Vals (toBool σ)) (bvalσs : Vals (toBools σs)) (bvalΓ′ : Vals (toBools Γ′))
           → bvalσ ++Vl (_++bVl_ {σs} {Γ′} bvalσs bvalΓ′)
           ≡ _++bVl_ {σ ∷ σs} {Γ′} (bvalσ ++Vl bvalσs) bvalΓ′

dec-++Vl : (bvalσ : Vals (toBool σ)) (bvalσs : Vals (toBools σs))
         → decode σ bvalσ ∷ decodes σs bvalσs ≡ decodes (σ ∷ σs) (bvalσ ++Vl bvalσs)
decs-++Vl : (bvalΓ : Vals (toBools Γ)) (bvalΓ′ : Vals (toBools Γ′))
          → decodes Γ bvalΓ ++Vl decodes Γ′ bvalΓ′
          ≡ decodes (Γ ++ Γ′) (_++bVl_ {Γ} {Γ′} bvalΓ bvalΓ′)

decs-lookup : (vars₁ : Vars Γ (toBool σ)) (vars₂ : Vars Γ (toBools σs)) (vals : Vals Γ)
             → decode σ (lookup vars₁ vals) ∷ decodes σs (lookup vars₂ vals)
             ≡ decodes (σ ∷ σs) (lookup (vars₁ ++Vr vars₂) vals)

look-dec : (vr : σ ∈ Γ) (bvals : Vals (toBools Γ))
         → look vr (decodes Γ bvals) ≡ decode σ (lookup (encodeVar vr) bvals)
lookup-dec : (vars : Vars Γ Δ) (bvals : Vals (toBools Γ))
           → lookup vars (decodes Γ bvals) ≡ decodes Δ (lookup (encodeVars vars) bvals)

------------------------------------------------
split-ri [] = refl
split-ri (vl ∷ vals) rewrite split-ri vals = refl

split-rc []          vals₁ vals₂ = refl
split-rc (vl ∷ vals) vals₁ vals₂ rewrite split-rc vals vals₁ vals₂ = refl

split-bv σ []        bval []    = split-ri bval
split-bv σ (σ′ ∷ σs) bval bvals                 with splitVals {toBool σ′} {toBools σs} bvals
split-bv σ (σ′ ∷ σs) bval .(bvalσ′ ++Vl bvalσs) | ⟨ bvalσ′ , ⟨ bvalσs , refl ⟩ ⟩ = split-rc bval bvalσ′ bvalσs

------------------------
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

lookup-ini {[]}     []          = refl
lookup-ini {σ ∷ σs} (vl ∷ vals) =
  begin
    lookup (iniVars (σ ∷ σs)) (vl ∷ vals)
  ≡⟨⟩
    lookup (here ∷ mapThere (iniVars σs)) (vl ∷ vals)
  ≡⟨⟩
    vl ∷ lookup (mapThere (iniVars σs)) (vl ∷ vals)
  ≡⟨ cong (vl ∷_) (lookup-mapThere (iniVars σs) vl vals) ⟩
    vl ∷ lookup (iniVars σs) vals
  ≡⟨ cong (vl ∷_) (lookup-ini {σs} vals) ⟩
    vl ∷ vals
  ∎

look-suf here       (σ ∷ _)    _     = refl
look-suf (there pf) (_ ∷ vals) vals′ = look-suf pf vals vals′

lookup-suf {[]}     {Γ′ = Γ′} []          []          valΓ′ = refl
lookup-suf {σ ∷ σs} {Γ′ = Γ′} []          (vl ∷ vals) valΓ′ = refl
lookup-suf {σ ∷ σs} {Γ′ = Γ′} (vr ∷ vars) (vl ∷ vals) valΓ′ =
  begin
    lookup (sufVars Γ′ (vr ∷ vars)) ((vl ∷ vals) ++Vl valΓ′)
  ≡⟨ cong (_∷ lookup (sufVars Γ′ vars) (vl ∷ (vals ++Vl valΓ′))) (look-suf vr (vl ∷ vals) valΓ′) ⟩
    look vr (vl ∷ vals) ∷ lookup (sufVars Γ′ vars) ((vl ∷ vals) ++Vl valΓ′)
  ≡⟨ cong (look vr (vl ∷ vals) ∷_) (lookup-suf vars (vl ∷ vals) valΓ′) ⟩
    look vr (vl ∷ vals) ∷ lookup vars (vl ∷ vals)
  ≡⟨⟩
    lookup (vr ∷ vars) (vl ∷ vals)
  ∎

lookup-pre               vars valΓ []           = refl
lookup-pre {Γ′ = τ ∷ τs} vars valΓ (vl ∷ valΓ′) =
  begin
    lookup (preVars (τ ∷ τs) vars) ((vl ∷ valΓ′) ++Vl valΓ)
  ≡⟨ lookup-mapThere (preVars τs vars) vl (valΓ′ ++Vl valΓ) ⟩
    lookup (preVars τs vars) (valΓ′ ++Vl valΓ)
  ≡⟨ lookup-pre vars valΓ valΓ′ ⟩
    lookup vars valΓ
  ∎

lookup-++Vr []           vars₂ vals = refl
lookup-++Vr (vr ∷ vars₁) vars₂ vals rewrite lookup-++Vr vars₁ vars₂ vals = refl

------------------------
++Vl-++bVl {σ} {σs} {Γ′} bvalσ bvalσs bvalΓ′ rewrite split-bv σ σs bvalσ bvalσs = refl

dec-++Vl {σ} {σs} bvalσ bvalσs rewrite split-bv σ σs bvalσ bvalσs = refl

decs-++Vl {[]}     {Γ′} []    bvalΓ′ = refl
decs-++Vl {σ ∷ σs} {Γ′} bvalΓ                bvalΓ′ with splitVals {toBool σ} {toBools σs} bvalΓ
decs-++Vl {σ ∷ σs} {Γ′} .(bvalσ ++Vl bvalσs) bvalΓ′    | ⟨ bvalσ , ⟨ bvalσs , refl ⟩ ⟩
  rewrite decs-++Vl {σs} {Γ′} bvalσs bvalΓ′
        | dec-++Vl {σ} {σs ++ Γ′} bvalσ (_++bVl_ {σs} {Γ′} bvalσs bvalΓ′)
        | ++Vl-++bVl {σ} {σs} {Γ′} bvalσ bvalσs bvalΓ′ = refl

decs-lookup {Γ} {σ} {σs} vars₁ vars₂ vals =
  begin
    decode σ (lookup vars₁ vals) ∷ decodes σs (lookup vars₂ vals)
  ≡⟨ dec-++Vl (lookup vars₁ vals) (lookup vars₂ vals) ⟩
    decodes (σ ∷ σs) (lookup vars₁ vals ++Vl lookup vars₂ vals)
  ≡⟨ cong (decodes (σ ∷ σs)) (lookup-++Vr vars₁ vars₂ vals) ⟩
    decodes (σ ∷ σs) (lookup (vars₁ ++Vr vars₂) vals)
  ∎

look-dec {σ} {σ ∷ σs} here bvals               with splitVals {toBool σ} {toBools σs} bvals
look-dec {σ} {σ ∷ σs} here .(bvalσ ++Vl bvalσs)   | ⟨ bvalσ , ⟨ bvalσs , refl ⟩ ⟩
  rewrite lookup-suf (iniVars (toBool σ)) bvalσ bvalσs | lookup-ini {toBool σ} bvalσ = refl
look-dec {σ} {x ∷ σs} (there l) bvals                with encodeVar {σ} {σs} l | inspect (encodeVar {σ} {σs}) l | splitVals {toBool x} {toBools σs} bvals
look-dec {σ} {x ∷ σs} (there l) .(bvalx ++Vl bvalσs) | evar                    | In[ pf ]                       | ⟨ bvalx , ⟨ bvalσs , refl ⟩ ⟩ =
  begin
    look l (decodes σs bvalσs)
  ≡⟨ trans (look-dec l bvalσs) (cong (λ{evar → decode σ (lookup evar bvalσs)}) pf) ⟩
    decode σ (lookup evar bvalσs)
  ≡⟨ cong (decode σ) (sym (lookup-pre evar bvalσs bvalx)) ⟩
    decode σ (lookup (preVars (toBool x) evar) (bvalx ++Vl bvalσs))
  ∎

lookup-dec {[]}              []          []    = refl
lookup-dec {σ ∷ σs}          []          bvals = refl
lookup-dec {σ ∷ σs} {τ ∷ τs} (vr ∷ vars) bvals =
  begin
    lookup (vr ∷ vars) (decodes (σ ∷ σs) bvals)
  ≡⟨⟩
    look vr (decodes (σ ∷ σs) bvals) ∷ lookup vars (decodes (σ ∷ σs) bvals)
  ≡⟨ cong (_∷ lookup vars (decodes (σ ∷ σs) bvals)) (look-dec vr bvals) ⟩
    decode τ (lookup (encodeVar vr) bvals) ∷ lookup vars (decodes (σ ∷ σs) bvals)
  ≡⟨ cong (decode τ (lookup (encodeVar vr) bvals) ∷_) (lookup-dec vars bvals) ⟩
    decode τ (lookup (encodeVar vr) bvals) ∷ decodes τs (lookup (encodeVars vars) bvals)
  ≡⟨ decs-lookup (encodeVar vr) (encodeVars vars) bvals ⟩
    decodes (τ ∷ τs) (lookup (encodeVars (vr ∷ vars)) bvals)
  ∎
