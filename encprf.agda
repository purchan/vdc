open import enclib public

split-ri : (vals : Vals Γ)
         → (pf : Ω ≡ Γ ++ [])
         → splitVals (++Vlp vals [] pf) pf ≡ ⟨ vals , ⟨ [] , refl ⟩ ⟩

split-rc : (vals : Vals Γ) (vals₁ : Vals Θ) (vals₂ : Vals Θ′)
         → (pf : Ω ≡ Θ ++ Θ′) (pf′ : Ω′ ≡ Γ ++ Ω)
         → splitVals (++Vlp vals (++Vlp vals₁ vals₂ pf) pf′) pf′ ≡ ⟨ vals , ⟨ ++Vlp vals₁ vals₂ pf , refl ⟩ ⟩

split-bv : {σ : Ty} {σs : List Ty} (bval : Vals (toBool σ)) (bvals : Vals (toBools σs))
         → (pf : toBools Ω ≡ toBool σ ++ toBools σs)
         → splitVals {σs = toBool σ} {τs = toBools σs} (++Vlp bval bvals pf) pf
         ≡ ⟨ bval , ⟨ bvals , refl ⟩ ⟩

------------------------
++Vlp-∷ : (v : Ty⟦ σ ⟧) (valσs : Vals σs) (valτs : Vals τs)
        → (pf₁ : Ω ≡ σs ++ τs) (pf₂ : σ ∷ Ω ≡ (σ ∷ σs) ++ τs)
        → v ∷ ++Vlp valσs valτs pf₁ ≡ ++Vlp (v ∷ valσs) valτs pf₂

++Vlp-assoc : (valσs : Vals σs) (valτs : Vals τs) (valsΓ : Vals Γ)
            → (pf₁ : Δ  ≡ τs ++ Γ ) (pf₂ : Ω ≡ σs ++ Δ)
              (pf₃ : Δ′ ≡ σs ++ τs) (pf₄ : Ω ≡ Δ′ ++ Γ)
            → ++Vlp valσs (++Vlp valτs valsΓ pf₁) pf₂ ≡ ++Vlp (++Vlp valσs valτs pf₃) valsΓ pf₄

dec-++Vlp : (bvalσ : Vals (toBool σ)) (bvalσs : Vals (toBools σs))
          → decode σ bvalσ ∷ decodes σs bvalσs ≡ decodes (σ ∷ σs) (++Vlp bvalσ bvalσs refl)

lookup-++Vr : (vars₁ : Vars Γ Δ) (vars₂ : Vars Γ Δ′) (vals : Vals Γ)
            → ++Vlp (lookup vars₁ vals) (lookup vars₂ vals) refl ≡ lookup (vars₁ ++Vr vars₂) vals

------------------------
decs-lookup : (vars₁ : Vars Γ (toBool σ)) (vars₂ : Vars Γ (toBools σs)) (vals : Vals Γ)
             → decode σ (lookup vars₁ vals) ∷ decodes σs (lookup vars₂ vals)
             ≡ decodes (σ ∷ σs) (lookup (vars₁ ++Vr vars₂) vals)

decs-++Vlp : (bvalΓ : Vals (toBools Γ)) (bvalΓ′ : Vals (toBools Γ′))
           → (pf : Ω ≡ Γ ++ Γ′) (pf′ : toBools Ω ≡ toBools Γ ++ toBools Γ′)
           → ++Vlp (decodes Γ bvalΓ) (decodes Γ′ bvalΓ′) pf
           ≡ decodes Ω (++Vlp bvalΓ bvalΓ′ pf′)

------------------------
lookup-mapThere : (vars : Vars Γ Δ) (vl : Ty⟦ τ ⟧) (vals : Vals Γ)
                → lookup (mapThere vars) (vl ∷ vals) ≡ lookup vars vals

lookup-pre : (vars : Vars Γ Δ) (valΓ : Vals Γ) (valΓ′ : Vals Γ′)
           → lookup (preVars Γ′ vars) (++Vlp valΓ′ valΓ refl) ≡ lookup vars valΓ

lookup-ini : (vals : Vals Γ) → lookup (iniVars Γ) vals ≡ vals

look-suf : (vr : σ ∈ Γ) (valΓ : Vals Γ) (valΓ′ : Vals Γ′)
            → look (∈-suf vr) (++Vlp valΓ valΓ′ refl) ≡ look vr valΓ

lookup-suf : (vars : Vars Γ Δ) (valΓ : Vals Γ) (valΓ′ : Vals Γ′)
           → lookup (sufVars Γ′ vars) (++Vlp valΓ valΓ′ refl) ≡ lookup vars valΓ

------------------------
look-dec : (vr : σ ∈ Γ) (bvals : Vals (toBools Γ))
         → look vr (decodes Γ bvals) ≡ decode σ (lookup (encodeVar vr) bvals)

lookup-dec : (vars : Vars Γ Δ) (bvals : Vals (toBools Γ))
           → lookup vars (decodes Γ bvals) ≡ decodes Δ (lookup (encodeVars vars) bvals)

------------------------------------------------
split-ri []       refl = refl
split-ri (v ∷ vs) refl rewrite split-ri vs refl = refl

split-rc []       vals₁ vals₂ refl refl = refl
split-rc (v ∷ vs) vals₁ vals₂ refl refl rewrite split-rc vs vals₁ vals₂ refl refl = refl

split-bv {σs = []}     bval []                         pf = split-ri bval pf
split-bv {σs = τ ∷ τs} bval bvals                      pf with splitVals {σs = toBool τ} {τs = toBools τs} bvals refl
split-bv {σs = τ ∷ τs} bval .(++Vlp bvalτ bvalτs refl) pf    | ⟨ bvalτ , ⟨ bvalτs , refl ⟩ ⟩ = split-rc bval bvalτ bvalτs refl pf
------------------------
++Vlp-∷ v valσs valτs refl refl = refl

++Vlp-assoc {[]}              []       valτs valsΓ refl refl refl refl = refl
++Vlp-assoc {σ ∷ σs} {τs} {Γ} (v ∷ vs) valτs valsΓ refl refl refl pf₄
  rewrite ++Vlp-assoc {σs} {τs} {Γ} vs valτs valsΓ refl refl refl (sym (++-assoc σs τs Γ))
        | ++Vlp-∷ v (++Vlp vs valτs refl) valsΓ (sym (++-assoc σs τs Γ)) pf₄ = refl

dec-++Vlp {σ} {σs} bvalσ bvalσs rewrite split-bv {σ ∷ σs} {σ} {σs} bvalσ bvalσs refl = refl

lookup-++Vr []           vars₂ vals = refl
lookup-++Vr (vr ∷ vars₁) vars₂ vals rewrite lookup-++Vr vars₁ vars₂ vals = refl

------------------------
decs-lookup {Γ} {σ} {σs} vars₁ vars₂ vals =
  begin
    decode σ (lookup vars₁ vals) ∷ decodes σs (lookup vars₂ vals)
  ≡⟨ dec-++Vlp (lookup vars₁ vals) (lookup vars₂ vals) ⟩
    decodes (σ ∷ σs) (++Vlp (lookup vars₁ vals) (lookup vars₂ vals) refl)
  ≡⟨ cong (decodes (σ ∷ σs)) (lookup-++Vr vars₁ vars₂ vals) ⟩
    decodes (σ ∷ σs) (lookup (vars₁ ++Vr vars₂) vals)
  ∎

decs-++Vlp {[]}     {Γ′} []    bvalΓ′ refl refl = refl
decs-++Vlp {σ ∷ σs} {Γ′} bvalΓ                      bvalΓ′ refl pf′    with splitVals {σs = toBool σ} {τs = toBools σs} bvalΓ refl
decs-++Vlp {σ ∷ σs} {Γ′} .(++Vlp bvalσ bvalσs refl) bvalΓ′ refl pf′       | ⟨ bvalσ , ⟨ bvalσs , refl ⟩ ⟩
  rewrite decs-++Vlp {σs} {Γ′} bvalσs bvalΓ′ refl (toBools-++ σs Γ′ refl)
        | dec-++Vlp {σ} {σs ++ Γ′} bvalσ (++Vlp bvalσs bvalΓ′ (toBools-++ σs Γ′ refl))
        | ++Vlp-assoc {toBool σ} {toBools σs} {toBools Γ′} bvalσ bvalσs bvalΓ′
            (toBools-++ σs Γ′ refl) refl refl pf′ = refl
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

lookup-pre               vars valΓ []           = refl
lookup-pre {Γ′ = τ ∷ τs} vars valΓ (vl ∷ valΓ′) =
  begin
    lookup (preVars (τ ∷ τs) vars) (++Vlp (vl ∷ valΓ′) valΓ refl)
  ≡⟨ lookup-mapThere (preVars τs vars) vl (++Vlp valΓ′ valΓ refl) ⟩
    lookup (preVars τs vars) (++Vlp valΓ′ valΓ refl)
  ≡⟨ lookup-pre vars valΓ valΓ′ ⟩
    lookup vars valΓ
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
    lookup (sufVars Γ′ (vr ∷ vars)) (++Vlp (vl ∷ vals) valΓ′ refl)
  ≡⟨ cong (_∷ lookup (sufVars Γ′ vars) (vl ∷ (++Vlp vals valΓ′ refl))) (look-suf vr (vl ∷ vals) valΓ′) ⟩
    look vr (vl ∷ vals) ∷ lookup (sufVars Γ′ vars) (++Vlp (vl ∷ vals) valΓ′ refl)
  ≡⟨ cong (look vr (vl ∷ vals) ∷_) (lookup-suf vars (vl ∷ vals) valΓ′) ⟩
    look vr (vl ∷ vals) ∷ lookup vars (vl ∷ vals)
  ≡⟨⟩
    lookup (vr ∷ vars) (vl ∷ vals)
  ∎

------------------------
look-dec {σ} {σ ∷ σs} here bvals                     with splitVals {σs = toBool σ} {τs = toBools σs} bvals (toBools-∷ σ σs refl)
look-dec {σ} {σ ∷ σs} here .(++Vlp bvalσ bvalσs refl)   | ⟨ bvalσ , ⟨ bvalσs , refl ⟩ ⟩
  rewrite lookup-suf (iniVars (toBool σ)) bvalσ bvalσs | lookup-ini {toBool σ} bvalσ = refl
look-dec {σ} {x ∷ σs} (there l) bvals                   with encodeVar {σ} {σs} l    | inspect (encodeVar {σ} {σs}) l | splitVals {σs = toBool x} {τs = toBools σs} bvals (toBools-∷ x σs refl)
look-dec {σ} {x ∷ σs} (there l) .(++Vlp bvalx bvalσs refl) | evar                    | In[ pf ]                       | ⟨ bvalx , ⟨ bvalσs , refl ⟩ ⟩ =
  begin
    look l (decodes σs bvalσs)
  ≡⟨ trans (look-dec l bvalσs) (cong (λ{evar → decode σ (lookup evar bvalσs)}) pf) ⟩
    decode σ (lookup evar bvalσs)
  ≡⟨ cong (decode σ) (sym (lookup-pre evar bvalσs bvalx)) ⟩
    decode σ (lookup (preVars (toBool x) evar) (++Vlp bvalx bvalσs refl))
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
