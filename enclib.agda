open import core public

size   : Ty → ℕ
toBool : Ty → List Ty

encode : (τ : Ty) → Ty⟦ τ ⟧ → Vals (toBool τ)
decode : (τ : Ty) → Vals (toBool τ) → Ty⟦ τ ⟧

toBools : List Ty → List Ty
encodes : (τs : List Ty) → Vals τs → Vals (toBools τs)
decodes : (τs : List Ty) → Vals (toBools τs) → Vals τs
------------------------------------------------

size bool = 1
size tri  = 2
toBool τ  = replicate (size τ) bool

encode bool b     = [ b ]
encode tri  true  = [ false , true  ]
encode tri  false = [ false , false ]
encode tri  dc    = [ true  , false ]
decode bool [ b ] = b
decode tri  [ false , true  ] = true
decode tri  [ false , false ] = false
decode tri  [ true  , _     ] = dc

toBools = concatMap toBool
encodes []       [] = []
encodes (τ ∷ τs) (val ∷ vals) = encode τ val ++Vl encodes τs vals

decodes τs bvals = decodes′ τs bvals (toVals′ τs bvals)
  where data Vals′ : (τs : List Ty) → Vals (toBools τs) → Set where
          nil  : Vals′ [] []
          cons : {τ : Ty} {τs : List Ty}
               → (bval : Vals (toBool τ)) (bvals : Vals (toBools τs))
               → Vals′ τs bvals → Vals′ (τ ∷ τs) (bval ++Vl bvals)

        splitVals : {σs : List Ty} {τs : List Ty} (valστ : Vals (σs ++ τs))
                  → Σ[ valσ ∈ Vals σs ] Σ[ valτ ∈ Vals τs ] (valστ ≡ valσ ++Vl valτ)
        splitVals {[]}     valτ = ⟨ _ , ⟨ valτ , refl ⟩ ⟩
        splitVals {σ ∷ σs} (val ∷ vals) with splitVals {σs} vals
        ...                                | ⟨ val′ , ⟨ valτ , pf ⟩ ⟩ = ⟨ val ∷ val′ , ⟨ valτ , cong (val ∷_) pf ⟩ ⟩

        toVals′ : (τs : List Ty) (bvals : Vals (toBools τs)) → Vals′ τs bvals
        toVals′ []       []    = nil
        toVals′ (τ ∷ τs) bvals                with splitVals {toBool τ} {toBools τs} bvals
        toVals′ (τ ∷ τs) .(bvalτ ++Vl bvalτs) | ⟨ bvalτ , ⟨ bvalτs , refl ⟩ ⟩
                               = cons {τ} {τs} bvalτ bvalτs (toVals′ τs bvalτs)

        decodes′ : (τs : List Ty) (bvals : Vals (toBools τs))
                 → Vals′ τs bvals → Vals τs
        decodes′ []       ._                 nil                     = []
        decodes′ (τ ∷ τs) .(bval ++Vl bvals) (cons bval bvals vals′) = decode τ bval ∷ decodes′ τs bvals vals′

------------------------------------------------
_++Vr_  : Vars Γ Δ → Vars Γ Δ′ → Vars Γ (Δ ++ Δ′)

mapThere : Vars Γ Δ → Vars (σ ∷ Γ) Δ
mapsThere : Vars Γ Δ → Vars (Γ′ ++ Γ) Δ
buildVars : (pre Γ suf : List Ty) → Vars (pre ++ Γ ++ suf) Γ
allVars   : (Γ : List Ty) → Vars Γ Γ

encodeVars : Vars Γ Δ → Vars (toBools Γ) (toBools Δ)
------------------------------------------------
[]       ++Vr ys = ys
(x ∷ xs) ++Vr ys = x ∷ (xs ++Vr ys)

mapThere []       = []
mapThere (x ∷ xs) = there x ∷ mapThere xs

mapsThere {Γ′ = []}       xs = xs
mapsThere {Γ′ = (y ∷ ys)} xs = mapThere (mapsThere {Γ′ = ys} xs)

buildVars _        []       _  = []
buildVars []       (x ∷ xs) ss = here ∷ buildVars [ x ] xs ss
buildVars (p ∷ ps) (x ∷ xs) ss = mapThere (buildVars ps (x ∷ xs) ss)

Vars-++ : Vars (Γ ++ []) Δ ≡ Vars Γ Δ
Vars-++ {Γ} {Δ} rewrite ++-identityʳ Γ = refl
allVars Γ rewrite sym (Vars-++ {Γ} {Γ}) = buildVars [] Γ []

encodeVars []           = []
encodeVars (var ∷ vars) = encodeVar var ++Vr encodeVars vars
                        where encodeVar : {σ : Ty} {Γ : List Ty}
                                        → σ ∈ Γ → Vars (toBools Γ) (toBool σ)
                              encodeVar {σ} {σ ∷ σs} here       = buildVars [] (toBool σ) (toBools σs)
                              encodeVar {σ} {x ∷ σs} (there pf) with encodeVar {σ} {σs} pf
                              ...                                  | res
                                                                = buildVars (toBool x) [] (toBools σs) ++Vr mapsThere res

------------------------------------------------
encodeCirc : (τs : List Ty) → Circ τs (toBools τs)
decodeCirc : (τs : List Ty) → Circ (toBools τs) τs

toBools-++ : toBools Γ ++ toBools Γ′ ≡ toBools (Γ ++ Γ′)
Circ-++  : Circ (toBools (Γ ++ Γ′)) Δ ≡ Circ (toBools Γ ++ toBools Γ′) Δ
Circ-++′ : Circ (toBools (Γ ++ Γ′)) Δ → Circ (toBools Γ ++ toBools Γ′) Δ

buildCirc : (pre Γ suf Δ : List Ty) → Circ Γ Δ → Circ (pre ++ Γ ++ suf) Δ
------------------------------------------------
encodeCirc τs = {!!}
decodeCirc τs = {!!}

toBools-++ {[]} = refl
toBools-++ {σ ∷ σs} {Γ′} =
  begin
    toBools (σ ∷ σs) ++ toBools Γ′
  ≡⟨⟩
    (toBool σ ++ toBools σs) ++ toBools Γ′
  ≡⟨ ++-assoc (toBool σ) (toBools σs) (toBools Γ′) ⟩
    toBool σ ++ (toBools σs ++ toBools Γ′)
  ≡⟨ cong (toBool σ ++_) (toBools-++ {σs} {Γ′}) ⟩
    toBool σ ++ toBools (σs ++ Γ′)
  ≡⟨⟩
    toBools ((σ ∷ σs) ++ Γ′)
  ∎

Circ-++  {Γ} {Γ′} {Δ} rewrite toBools-++ {Γ} {Γ′} = refl
Circ-++′ {Γ} {Γ′} {Δ} k rewrite Circ-++ {Γ} {Γ′} {Δ} = k

buildCirc pre Γ suf Δ circ = comp pickupVr circ pickupCr
                           where pickupVr = buildVars pre Γ suf
                                 pickupCr = ret (buildVars [] Δ (pre ++ Γ ++ suf))
