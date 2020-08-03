------------------------
open import Data.Bool using (Bool; true; false;  _∧_) public
data Tri : Set
------------------------
open import Data.Nat  using (ℕ; zero; suc) public
open import Data.List using (List; []; _∷_; _++_; replicate; concatMap; concat; map; take) public

infix 2 _∈_
data _∈_ {A : Set} : A → List A → Set where
  here  : ∀{x xs}
        → x ∈ x ∷ xs
  there : ∀{x y xs} → x ∈ xs
        → x ∈ y ∷ xs

data Ty : Set
Ty⟦_⟧ : Ty → Set

variable
  σ  τ  : Ty
  σs τs Γ Γ′ Δ Δ′ Θ Θ′ : List Ty
  τss : List (List Ty)
------------------------
data Vals : List Ty → Set

data Vars : List Ty → List Ty → Set
data Op   : List Ty → Ty → Set
data Circ : List Ty → List Ty → Set

Op⟦_⟧ : Op Θ τ   → Vals Θ → Ty⟦ τ ⟧
Cr⟦_⟧ : Circ Γ Δ → Vals Γ → Vals Δ

lookup : Vars Γ Δ → Vals Γ  → Vals Δ
_++Vl_ : Vals Γ   → Vals Γ′ → Vals (Γ ++ Γ′)
------------------------------------------------
------------------------------------------------
data Tri where
  true  : Tri
  dc    : Tri
  false : Tri

data Ty where
  bool : Ty
  tri  : Ty

Ty⟦ bool ⟧ = Bool
Ty⟦ tri  ⟧ = Tri

data Vals where
  []  : Vals []
  _∷_ : Ty⟦ τ ⟧ → Vals τs → Vals (τ ∷ τs)

data Vars where
  []  : Vars Γ []
  _∷_ : (σ ∈ Γ) → Vars Γ Δ → Vars Γ (σ ∷ Δ)

pattern [_]     x     = x ∷ []
pattern [_,_]   x y   = x ∷ y ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []

data Op where
  andT : Op [ tri , tri ]   tri
  andB : Op [ bool , bool ] bool
  ≡C   : Op [ tri , tri ]   bool

data Circ where
  ret  : Vars Γ Δ → Circ Γ Δ
  oper : Op Γ τ   → Circ Γ [ τ ]
  comp : Vars Γ Θ → Circ Θ Θ′ → Circ (Θ′ ++ Γ) Δ → Circ Γ Δ

[]       ++Vl ys = ys
(x ∷ xs) ++Vl ys = x ∷ (xs ++Vl ys)

Op⟦ andT ⟧ [ true  , y     ] = y
Op⟦ andT ⟧ [ false , _     ] = false
Op⟦ andT ⟧ [ dc    , false ] = false
Op⟦ andT ⟧ [ dc    , _     ] = dc

Op⟦ andB ⟧ [ x , y ] = x ∧ y

Op⟦ ≡C   ⟧ [ false , false ] = true
Op⟦ ≡C   ⟧ [ false , _     ] = false
Op⟦ ≡C   ⟧ [ true  , true  ] = true
Op⟦ ≡C   ⟧ [ true  , _     ] = false
Op⟦ ≡C   ⟧ [ dc    , _     ] = true

Cr⟦ ret vars ⟧ vals = lookup vars vals
Cr⟦ oper op  ⟧ vals = [ Op⟦ op ⟧ vals ]
Cr⟦ comp vars c k ⟧ vals = Cr⟦ k ⟧ (Cr⟦ c ⟧ (lookup vars vals) ++Vl vals)

lookup []           _    = []
lookup (var ∷ vars) vals = look var vals ∷ lookup vars vals
                         where look : σ ∈ Γ → Vals Γ → Ty⟦ σ ⟧
                               look here      (val ∷ _   ) = val
                               look (there l) (_   ∷ vals) = look l vals


------------------------------------------------
open import Data.Product using (_×_; Σ; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

size   : Ty → ℕ
toBool : Ty → List Ty

encode : (τ : Ty) → Ty⟦ τ ⟧ → Vals (toBool τ)   -- Needed for Op conversion
decode : (τ : Ty) → Vals (toBool τ) → Ty⟦ τ ⟧   -- For correctness checking

toBools : List Ty → List Ty
encodes : (τs : List Ty) → Vals τs → Vals (toBools τs)
decodes : (τs : List Ty) → Vals (toBools τs) → Vals τs

compile : Circ Γ Δ → Circ (toBools Γ) (toBools Δ)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; inspect) renaming ([_] to In[_])
correctness : (c : Circ Γ Δ) (bvals : Vals (toBools Γ))
            → Cr⟦ c ⟧ (decodes Γ bvals) ≡ decodes Δ (Cr⟦ compile c ⟧ bvals)
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


++-identityʳ : ∀{A : Set} (xs : List A)
             → xs ++ [] ≡ xs
++-identityʳ [] = refl
++-identityʳ (x ∷ xs) rewrite ++-identityʳ xs = refl

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
-- Is compiled op, just (decode ∘ op ∘ encode) ?
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
  where ++-assoc : {A : Set} → (xs ys zs : List A)
                 → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
        ++-assoc []       ys zs = refl
        ++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

Circ-++  {Γ} {Γ′} {Δ} rewrite toBools-++ {Γ} {Γ′} = refl
Circ-++′ {Γ} {Γ′} {Δ} k rewrite Circ-++ {Γ} {Γ′} {Δ} = k


buildCirc pre Γ suf Δ circ = comp pickupVr circ pickupCr
                           where pickupVr = buildVars pre Γ suf
                                 pickupCr = ret (buildVars [] Δ (pre ++ Γ ++ suf))

compile (ret vars)        = ret (encodeVars vars)
compile (oper {Γ} {τ} op) = comp pickall (comp pickall (decodeCirc Γ) matchOp) matchEnc
                          where pickall   = allVars (toBools Γ)
                                matchOp   = buildCirc [] Γ (toBools Γ) [ τ ] (oper op)
                                matchEnc  = buildCirc [] [ τ ] (toBools Γ) (toBools [ τ ]) (encodeCirc [ τ ])

compile (comp {Γ} {Θ} {Θ′} {Δ} vars c k) = comp (encodeVars vars) (compile c) (Circ-++′ {Θ′} {Γ} (compile k))
