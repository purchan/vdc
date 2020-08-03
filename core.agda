open import lib public
data Tri : Set

data Ty : Set
Ty⟦_⟧ : Ty → Set

variable
  σ  τ  : Ty
  σs τs Γ Γ′ Δ Δ′ Θ Θ′ : List Ty
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
