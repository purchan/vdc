open import lib public
data Tri : Set

data Ty : Set
Ty⟦_⟧ : Ty → Set

variable
  σ  τ  : Ty
  σs τs Γ Γ′ Δ Δ′ Θ Θ′ Ω Ω′ : List Ty
------------------------
data Vals : List Ty → Set
++Vlp : Vals Γ → Vals Γ′ → (pf : Ω ≡ Γ ++ Γ′) → Vals Ω

data Vars : List Ty → List Ty → Set
_++Vr_ : Vars Γ Δ → Vars Γ Δ′ → Vars Γ (Δ ++ Δ′)

look : σ ∈ Γ → Vals Γ → Ty⟦ σ ⟧
lookup : Vars Γ Δ → Vals Γ  → Vals Δ

mapThere : Vars Γ Δ → Vars (σ ∷ Γ) Δ
iniVars : (Γ   : List Ty) → Vars Γ Γ
preVars : (pre : List Ty) → Vars Γ Δ → Vars (pre ++ Γ) Δ
sufVars : (suf : List Ty) → Vars Γ Δ → Vars (Γ ++ suf) Δ

------------------------
data Op   : List Ty → Ty → Set
data Circ : List Ty → List Ty → Set

Op⟦_⟧ : Op Θ τ   → Vals Θ → Ty⟦ τ ⟧
Cr⟦_⟧ : Circ Γ Δ → Vals Γ → Vals Δ

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

------------------------
data Vals where
  []  : Vals []
  _∷_ : Ty⟦ τ ⟧ → Vals τs → Vals (τ ∷ τs)

data Vars where
  []  : Vars Γ []
  _∷_ : (σ ∈ Γ) → Vars Γ Δ → Vars Γ (σ ∷ Δ)

pattern [_]       w       = w ∷ []
pattern [_,_]     w x     = w ∷ x ∷ []
pattern [_,_,_]   w x y   = w ∷ x ∷ y ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []

++Vlp []       ys refl = ys
++Vlp (x ∷ xs) ys refl = x ∷ (++Vlp xs ys refl)

[]       ++Vr ys = ys
(x ∷ xs) ++Vr ys = x ∷ (xs ++Vr ys)


look here      (val ∷ _   ) = val
look (there l) (_   ∷ vals) = look l vals

lookup []           _    = []
lookup (var ∷ vars) vals = look var vals ∷ lookup vars vals

mapThere []       = []
mapThere (x ∷ xs) = there x ∷ mapThere xs

iniVars []       = []
iniVars (x ∷ xs) = here ∷ mapThere (iniVars xs)

preVars []       vars = vars
preVars (p ∷ ps) vars = mapThere (preVars ps vars)

sufVars s []          = []
sufVars s (vr ∷ vars) = ∈-suf vr ∷ sufVars s vars

------------------------
data Op where
  andT : Op [ tri , tri ]   tri
  orT  : Op [ tri , tri ]   tri
  ≡C   : Op [ tri , tri ]   bool

  andB : Op [ bool , bool ] bool
  orB  : Op [ bool , bool ] bool
  notB : Op [ bool ]        bool

data Circ where
  ret  : Vars Γ Δ → Circ Γ Δ
  oper : Op Γ τ   → Circ Γ [ τ ]
  comp : Vars Γ Θ → Circ Θ Θ′ → {Γ′ : List Ty} → (pf : Γ′ ≡ Θ′ ++ Γ) → Circ Γ′ Δ → Circ Γ Δ

Op⟦ andT ⟧ [ true  , y     ] = y
Op⟦ andT ⟧ [ false , _     ] = false
Op⟦ andT ⟧ [ dc    , false ] = false
Op⟦ andT ⟧ [ dc    , _     ] = dc

Op⟦ orT  ⟧ [ false , y     ] = y
Op⟦ orT  ⟧ [ true  , _     ] = true
Op⟦ orT  ⟧ [ dc    , true  ] = true
Op⟦ orT  ⟧ [ dc    , _     ] = dc

Op⟦ ≡C   ⟧ [ false , false ] = true
Op⟦ ≡C   ⟧ [ false , _     ] = false
Op⟦ ≡C   ⟧ [ true  , true  ] = true
Op⟦ ≡C   ⟧ [ true  , _     ] = false
Op⟦ ≡C   ⟧ [ dc    , _     ] = true

Op⟦ andB ⟧ [ x , y ] = x ∧ y
Op⟦ orB  ⟧ [ x , y ] = x ∨ y
Op⟦ notB ⟧ [ b ]     = not b

Cr⟦ ret vars ⟧ vals = lookup vars vals
Cr⟦ oper op  ⟧ vals = [ Op⟦ op ⟧ vals ]
Cr⟦ comp vars c pf k ⟧ vals = Cr⟦ k ⟧ (++Vlp (Cr⟦ c ⟧ (lookup vars vals)) vals pf)
