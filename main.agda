open import Function
open import Data.Product
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.List as List
open import Relation.Binary.PropositionalEquality


infix 2 _∈_

data _∈_ {A : Set} : A → List A → Set where
  zero : ∀ {x xs}   → x ∈ x ∷ xs
  suc  : ∀ {x y xs} → x ∈ xs → x ∈ y ∷ xs

data Tri : Set where
  false : Tri
  true  : Tri
  dc    : Tri

data Ty : Set where
  bool : Ty
  tri  : Ty

variable
  σ τ : Ty
  σs τs Γ Δ Θ : List Ty

⟦_⟧ᵀʸ : Ty → Set
⟦ bool ⟧ᵀʸ = Bool
⟦ tri  ⟧ᵀʸ = Tri

infixr 5 _∷_
data Vals : List Ty → Set where
  []  : Vals []
  _∷_ : ⟦ τ ⟧ᵀʸ → Vals τs → Vals (τ ∷ τs)

_++ⱽᵃˡˢ_ : Vals σs → Vals τs → Vals (σs ++ τs)
[]       ++ⱽᵃˡˢ ys = ys
(x ∷ xs) ++ⱽᵃˡˢ ys = x ∷ (xs ++ⱽᵃˡˢ ys)

splitVals : (xs : Vals (σs ++ τs)) → Σ[ ys ∈ Vals σs ] Σ[ zs ∈ Vals τs ] xs ≡ ys ++ⱽᵃˡˢ zs
splitVals {[]}     xs       = _ , xs , refl
splitVals {σ ∷ σs} (x ∷ xs) with splitVals {σs} xs
splitVals {σ ∷ σs} (x ∷ xs) | ys , zs , eq = x ∷ ys , zs , cong₂ _∷_ refl eq

data Op : List Ty → Ty → Set where
  andᵀ : Op (tri  ∷ tri  ∷ []) tri
  andᴮ : Op (bool ∷ bool ∷ []) bool
  test : Op (tri  ∷ tri  ∷ []) bool

⟦_⟧ᴼᵖ : Op Θ τ → Vals Θ → ⟦ τ ⟧ᵀʸ
⟦ andᵀ ⟧ᴼᵖ (false ∷ y     ∷ []) = false
⟦ andᵀ ⟧ᴼᵖ (true  ∷ y     ∷ []) = y
⟦ andᵀ ⟧ᴼᵖ (dc    ∷ false ∷ []) = false
⟦ andᵀ ⟧ᴼᵖ (dc    ∷ true  ∷ []) = dc
⟦ andᵀ ⟧ᴼᵖ (dc    ∷ dc    ∷ []) = dc
⟦ andᴮ ⟧ᴼᵖ (x     ∷ y     ∷ []) = x ∧ y
⟦ test ⟧ᴼᵖ (false ∷ false ∷ []) = true
⟦ test ⟧ᴼᵖ (false ∷ true  ∷ []) = false
⟦ test ⟧ᴼᵖ (false ∷ dc    ∷ []) = false
⟦ test ⟧ᴼᵖ (true  ∷ false ∷ []) = false
⟦ test ⟧ᴼᵖ (true  ∷ true  ∷ []) = true
⟦ test ⟧ᴼᵖ (true  ∷ dc    ∷ []) = false
⟦ test ⟧ᴼᵖ (dc    ∷ y     ∷ []) = true

data Vars : List Ty → List Ty → Set where
  []  : Vars Γ []
  _∷_ : (σ ∈ Γ) → Vars Γ Δ → Vars Γ (σ ∷ Δ)

data Circuit : List Ty → List Ty → Set where
  return  : Vars Γ Δ → Circuit Γ Δ
  compute : Op Θ τ → Vars Γ Θ → Circuit (τ ∷ Γ) Δ → Circuit Γ Δ

var : τ ∈ Γ → Vals Γ → ⟦ τ ⟧ᵀʸ
var zero    (x ∷ env) = x
var (suc i) (_ ∷ env) = var i env

vars : Vars Γ Δ → Vals Γ → Vals Δ
vars []       _   = []
vars (v ∷ vs) env = var v env ∷ vars vs env

⟦_⟧ : Circuit Γ Δ → Vals Γ → Vals Δ
⟦ return vs       ⟧ env = vars vs env
⟦ compute op vs c ⟧ env = ⟦ c ⟧ (⟦ op ⟧ᴼᵖ (vars vs env) ∷ env)

BooleanContext : List Ty → Set
BooleanContext Γ = Γ ≡ List.map (const bool) Γ

data BooleanCircuit : Circuit Γ Δ → Set where
  return  : {vs : Vars Γ Δ}
          → BooleanContext Γ → BooleanCircuit (return vs)
  compute : {op : Op Θ τ} {vs : Vars Γ Θ} {c : Circuit (τ ∷ Γ) Δ}
          → BooleanCircuit c → BooleanCircuit (compute op vs c)

size : Ty → ℕ
size bool = 1
size tri  = 2

encodeTy : Ty → List Ty
encodeTy τ = replicate (size τ) bool

encodeTys : List Ty → List Ty
encodeTys = concatMap encodeTy

data Bundle : (τs : List Ty) → Vals (encodeTys τs) → Set where
  nil  : Bundle [] []
  cons : (xs : Vals (encodeTy τ)) (ys : Vals (encodeTys τs)) → Bundle τs ys → Bundle (τ ∷ τs) (xs ++ⱽᵃˡˢ ys)

matchBundle : (τs : List Ty) (xs : Vals (encodeTys τs)) → Bundle τs xs
matchBundle []       []  = nil
matchBundle (τ ∷ τs) xs with splitVals {encodeTy τ} xs
matchBundle (τ ∷ τs) .(ys ++ⱽᵃˡˢ zs) | ys , zs , refl = cons ys zs (matchBundle τs zs)

decode : (τ : Ty) → Vals (encodeTy τ) → ⟦ τ ⟧ᵀʸ
decode bool (false ∷ []) = false
decode bool (true  ∷ []) = true
decode tri  (false ∷ false ∷ []) = false
decode tri  (false ∷ true  ∷ []) = true
decode tri  (true  ∷ _     ∷ []) = dc

decodeBundle : (τs : List Ty) (xs : Vals (encodeTys τs)) → Bundle τs xs → Vals τs
decodeBundle []       ._              nil            = []
decodeBundle (τ ∷ τs) .(xs ++ⱽᵃˡˢ ys) (cons xs ys b) = decode τ xs ∷ decodeBundle τs ys b

compile : Circuit Γ Δ → Circuit (encodeTys Γ) (encodeTys Δ)
compile = {!!}

compile-Boolean : (c : Circuit Γ Δ) → BooleanCircuit (compile c)
compile-Boolean = {!!}

compile-correctness : (c : Circuit Γ Δ) (xs : Vals (encodeTys Γ)) (b : Bundle Γ xs) (b' : Bundle Δ (⟦ compile c ⟧ xs))
                    → ⟦ c ⟧ (decodeBundle Γ xs b) ≡ decodeBundle Δ (⟦ compile c ⟧ xs) b'
compile-correctness = {!!}
