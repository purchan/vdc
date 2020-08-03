open import Data.Bool using (Bool; true; false;  _∧_) public
open import Data.Nat  using (ℕ; zero; suc) public
open import Data.List using (List; []; _∷_; _++_; replicate; concatMap; concat; map; take) public
open import Data.Product using (_×_; Σ; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst; inspect) renaming ([_] to In[_]) public
open Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎) public
open import Function using (id) public
------------------------------------------------

infix 2 _∈_
data _∈_ {A : Set} : A → List A → Set where
  here  : ∀{x xs}
        → x ∈ x ∷ xs
  there : ∀{x y xs} → x ∈ xs
        → x ∈ y ∷ xs

∈-suf : {A : Set} → {x : A} {xs ys : List A}
      →  x ∈ xs → x ∈ xs ++ ys
∈-suf           here      = here
∈-suf {ys = ys} (there l) = there (∈-suf {ys = ys} l)
------------------------------------------------

++-identityʳ : ∀{A : Set} (xs : List A)
             → xs ++ [] ≡ xs
++-identityʳ [] = refl
++-identityʳ (x ∷ xs) rewrite ++-identityʳ xs = refl

++-assoc : {A : Set} → (xs ys zs : List A)
         → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc []       ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)
