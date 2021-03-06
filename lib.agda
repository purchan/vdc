open import Data.Bool using (Bool; true; false;  _∧_; _∨_; not) public
open import Data.Nat  using (ℕ) public
open import Data.List using (List; []; _∷_; _++_; replicate; concatMap) public
open import Data.Product using (Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; inspect) renaming ([_] to In[_]) public
open        Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎) public

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

------------------------

++-assoc : {A : Set} → (xs ys zs : List A)
         → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc []       ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)
