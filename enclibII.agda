open import enclib public

preCirc′ : (Γ′ : List Ty) → Circ Γ Δ → Circ (Γ′ ++ Γ) (Γ′ ++ Δ)
preCirc′ {Γ} {Δ} Γ′ circ = comp pick₁ circ refl (ret pick₂)
                         where pick₁ = preVars Γ′ (iniVars Γ)

                               pick₂₁ = preVars Δ (sufVars Γ (iniVars Γ′))
                               pick₂₂ = sufVars (Γ′ ++ Γ) (iniVars Δ)
                               pick₂ = pick₂₁ ++Vr pick₂₂

_++Cr_ : Circ Γ Δ → Circ Γ Δ′ → Circ Γ (Δ ++ Δ′)
_++Cr_ {Γ} {Δ} {Δ′} c₁ c₂ = comp (iniVars Γ) c₁ refl (preCirc′ Δ c₂)

--------------------------
data Lit Γ : Set where
  pos   : bool ∈ toBools Γ → Lit Γ
  neg   : bool ∈ toBools Γ → Lit Γ
  -- trueC : Lit Γ

data Cls Γ : Set where
  triv : Lit Γ → Cls Γ
  disj : Lit Γ → Cls Γ → Cls Γ

data Cnf Γ : Set where
  triv : Cls Γ → Cnf Γ
  conj : Cls Γ → Cnf Γ → Cnf Γ

litCirc : Lit Γ → Circ (toBools Γ) [ bool ]
litCirc     (pos i) = ret [ i ]
litCirc {Γ} (neg i) = comp [ i ] (oper notB) refl (ret pick)
                    where pick = sufVars (toBools Γ) (iniVars [ bool ])
-- litCirc     trueC   = oper trueC

clsCirc : Cls Γ → Circ (toBools Γ) [ bool ]
clsCirc     (triv l)   = litCirc l
clsCirc {Γ} (disj l c) = comp pick₁ (litCirc l ++Cr clsCirc c) refl (comp pick₂ (oper orB) refl  (ret pick₃))
                       where pick₁ = iniVars (toBools Γ)
                             pick₂ = sufVars (toBools Γ) (iniVars [ bool , bool ])
                             pick₃ = sufVars (bool ∷ bool ∷ toBools Γ) (iniVars [ bool ])

cnfCirc : Cnf Γ → Circ (toBools Γ) [ bool ]
cnfCirc     (triv c)   = clsCirc c
cnfCirc {Γ} (conj c n) = comp pick₁ (clsCirc c ++Cr cnfCirc n) refl (comp pick₂ (oper andB) refl (ret pick₃))
                       where pick₁ = iniVars (toBools Γ)
                             pick₂ = sufVars (toBools Γ) (iniVars [ bool , bool ])
                             pick₃ = sufVars (bool ∷ bool ∷ toBools Γ) (iniVars [ bool ])

pattern i11 = here
pattern i12 = there here
pattern i21 = there (there here)
pattern i22 = there (there (there here))
--------------------------
{-
decode-surj : ∀(v : Ty⟦ τ ⟧)
            → Σ[ bv ∈ Vals (toBool τ) ] decode τ bv ≡ v
decode-surj {tri}  false = ⟨ [ false , false ] , refl ⟩
decode-surj {tri}  true  = ⟨ [ false , true  ] , refl ⟩
decode-surj {tri}  dc    = ⟨ [ true  , true  ] , refl ⟩

decode-surj {bool} b     = ⟨ [ b ] , refl ⟩

open import Data.Nat using (zero; suc; _+_) public
open import Data.List using (map; zip) public
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩) public
open import Function using (_∘_) public

sizes : (Γ : List Ty) → ℕ
sizes []       = zero
sizes (σ ∷ σs) = size σ + sizes σs

genBL : (n : ℕ) → List Ty
genBL n = replicate n bool

genB : (n : ℕ) → List (Vals (genBL n))
genB zero    = [ [] ]
genB (suc n) = map (false ∷_) (genB n) ++ map (true ∷_) (genB n)

genBL-++ : (m n : ℕ) → genBL (m + n) ≡ genBL m ++ genBL n
genBL-++ zero    n = refl
genBL-++ (suc m) n = cong (bool ∷_) (genBL-++ m n)

gBLs≡tBΓ : genBL (sizes Γ) ≡ toBools Γ
gBLs≡tBΓ {[]} = refl
gBLs≡tBΓ {σ ∷ σs} =
  begin
    genBL (sizes (σ ∷ σs))
  ≡⟨⟩
    genBL (size σ + sizes σs)
  ≡⟨ genBL-++ (size σ) (sizes σs) ⟩
    genBL (size σ) ++ genBL (sizes σs)
  ≡⟨ cong (genBL (size σ) ++_) (gBLs≡tBΓ {σs}) ⟩
    genBL (size σ) ++ toBools σs
  ≡⟨⟩
    toBool σ ++ toBools σs
  ≡⟨⟩
    toBools (σ ∷ σs)
  ∎

genBΓ : (Γ : List Ty) → List (Vals (toBools Γ))
genBΓ Γ rewrite cong (λ pf → List (Vals pf)) (sym (gBLs≡tBΓ {Γ}))
  = genB (sizes Γ)

genOpVals : (op : Op Γ τ) → List (Vals (toBools Γ) × Vals (toBool τ))
genOpVals {Γ} {τ} op = map (λ is → ⟨ is , (encode″ ∘ Op⟦ op ⟧ ∘ decodes Γ) is ⟩) (genBΓ Γ)
                 where encode″ : Ty⟦ τ ⟧ → Vals (toBool τ)
                       encode″ v with decode-surj v
                       ...          | ⟨ bv , _ ⟩ = bv

--------------------------
data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : ∀{x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

_++A_ : {A : Set} {P : A → Set} {xs ys : List A}
      → All P xs → All P ys → All P (xs ++ ys)
[]       ++A ys = ys
(x ∷ xs) ++A ys = x ∷ (xs ++A ys)

replicate-allBool : (n : ℕ) → All (_≡ bool) (replicate n bool)
replicate-allBool zero    = []
replicate-allBool (suc n) = refl ∷ replicate-allBool n

toBool-allBool : All (_≡ bool) (toBool τ)
toBool-allBool {τ} = replicate-allBool (size τ)

toBools-allBool : All (_≡ bool) (toBools Γ)
toBools-allBool {[]}     = []
toBools-allBool {σ ∷ σs} = toBool-allBool {σ} ++A toBools-allBool {σs}

{-
toList : All (_≡ bool) Γ → Vals Γ → List Bool
toList []          []       = []
toList (refl ∷ pf) (v ∷ vs) = v ∷ toList pf vs
-}
--------------------------
open import Data.Vec using (Vec; []; _∷_) renaming (map to mapV; replicate to replicateV)

invert : Bool → Bool
invert true  = false
invert false = true

invertVals : All (_≡ bool) Γ → Vals Γ → Vals Γ
invertVals []          []       = []
invertVals (refl ∷ pf) (v ∷ vs) = invert v ∷ invertVals pf vs

splits″ : (n : ℕ) → List (Vals Γ × Vals (genBL n)) → List (Vec (Vals Γ × Bool) (size τ))

splits′ : List (Vals Γ × Vals (toBool τ)) → Vec (List (Vals Γ × Bool)) (size τ)


filter′ : List (Vals Γ × Bool) → List (Vals Γ)
filter′ []                  = []
filter′ (⟨ v , false ⟩ ∷ vs) = v ∷ filter′ vs
filter′ (⟨ _ , true  ⟩ ∷ vs) = filter′ vs

genCnf′ : List (Vals (toBools Γ)) → Cnf Γ
genCnf′ []       = triv (triv trueC)
genCnf′ (v ∷ vs) = {!!}

genCnf : (op : Op Γ τ) → Vec (Cnf Γ) (size τ)
genCnf {Γ} {τ} op = mapV (genCnf′ ∘ (map (invertVals (toBools-allBool {Γ}))) ∘ filter′) (splits′ (genOpVals op))

{-
open import Data.Empty using (⊥; ⊥-elim)
¬_ : Set → Set
¬ A = A → ⊥

size≠0 : ¬ (size τ ≡ zero)
size≠0 {bool} ()
size≠0 {tri}  ()
-}

genCirc′ : {n : ℕ} → Vec (Cnf Γ) n → Circ (toBools Γ) (genBL n)
genCirc′ []       = ret []
genCirc′ (v ∷ vs) = cnfCirc v ++Cr genCirc′ vs

genCirc : Vec (Cnf Γ) (size τ) → Circ (toBools Γ) (toBool τ)
genCirc v = genCirc′ v
-}
------------------------------------------------

encodeOp : Op Γ τ → Circ (toBools Γ) (toBools [ τ ])
encodeOp andT = cnfCirc {[ tri , tri ]} γn ++Cr cnfCirc {[ tri , tri ]} cn
              where γn = conj (disj (pos i11) (triv (pos i21)))
                         (conj (disj (pos i11) (triv (pos i12)))
                         (triv (disj (pos i21) (triv (pos i22)))))

                    cn = conj (triv (pos i12))
                         (triv (triv (pos i22)))
encodeOp ≡C   = cnfCirc {[ tri , tri ]} cn
              where cn = conj (disj (pos i11) (triv (neg i21)))
                         (conj (disj (pos i11) (disj (pos i12) (triv (neg i22))))
                         (triv (disj (pos i11) (disj (neg i12) (triv (pos i22))))))

encodeOp andB = oper andB
encodeOp orB  = oper orB
encodeOp notB = oper notB

-- encodeOp trueC = oper trueC

-- encodeOp op = genCirc (genCnf op)
