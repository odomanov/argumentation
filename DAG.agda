-- Direct Acyclic Graph

open import LabelAlgebra renaming (⊤ to LA⊤; ⊥ to LA⊥) 

module DAG {c ℓ₁ ℓ₂} (la : LabelAlgebra c ℓ₁ ℓ₂) where

open import Data.Bool
open import Data.Empty using (⊥)
open import Data.Fin as Fin
  using (Fin; Fin′; zero; suc; #_; toℕ; _≟_) renaming (_ℕ-ℕ_ to _-_)
open import Data.Float
open import Data.Graph.Acyclic as Ac public
open import Data.List as List using (List; []; _∷_)
open import Data.Maybe
open import Data.Nat as Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String renaming (_++_ to _+++_)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.Unit using (⊤)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (yes; no)

open import ArgPrelude 
open import AIF


LNode = Node {la = la}
AContext = Context LNode Role   -- argumentation context
AGraph = Graph LNode Role       -- argumentation graph     

private
  MC = Maybe (Carrier la)

-- applying an operation to the Maybe label (TODO: rewrite with >>=)
_⟪_⟫_ : MC → ((Carrier la) → (Carrier la) → (Carrier la)) → MC → MC
(just v1) ⟪ op ⟫ (just v2) = just (op v1 v2)
_ ⟪ _ ⟫ _ = nothing

-- unary opeation
⟪_⟫_ : ((Carrier la) → (Carrier la)) → MC → MC
⟪ op ⟫ (just v) = just (op v)
⟪ _ ⟫ _ = nothing


-- nodes on which nothing depends (no predecessors)
roots : ∀ {n} → AGraph n → List (Fin n × LNode)
roots ∅ = []
roots {n} g = filterb (P g) (Vec.toList (nodes g))
  where
  P : ∀ {n} → AGraph n → Fin n × LNode → Bool
  P g (i , _) with (preds g i)
  ... | [] = true
  ... | _  = false



-- δi-th graph relative to i  
_[_>_] : ∀ {n} → AGraph (ℕ.suc n) → (i : Fin (ℕ.suc n)) → (δi : Fin (n - i))
         → AGraph _
g [ i > δi ] = Ac.tail (g [ i ]) [ δi ]

-- i-th context
_!_ : ∀ {n} → AGraph n → (i : Fin n) → AContext (n - suc i)
g ! i = Ac.head (g [ i ])

-- δi-th context relative to i  
_![_>_] : ∀ {n} → AGraph (ℕ.suc n) → (i : Fin (ℕ.suc n)) → (δi : Fin (n - i))
          → AContext _ 
_![_>_] g i δi = Ac.head (Ac.tail (g [ i ]) [ δi ])


-- extracting info from the i-th context

isInode : LNode → Bool
isInode (Ln (In _) _) = true
isInode _ = false

isRAnode : LNode → Bool
isRAnode (Ln (Sn (SR _)) _) = true
isRAnode _ = false

isCAnode : LNode → Bool
isCAnode (Ln (Sn (SC _)) _) = true
isCAnode _ = false

isPAnode : LNode → Bool
isPAnode (Ln (Sn (SP _)) _) = true
isPAnode _ = false

value : LNode → MC
value (Ln _ v) = v

-- LNode of the i-th context
LNode←Ctx : ∀ {n} → AGraph n → Fin n → LNode
LNode←Ctx g i = label (g ! i)

-- Algebra label from the node of the i-th context
val←Ctx : ∀ {n} → AGraph n → Fin n → MC
val←Ctx g i = value (LNode←Ctx g i)

-- successors data of the i-th context
sucs←Ctx : ∀ {n} → AGraph n → (i : Fin n) → List (Role × Fin (n - suc i))
sucs←Ctx g i = successors (g ! i )


-- extract δi-th role from the successors list
Role←sucs : ∀ {n} → List (Role × Fin n) → Fin n → Maybe Role
Role←sucs [] _ = nothing
Role←sucs (x ∷ xs) δi with (δi Fin.≟ proj₂ x)
... | yes _ = just (proj₁ x)
... | no _  = Role←sucs xs δi

-- the role of the δi-th edge of the i-th context
Role←Ctx : ∀ {n} → AGraph n → (i : Fin n) → (δi : Fin (n - suc i)) → Maybe Role
Role←Ctx g i δi = Role←sucs (successors (g ! i )) δi
  
isSupport : ∀ {n} → AGraph n → (i : Fin n) → (δi : Fin (n - suc i)) → Bool
isSupport g i δi with Role←Ctx g i δi
... | nothing = false
... | just r = isRAnode (LNode←Ctx (g [ i ]) (suc δi)) ∧ (r === поддержка)

isAttack : ∀ {n} → AGraph n → (i : Fin n) → (δi : Fin (n - suc i)) → Bool
isAttack g i δi with Role←Ctx g i δi
... | nothing = false
... | just r = isRAnode (LNode←Ctx (g [ i ]) (suc δi)) ∧ (r === атака)

-- the list of arguments (RA-nodes) of the i-th context
NArgs : ∀ {n} → AGraph n → (i : Fin n) → List (Role × Fin (n - suc i))
NArgs {n} g i = filterb P (sucs←Ctx g i)
  where
  P : (Role × Fin (n - suc i)) → Bool
  P (_ , δi) = isRAnode (LNode←Ctx (g [ i ]) (suc δi))

-- the list of supports (supporting RA-nodes) of the i-th context
NArgs+ : ∀ {n} → AGraph n → (i : Fin n) → List (Role × Fin (n - suc i))
NArgs+ {n} g i = filterb P (sucs←Ctx g i)
  where
  P : (Role × Fin (n - suc i)) → Bool
  P (_ , δi) = isSupport g i δi 

-- the list of attacks (attacking RA-nodes) of the i-th context
NArgs- : ∀ {n} → AGraph n → (i : Fin n) → List (Role × Fin (n - suc i))
NArgs- {n} g i = filterb P (sucs←Ctx g i)
  where
  P : (Role × Fin (n - suc i)) → Bool
  P (_ , δi) = isAttack g i δi 

-- the list of premises of the i-th context (empty if not RA-node)
NPremises : ∀ {n} → AGraph n → (i : Fin n) → List (Role × Fin (n - suc i))
NPremises {n} g i with isRAnode (LNode←Ctx g i)
... | true  = sucs←Ctx g i
... | false = []


--  calculating algebra values  --------------------------------------------

-- fold the list of the i-th successors with functions fex and op.
-- fex extracts MC from the sucs' elements,
-- op comibines the extracted value with the fold's accumulator
foldsucs : ∀ {n} → AGraph n → (i : Fin n)
           → (Role × Fin (n - suc i) → MC)  -- extract MC from sucs
           → (MC → MC → MC)                 -- combine with accumulator
           → MC                             -- starting value
           → List (Role × Fin (n - suc i))
           → MC
foldsucs g i _ _ v [] = v 
foldsucs g i fex op v (x ∷ xs) = (op ∘ fex) x (foldsucs g i fex op v xs)



-- the value of the i-th node computed recursively

{-# TERMINATING #-}    -- I need it because the termination check fails
val : ∀ {n} → AGraph n → (i : Fin n) → MC
val {n} g i with NArgs g i
... | [] = val←Ctx g i
... | _  = foldsucs g i fex (_⟪ _⊕_ la ⟫_) (just (LA⊥ la)) (NArgs+ g i)
           -- Taking Attacks into account
           -- ⟪ _⊕_ la ⟫
           -- (⟪ ⊘ la ⟫ (foldsucs g i fex (_⟪ _⊕_ la ⟫_) (just (LA⊥ la)) (NArgs- g i)))
  where
  gg  = Ac.tail (g [ i ])
  ggg = λ δi → Ac.tail (gg [ δi ])

  fex : Role × Fin (n - suc i) → MC
  fex (_ , δi) = foldsucs gg δi
                 (λ x → val (ggg δi) (proj₂ x))  -- extracting values from sucs
                 (_⟪ _⊙_ la ⟫_)
                 (val←Ctx gg δi)
                 (NPremises gg δi)
  
