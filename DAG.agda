-- Direct Acyclic Graph -- with conflicts handling

open import LabelAlgebra renaming (⊤ to LA⊤; ⊥ to LA⊥; _∧_ to _LA∧_; _∨_ to _LA∨_) 

module DAG {c ℓ₁ ℓ₂} (la : LabelAlgebra c ℓ₁ ℓ₂) where

open import Agda.Builtin.Float
open import Data.Bool
open import Data.Empty using (⊥)
open import Data.Fin as Fin
  using (Fin; Fin′; zero; suc; #_; toℕ; _≟_) renaming (_ℕ-ℕ_ to _-_)
open import Data.Float
open import Data.Graph.Acyclic as Ac public
open import Data.List as List using (List; []; _∷_)
open import Data.Maybe
open import Data.Nat as ℕ 
open import Data.Nat.Properties
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String renaming (_++_ to _+++_)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.Unit using (⊤)
open import Function using (_∘_; _$_; id)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (yes; no)

-- for debugging
-- open import Debug.Trace
-- open import Data.Nat.Show renaming (show to ℕshow)

open import ArgPrelude 
open import AIF

LNode = Node {la = la}
AContext = Context LNode Role   -- argumentation context
AGraph = Graph LNode Role       -- argumentation graph     

private
  MC = Maybe (Carrier la)

-- applying a binary operation to the Maybe label (TODO: rewrite with >>=)
_⟪_⟫_ : MC → ((Carrier la) → (Carrier la) → (Carrier la)) → MC → MC
(just v1) ⟪ op ⟫ (just v2) = just (op v1 v2)
_ ⟪ _ ⟫ _ = nothing

-- same for an unary opeation
⟪_⟫_ : ((Carrier la) → (Carrier la)) → MC → MC
⟪ op ⟫ (just v) = just (op v)
⟪ _ ⟫ _ = nothing



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


-- TODO: prove these
postulate
  p3 : ∀ {n} {i : Fin n} → ℕ.suc (ℕ.suc (ℕ.suc (toℕ i + (n - suc i)))) ℕ.≤ ℕ.suc (ℕ.suc n)

-- i, δi → i
realIdx : ∀ {n} → (i : Fin n) → Fin (n - suc i) → Fin n
realIdx zero δi = Fin.inject≤ (suc δi) (s≤s (≤-reflexive refl)) 
realIdx (suc zero) δi = Fin.inject≤ (suc (suc δi)) (s≤s (≤-reflexive refl))
realIdx (suc (suc i)) δi = Fin.inject≤ (suc ((suc (suc i)) Fin.+ δi)) p3 

-- should be true, but I can't prove it
-- lm : ∀ n i δi → theSame {n} (realIdx {n} i δi) i δi ≡ true
-- lm .(suc _) zero δi = {!refl!}
-- lm .(suc _) (suc i) δi = {!!}

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

Nvalue : LNode → MC
Nvalue (Ln _ v) = v

-- LNode of the i-th context
LNode←Idx : ∀ {n} → AGraph n → Fin n → LNode
LNode←Idx g i = label (g ! i)

-- Algebra label from the node of the i-th context
val←Idx : ∀ {n} → AGraph n → Fin n → MC
val←Idx g i = Nvalue (LNode←Idx g i)

-- successors data of the i-th context
sucs←Idx : ∀ {n} → AGraph n → (i : Fin n) → List (Role × Fin (n - suc i))
sucs←Idx g i = successors (g ! i )


-- extract δi-th role from the successors list, if exists
Role←sucs : ∀ {n} → List (Role × Fin n) → Fin n → Maybe Role
Role←sucs [] _ = nothing
Role←sucs (x ∷ xs) δi with (δi Fin.≟ proj₂ x)
... | yes _ = just (proj₁ x)
... | no _  = Role←sucs xs δi

-- the role of the δi-th edge of the i-th context, if exists
Role←Idx : ∀ {n} → AGraph n → (i : Fin n) → (δi : Fin (n - suc i)) → Maybe Role
Role←Idx g i δi = Role←sucs (sucs←Idx g i) δi

-- extract the Role's index from the successors list, if exists
RoleIdx←sucs : ∀ {n} → List (Role × Fin n) → Role → Maybe (Fin n)
RoleIdx←sucs [] _ = nothing
RoleIdx←sucs ((r' , δi) ∷ xs) r with (r === r')
... | true  = just δi
... | false = RoleIdx←sucs xs r

-- the role index of the 'Role' edge of the i-th context
RoleIdx←Idx : ∀ {n} → AGraph n → (i : Fin n) → Role → Maybe (Fin (n - suc i))
RoleIdx←Idx g i r = RoleIdx←sucs (sucs←Idx g i) r
  
isSupport : ∀ {n} → AGraph n → (i : Fin n) → (δi : Fin (n - suc i)) → Bool
isSupport g i δi with Role←Idx g i δi
... | nothing = false
... | just r = isRAnode (LNode←Idx (g [ i ]) (suc δi)) ∧ (r === поддержка)

isAttack : ∀ {n} → AGraph n → (i : Fin n) → (δi : Fin (n - suc i)) → Bool
isAttack g i δi with Role←Idx g i δi
... | nothing = false
... | just r = isRAnode (LNode←Idx (g [ i ]) (suc δi)) ∧ (r === атака)

-- the list of arguments (RA-nodes) of the i-th context
NArgs : ∀ {n} → AGraph n → (i : Fin n) → List (Role × Fin (n - suc i))
NArgs {n} g i = filterb P (sucs←Idx g i)
  where
  P : (Role × Fin (n - suc i)) → Bool
  P (_ , δi) = isRAnode (LNode←Idx (g [ i ]) (suc δi))

-- the list of supports (supporting RA-nodes) of the i-th context
NArgs+ : ∀ {n} → AGraph n → (i : Fin n) → List (Role × Fin (n - suc i))
NArgs+ {n} g i = filterb (λ s → isSupport g i (proj₂ s)) (sucs←Idx g i)

-- the list of attacks (attacking RA-nodes) of the i-th context
NArgs- : ∀ {n} → AGraph n → (i : Fin n) → List (Role × Fin (n - suc i))
NArgs- {n} g i = filterb (λ s → isAttack g i (proj₂ s)) (sucs←Idx g i)

-- the list of premises of the i-th context (empty if not RA-node)
NPremises : ∀ {n} → AGraph n → (i : Fin n) → List (Role × Fin (n - suc i))
NPremises {n} g i with isRAnode (LNode←Idx g i)
... | true  = sucs←Idx g i
... | false = []

-- nodes on which nothing depends (no predecessors)
roots : ∀ {n} → AGraph n → List (Fin n × LNode)
roots ∅ = []
roots {n} g = filterb (P g) (Vec.toList (nodes g))
  where
  P : ∀ {n} → AGraph n → Fin n × LNode → Bool
  P g (i , _) with (preds g i)
  ... | [] = true
  ... | _  = false

-- preds skipping conflicts
preds¬CA : ∀ {n} → AGraph n → (i : Fin n) → List (Fin′ i × Role)
preds¬CA g       zero    = []
preds¬CA ((context nd sucs) & g) (suc i) with (isCAnode nd)
... | true  = List.map (Data.Product.map suc id) $ preds¬CA g i
... | false = List._++_ (List.mapMaybe (p i) sucs)
                        (List.map (Data.Product.map suc id) $ preds¬CA g i)
  where
  p : ∀ {n} (i : Fin n) → Role × Fin n → Maybe (Fin′ (suc i) × Role)
  p i (r , j)  with i Fin.≟ j
  p i (r , .i) | yes refl = just (zero , r)
  p i (r , j)  | no _     = nothing

-- nodes on which nothing depends (no predecessors)
-- skipping conflicts
roots¬CA : ∀ {n} → AGraph n → List (Fin n × LNode)
roots¬CA ∅ = []
roots¬CA {n} g = filterb (P g) (Vec.toList (nodes g))
  where
  P : ∀ {n} → AGraph n → Fin n × LNode → Bool
  P g (i , nd) with isCAnode nd | (preds¬CA g i)
  ... | true  | _  = false  -- skip CA nodes
  ... | false | [] = true
  ... | false | _  = false


{-# TERMINATING #-}    -- the termination check fails
-- fold down on the whole Fin n
fold↓ : ∀ {t n}
        → {Ty : Set t}
        → (Fin n → Ty → Ty)
        → Ty  -- initial
        → Ty
fold↓ {n = ℕ.zero}  f init = init
fold↓ {n = ℕ.suc n} f init = fold' f init (Fin.fromℕ n)
  where
  fold' : ∀ {t n}
          → {Ty : Set t}
          → (Fin n → Ty → Ty)
          → Ty  -- initial
          → Fin n
          → Ty
  fold' f init zero    = init
  fold' f init (suc i) = f (suc i) (fold' f init (Fin.inject₁ i))

-- TODO: prove
postulate
  p5 : ∀ {n} {i : Fin n} → ℕ.suc (toℕ {n} i) ≥ Fin.1F

{-# TERMINATING #-}    -- the termination check fails
-- fold up on the whole Fin n
fold↑ : ∀ {t n}
        → {Ty : Set t}
        → (Fin n → Ty → Ty)
        → Ty  -- initial
        → Ty
fold↑ {n = ℕ.zero}  f init = init
fold↑ {n = ℕ.suc n} f init = fold' f init (zero)
  where
  fold' : ∀ {t n}
          → {Ty : Set t}
          → (Fin n → Ty → Ty)
          → Ty  -- initial
          → Fin n
          → Ty
  fold' {n = n} f init i with n - suc i ≥? ℕ.zero
  ... | yes _ = init
  ... | no  _ = f i (fold' f init (Fin.reduce≥ (suc i) p5))


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

{-# TERMINATING #-}    -- because the termination check fails :(
val : ∀ {n} → AGraph n → (i : Fin n) → MC
val {n} g i with NArgs g i
... | [] = val←Idx g i
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
                          (val←Idx gg δi)
                          (NPremises gg δi)
  

-- computing the values of the whole graph (recursively)

-- TODO: prove
postulate
  p6 : ∀ {n k} → (_ : ℕ.suc k ℕ.≤ n) → k ℕ.≤ n
  p7 : ∀ {n k} → ℕ.suc (n ∸ ℕ.suc k) ℕ.≤ n

compute : ∀ {n} → AGraph n → AGraph n
compute {n} g = compute' {n} {_} {≤-reflexive refl} g g
  where
  compute' : ∀ {n k} → {_ : k ℕ.≤ n} → AGraph n → AGraph k → AGraph k
  compute' _ ∅ = ∅
  compute' {n} {k} {p} g0 ((context (Ln nd _) sucs) & g) =
    (context (Ln nd (val g0 (Fin.inject≤ (Fin.fromℕ (n ∸ k)) p7))) sucs)
    & compute' {n} {k ∸ 1} {p6 p} g0 g




--   Conflicts  --------------------------------------------

-- i₁ and (i₂ + δi₂) denote the same context
theSame : ∀ {n} → Fin n → (i₂ : Fin n) → Fin (n - suc i₂) → Bool
theSame {ℕ.suc (ℕ.suc _)} i₁ i₂ δi₂ with (toℕ i₁) ℕ.≟ ℕ.suc ((toℕ i₂) ℕ.+ (toℕ δi₂))
... | yes _ = true
... | no _  = false
theSame {_} _ _ _ = false  -- for n = 0, 1

-- 'conflicting' and 'conflicted' indexes
c-ing : ∀ {n} → AGraph n → (ic : Fin n) → Maybe (Fin (n - suc ic))
c-ing g ic = RoleIdx←Idx g ic conflicting

c-ed : ∀ {n} → AGraph n → (ic : Fin n) → Maybe (Fin (n - suc ic))
c-ed g ic = RoleIdx←Idx g ic conflicted

-- TODO: prove these
postulate
  p1 : ∀ (n i) → (n - suc i) ℕ.≤ n
  p2 : ∀ n i → ℕ.suc ((toℕ i) + (ℕ.suc n - i)) ℕ.≤ ℕ.suc (ℕ.suc n)
  
-- extract the 'conflicted' index for the 'conflicting' i from the (ic-th) CA-node
-- (I don't actually use it)
c-ed←CA : ∀ {n} → AGraph n → (ic : Fin n) → Fin (n - suc ic) → Maybe (Fin (n - suc ic))
c-ed←CA {ℕ.suc (ℕ.suc (ℕ.suc n))} g ic i with c-ing g ic
... | nothing = nothing
... | just δic with theSame (Fin.inject≤ i (p1 (ℕ.suc (ℕ.suc (ℕ.suc n))) ic)) ic δic
...           | false = nothing
...           | true = c-ed g ic
c-ed←CA {_} _ _ _ = nothing   -- for n = 0, 1, 2

-- the list of conflicts (= conflicting indexes) of the i-th context
NConflicts : ∀ {n} → AGraph n → Fin n → List (Fin n)
NConflicts {n} g i = fold↓ f (NConflicts0 g i) 
  where
  f : Fin n → List (Fin n) → List (Fin n)
  f ic l with c-ing g ic
  ... | nothing = l
  ... | just ing with theSame i ic ing | c-ed g ic
  ...            | true | just ied = realIdx ic ied ∷ l
  ...            | _    | _ = l

  -- the list of conflicts of the 0-th context
  NConflicts0 : ∀ {n} → AGraph n → Fin n → List (Fin n)
  NConflicts0 {ℕ.suc n} g i with c-ing g zero
  ... | nothing = []
  ... | just ing with theSame i (# 0) ing | c-ed g (# 0)
  ...            | true | just ied = ((Fin.inject≤ (suc ied) (s≤s (≤-reflexive refl))) ∷ [])
  ...            | _    | _ = []


-- Conflict iterations

replaceVal : ∀ {n} → AContext n → MC → AContext n
replaceVal (context (Ln nd _) sucs) v = context (Ln nd v) sucs

-- -- replace value in i-th context
-- replaceInGraph : ∀ {n} → AGraph n → Fin n → MC → AGraph n
-- replaceInGraph {n} g i v = foldr (λ k → AGraph k) f ∅ g
--   where
--   f : ∀ {k} → AContext k → AGraph k → AGraph (ℕ.suc k)
--   f {k} c g with k ℕ.≟ n - suc i 
--   ... | yes _ = (replaceVal c v) & g
--   ... | no _  = c & g




-- the cumulative value of all conflicts of the i-th context
foldConflicts : ∀ {n} → AGraph n → Fin n → MC
foldConflicts {n} g i = List.foldr f (just (LA⊥ la)) (NConflicts g i)
  where
  f : Fin n → MC → MC
  f i v = v ⟪ _LA∨_ la ⟫ (val g i)


-- iteration step

infixr 4 step_ 

step_ : ∀ {n}
       → AGraph n  -- current iteration
       → AGraph n  -- next iteration
step_ {n} gin = foldr (λ k → AGraph k) (f) ∅ gin
  where
  -- the value of the next iteration
  iterationVal : Fin n → MC
  -- iterationVal i = (val←Idx gin i)
  iterationVal i = (⟪ ½ la ⟫ (val←Idx gin i))
                   ⟪ _⊕_ la ⟫
                   (⟪ ½ la ⟫ ((val gin i)
                              ⟪ _LA∧_ la ⟫
                              ((just (LA⊤ la)) ⟪ _⊖_ la ⟫ (foldConflicts gin i))
                             )
                   )

  f : ∀ {k} → AContext k → AGraph k → AGraph (ℕ.suc k)
  f {k} c g = (replaceVal c (iterationVal (Fin.inject≤ (Fin.fromℕ (n ∸ (ℕ.suc k))) p7))) & g

