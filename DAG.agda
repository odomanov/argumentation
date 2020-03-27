-- Direct Acyclic Graph -- with conflicts handling

open import LabelAlgebra renaming (⊤ to LA⊤; ⊥ to LA⊥; _∧_ to _LA∧_; _∨_ to _LA∨_) 

module DAG {c ℓ₁ ℓ₂} (la : LabelAlgebra c ℓ₁ ℓ₂) where

open import Data.Bool
open import Data.Empty using (⊥)
open import Data.Fin as Fin
  using (Fin; Fin′; zero; suc; #_; toℕ; _≟_) renaming (_ℕ-ℕ_ to _-_)
open import Data.Fin.Patterns as FinP 
open import Data.Graph.Acyclic as Ac public
open import Data.List as List using (List; []; _∷_)
open import Data.Maybe
open import Data.Nat as ℕ renaming (zero to ℕzero; suc to ℕsuc)
open import Data.Nat.Properties
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String as S renaming (_++_ to _+++_)
open import Data.Vec as V renaming ([] to []v; _∷_ to _∷v_) hiding ([_]; foldr) 
open import Data.Unit using (⊤)
open import Function using (_∘_; _$_; id)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Relation.Nullary using (yes; no)

-- for debugging
-- open import Debug.Trace
-- open import Data.Nat.Show renaming (show to ℕshow)

open import ArgPrelude 
open import AIF

ANode = Node {la = la}
ALNode = LNode {la = la}
AContext = Context ALNode Role   -- argumentation context
AGraph = Graph ALNode Role       -- argumentation graph     
AArg = Argument {la = la}

MC = Maybe (Carrier la)
MC⊥ = just (LA⊥ la)
MC⊤ = just (LA⊤ la)

Sucs : ℕ → Set
Sucs n = List (Role × Fin n)

-- applying a binary operation to the Maybe label (TODO: rewrite with >>=)
_⟪_⟫_ : MC → ((Carrier la) → (Carrier la) → (Carrier la)) → MC → MC
(just v1) ⟪ op ⟫ (just v2) = just (op v1 v2)
_ ⟪ _ ⟫ _ = nothing

-- same for a unary operation
⟪_⟫_ : ((Carrier la) → (Carrier la)) → MC → MC
⟪ op ⟫ (just v) = just (op v)
⟪ _ ⟫ _ = nothing



-- δi-th graph relative to i  
_[_>_] : ∀ {n} → AGraph (ℕsuc n)
               → (i : Fin (ℕsuc n))
               → (δi : Fin (n - i))
               → AGraph _
g [ i > δi ] = Ac.tail (g [ i ]) [ δi ]

-- i-th context
_!_ : ∀ {n} → AGraph n → (i : Fin n) → AContext (n - suc i)
g ! i = Ac.head (g [ i ])

-- δi-th context relative to i  
_![_>_] : ∀ {n} → AGraph (ℕsuc n)
                → (i : Fin (ℕsuc n))
                → (δi : Fin (n - i))
                → AContext _ 
g ![ i > δi ] = Ac.head (Ac.tail (g [ i ]) [ δi ])



-- Auxiliary statements

p1 : ∀ n i → (n - suc i) ℕ.≤ n
p1 (ℕsuc n) FinP.0F = ≤-step ≤-refl
p1 (ℕsuc n) (suc i) = ≤-step (p1 n i)

p2 : ∀ n i → ℕsuc ((toℕ i) + (ℕsuc n - i)) ℕ.≤ ℕsuc (ℕsuc n)
p2 0 FinP.0F = s≤s (s≤s z≤n)
p2 0 FinP.1F = ≤-reflexive refl
p2 (ℕsuc n) FinP.0F = s≤s (s≤s (s≤s ≤-refl))
p2 (ℕsuc n) (suc i) = s≤s (s≤s (≤-reflexive (pppp n i)))
  where
  pppp : ∀ n i → toℕ i + (ℕsuc n - i) ≡ ℕsuc n
  pppp 0 FinP.0F = refl
  pppp 0 FinP.1F = refl
  pppp (ℕsuc n) FinP.0F = refl
  pppp (ℕsuc n) (suc i) = cong ℕsuc (pppp n i)

p3 : ∀ {n} {i : Fin n} → ℕsuc (ℕsuc (ℕsuc (toℕ i + (n - suc i)))) ℕ.≤ ℕsuc (ℕsuc n)
p3 {ℕsuc n} {FinP.0F} = s≤s (s≤s (s≤s ≤-refl))
p3 {ℕsuc n} {suc i} = s≤s (s≤s (s≤s (pppp n i)))
  where
  pppp : ∀ n i → ℕsuc (toℕ i + (n - suc i)) ℕ.≤ n
  pppp (ℕsuc n) FinP.0F = s≤s ≤-refl
  pppp (ℕsuc n) (suc i) = ≤-pred (s≤s (s≤s (pppp n i))) 




-- i₁ and (i₂ + δi₂) denote the same context
theSame : ∀ {n} → Fin n → (i₂ : Fin n) → Fin (n - suc i₂) → Bool
theSame {ℕsuc (ℕsuc _)} i₁ i₂ δi₂ with (toℕ i₁) ℕ.≟ ℕsuc ((toℕ i₂) ℕ.+ (toℕ δi₂))
... | yes _ = true
... | no _  = false
theSame _ _ _ = false  -- for n = 0, 1

-- i, δi → i
realIdx : ∀ {n} → (i : Fin n) → Fin (n - suc i) → Fin n
realIdx zero δi = Fin.inject≤ (suc δi) (s≤s (≤-reflexive refl)) 
realIdx (suc zero) δi = Fin.inject≤ (suc (suc δi)) (s≤s (≤-reflexive refl))
realIdx (suc (suc i)) δi = Fin.inject≤ (suc ((suc (suc i)) Fin.+ δi)) p3 

-- should be true, but I can't prove it
-- lm : ∀ n i δi → theSame {n} (realIdx {n} i δi) i δi ≡ true
-- lm .(ℕsuc _) zero δi = {!!}
-- lm .(ℕsuc _) (suc i) δi = {!!}

-- extracting info from the i-th context

isInode : ALNode → Bool
isInode (Ln (Lni _) _) = true
isInode _ = false

isRAnode : ALNode → Bool
isRAnode (Ln (Lnr _) _) = true
isRAnode _ = false

isCAnode : ALNode → Bool
isCAnode (Ln (Lnc _) _) = true
isCAnode _ = false

isPAnode : ALNode → Bool
isPAnode (Ln (Lnp _) _) = true
isPAnode _ = false

tryRAnode : ALNode → Maybe ALNode
tryRAnode n@(Ln (Lnr _) _) = just n
tryRAnode _ = nothing

-- ALNode of the i-th context
ALNode←i : ∀ {n} → AGraph n → Fin n → ALNode
ALNode←i g i = label (g ! i)

ALNode←δi : ∀ {n} → AGraph (ℕsuc n) → (i : Fin (ℕsuc n)) → Fin (n - i) → ALNode
ALNode←δi g i δi = label (g ![ i > δi ])

-- Algebra label from the node of the i-th context
val←i : ∀ {n} → AGraph n → Fin n → MC
val←i g i = LNode.value (ALNode←i g i)


-- successors

-- successors data of the i-th context
sucs←i : ∀ {n} → AGraph n
               → (i : Fin n)
               → Sucs (n - suc i)
sucs←i g i = successors (g ! i )

-- successors data for i, δi
sucs←δi : ∀ {n} → AGraph (ℕsuc n)
                → (i : Fin (ℕsuc n))
                → (δi : Fin (n - i))
                → Sucs (n - i - suc δi)
sucs←δi g i δi = successors (g ![ i > δi ])


-- extract δi-th role from the successors list, if exists
Role←sucs : ∀ {n} → Sucs n → Fin n → Maybe Role
Role←sucs [] _ = nothing
Role←sucs (x ∷ xs) δi with (δi Fin.≟ proj₂ x)
... | yes _ = just (proj₁ x)
... | no _  = Role←sucs xs δi

-- the role of the δi-th edge of the i-th context, if exists
Role←i : ∀ {n} → AGraph n → (i : Fin n) → (δi : Fin (n - suc i)) → Maybe Role
Role←i g i δi = Role←sucs (sucs←i g i) δi

-- extract the Role's index from the successors list, if exists
RoleIdx←sucs : ∀ {n} → Sucs n → Role → Maybe (Fin n)
RoleIdx←sucs [] _ = nothing
RoleIdx←sucs ((r' , δi) ∷ xs) r with (r =ᵇ r')
... | true  = just δi
... | false = RoleIdx←sucs xs r

-- the role index of the 'Role' edge of the i-th context
RoleIdx←i : ∀ {n} → AGraph n → (i : Fin n) → Role → Maybe (Fin (n - suc i))
RoleIdx←i g i r = RoleIdx←sucs (sucs←i g i) r


-- I don't use these two
isSupport : ∀ {n} → AGraph n → (i : Fin n) → (δi : Fin (n - suc i)) → Bool
isSupport g i δi with Role←i g i δi
... | nothing = false
... | just r = isRAnode (ALNode←i (g [ i ]) (suc δi)) ∧ (r =ᵇ поддержка)

isAttack : ∀ {n} → AGraph n → (i : Fin n) → (δi : Fin (n - suc i)) → Bool
isAttack g i δi with Role←i g i δi
... | nothing = false
... | just r = isRAnode (ALNode←i (g [ i ]) (suc δi)) ∧ (r =ᵇ атака)


-- argument for δi-th of the i-th context, if exists
Arg : ∀ {n} → AGraph (ℕsuc n) → (i : Fin (ℕsuc n)) → (δi : Fin (n - i)) → Maybe AArg
Arg {n} g i δi with ALNode←δi g i δi
... | Ln (Lnr s) v = just (mkArg s (premises s) (just (ALNode←i g i)))
  where
  extr : Role → Sucs (n - i - suc δi) → Maybe ALNode
  extr r [] = nothing
  extr r ((r1 , δδi) ∷ xs) with r =ᵇ r1
  ... | true  = just (ALNode←δi (g [ i ]) (suc δi) δδi)
  ... | false = extr r xs

  premises' : ∀ {m} → Vec Role m → Vec (Maybe ALNode) m
  premises' []v = []v
  premises' (r ∷v rs) = extr r (sucs←δi g i δi) ∷v premises' rs

  premises : (s : RA-Scheme) → Vec (Maybe ALNode) (RA-Scheme.ℕprem s)
  premises (mkRA p c) = premises' p
... | _ = nothing


-- the list of arguments (RA-nodes) of the i-th context
NArgs : ∀ {n} → AGraph (ℕsuc n) → (i : Fin (ℕsuc n)) → List AArg
NArgs {ℕzero} _ _ = []
NArgs {n} g i = nargs (sucs←i g i)
  where
  -- list of RA-nodes from sucs
  nargs : Sucs (n - i) → List AArg
  nargs [] = []
  nargs (x ∷ xs) with Arg g i (proj₂ x)
  ... | nothing  = nargs xs
  ... | just arg = arg ∷ nargs xs

-- the list of supports (supporting RA-nodes) of the i-th context
NArgs+ : ∀ {n} → AGraph n → (i : Fin n) → Sucs (n - suc i)
NArgs+ {n} g i = filterb (λ s → isSupport g i (proj₂ s)) (sucs←i g i)

-- the list of attacks (attacking RA-nodes) of the i-th context
NArgs- : ∀ {n} → AGraph n → (i : Fin n) → Sucs (n - suc i)
NArgs- {n} g i = filterb (λ s → isAttack g i (proj₂ s)) (sucs←i g i)

-- the list of premises of the i-th context (empty if not RA-node)
NPremises : ∀ {n} → AGraph n → (i : Fin n) → Sucs (n - suc i)
NPremises {n} g i with isRAnode (ALNode←i g i)
... | true  = sucs←i g i
... | false = []

-- nodes on which nothing depends (no predecessors)
roots : ∀ {n} → AGraph n → List (Fin n × ALNode)
roots ∅ = []
roots {n} g = filterb (P g) (V.toList (nodes g))
  where
  P : ∀ {n} → AGraph n → Fin n × ALNode → Bool
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
roots¬CA : ∀ {n} → AGraph n → List (Fin n × ALNode)
roots¬CA ∅ = []
roots¬CA {n} g = filterb (P g) (V.toList (nodes g))
  where
  P : ∀ {n} → AGraph n → Fin n × ALNode → Bool
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
fold↓ {n = ℕzero}  f init = init
fold↓ {n = ℕsuc n} f init = fold' f init (Fin.fromℕ n)
  where
  fold' : ∀ {t n}
          → {Ty : Set t}
          → (Fin n → Ty → Ty)
          → Ty  -- initial
          → Fin n
          → Ty
  fold' f init zero    = init
  fold' f init (suc i) = f (suc i) (fold' f init (Fin.inject₁ i))


{-# TERMINATING #-}    -- the termination check fails
-- fold up on the whole Fin n
fold↑ : ∀ {t n}
        → {Ty : Set t}
        → (Fin n → Ty → Ty)
        → Ty  -- initial
        → Ty
fold↑ {n = ℕzero}  f init = init
fold↑ {n = ℕsuc n} f init = fold' f init (zero)
  where
  fold' : ∀ {t n}
          → {Ty : Set t}
          → (Fin n → Ty → Ty)
          → Ty  -- initial
          → Fin n
          → Ty
  fold' {n = n} f init i with n - suc i ≥? ℕzero
  ... | yes _ = init
  ... | no  _ = f i (fold' f init (Fin.reduce≥ (suc i) (s≤s z≤n)))


--  calculating algebra values  --------------------------------------------

-- from premises to conclusion

valRA : AArg → MC
valRA (mkArg _ prems concl) = valRA' prems concl
  where
  valRA' : ∀ {n} → Vec (Maybe ALNode) n → Maybe ALNode → MC
  valRA' []v (just (Ln _ (just v))) = just v   -- ok
  valRA' []v (just (Ln _ nothing))  = MC⊤      -- missed conclusion value
  valRA' []v nothing                = nothing  -- missed conclusion itself
  valRA' (nothing  ∷v _) _          = nothing  -- missed premise
  valRA' ((just x) ∷v xs) c = LNode.value x ⟪ _⊙_ la ⟫ valRA' xs c


private
  op : MC → MC → MC
  op (just v1) (just v2) = just ((_⊕_ la) v1 v2)
  op (just v1) nothing   = just v1
  op nothing   (just v2) = just v2
  op nothing   nothing   = nothing
  
  valargs : List AArg → MC
  valargs [] = MC⊥   -- impossible case, actually
  valargs (x ∷ []) with valRA x
  ... | nothing = nothing
  ... | just v  = just v
  valargs (x ∷ xs) with valRA x
  ... | nothing = valargs xs
  ... | just v  = op (just v) (valargs xs)

-- the value of the i-th node computed recursively

val : ∀ {n} → AGraph n → (i : Fin n) → MC
val {ℕzero} _ _ = nothing
val {ℕsuc n} g i with NArgs g i | val←i g i
... | []   | v       = v  
... | args | nothing = valargs args 
... | args | v       = v ⟪ _⊙_ la ⟫ valargs args 



-- computing the values of the whole graph (recursively)

compute : ∀ {n} → AGraph n → AGraph n
compute {n} g = compute' {n} {_} {≤-reflexive refl} g g
  where
  compute' : ∀ {n k} → {k ℕ.≤ n} → AGraph n → AGraph k → AGraph k
  compute' _ ∅ = ∅
  compute' {ℕsuc n} {ℕsuc k} {p} g0 ((context (Ln nd _) sucs) & g) =
    (context (Ln nd (val g0 (Fin.inject≤ (Fin.fromℕ (ℕsuc n ∸ ℕsuc k)) (s≤s (m∸n≤m n k))))) sucs)
    & compute' {ℕsuc n} {k} {≤⇒pred≤ p} g0 g




--   Conflicts  --------------------------------------------

-- 'conflicting' and 'conflicted' indexes
c-ing : ∀ {n} → AGraph n → (ic : Fin n) → Maybe (Fin (n - suc ic))
c-ing g ic = RoleIdx←i g ic conflicting

c-ed : ∀ {n} → AGraph n → (ic : Fin n) → Maybe (Fin (n - suc ic))
c-ed g ic = RoleIdx←i g ic conflicted


-- extract the 'conflicted' index for the 'conflicting' i from the (ic-th) CA-node
-- (I don't actually use it)
c-ed←CA : ∀ {n} → AGraph n → (ic : Fin n) → Fin (n - suc ic) → Maybe (Fin (n - suc ic))
c-ed←CA {ℕsuc (ℕsuc (ℕsuc n))} g ic i with c-ing g ic
... | nothing = nothing
... | just δic with theSame (Fin.inject≤ i (p1 (ℕsuc (ℕsuc (ℕsuc n))) ic)) ic δic
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
  NConflicts0 {ℕsuc n} g i with c-ing g zero
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
--   f : ∀ {k} → AContext k → AGraph k → AGraph (ℕsuc k)
--   f {k} c g with k ℕ.≟ n - suc i 
--   ... | yes _ = (replaceVal c v) & g
--   ... | no _  = c & g

-- the cumulative value of all conflicts of the i-th context
foldConflicts : ∀ {n} → AGraph n → Fin n → MC
foldConflicts {n} g i = List.foldr f MC⊥ (NConflicts g i)
  where
  f : Fin n → MC → MC
  f i v = v ⟪ _LA∨_ la ⟫ (val g i)

-- negation of foldConflicts
¬foldConflicts : ∀ {n} → AGraph n → Fin n → MC
¬foldConflicts {n} g i = ⟪ ⊘ la ⟫ foldConflicts g i

-- value corrected by conflicts
val+conflicts : ∀ {n} → AGraph n → AGraph n → Fin n → MC
val+conflicts {n} g0 g i = (val g0 i) ⟪ _⊙_ la ⟫ ¬foldConflicts g i

-- iteration steps

-- the value of the next iteration
iterationVal : ∀ {n} → AGraph n → AGraph n → Fin n → MC
-- iterationVal i = (val←i gin i)
iterationVal g0 gin i = (⟪ ½ la ⟫ (val←i gin i))
                        ⟪ _⊕_ la ⟫
                        (⟪ ½ la ⟫ val+conflicts g0 gin i)

private
  step' : ∀ {n}
         → AGraph n  -- initial graph
         → AGraph n  -- current iteration
         → AGraph n  -- next iteration
  step' {ℕzero} ∅ _ = ∅
  step' {ℕsuc n} g0 gin = foldr (λ k → AGraph k) f ∅ gin
    where
    f : ∀ {k} → AContext k → AGraph k → AGraph (ℕsuc k)
    f {k} c g = (replaceVal c (iterationVal g0 gin
      (Fin.inject≤ (Fin.fromℕ (ℕsuc n ∸ (ℕsuc k))) (s≤s (m∸n≤m n k))))) & g

steps : ∀ {n}
        → ℕ         -- number of iterations 
        → AGraph n  -- initial graph
        → AGraph n  -- final iteration
steps  ℕzero   g = compute g
steps (ℕsuc i) g = step' g (steps i g)
