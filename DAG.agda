-- Direct Acyclic Graph -- with conflicts handling

open import LabelAlgebra renaming (⊤ to LA⊤; ⊥ to LA⊥; _∧_ to _LA∧_; _∨_ to _LA∨_) 

module DAG {c ℓ₁ ℓ₂} (la : LabelAlgebra c ℓ₁ ℓ₂) where

open import Data.Bool
open import Data.Empty using (⊥)
open import Data.Fin as Fin
  using (Fin; Fin′; zero; suc; #_; fromℕ; toℕ; inject₁; inject≤; fold′; _≟_)
  renaming (_ℕ-ℕ_ to _-_)
open import Data.Fin.Properties as Finₚ using (toℕ-inject₁)
open import Data.Graph.Acyclic as Ac hiding (node) public
open import Data.List as List using (List; []; _∷_)
open import Data.Maybe
open import Data.Nat as ℕ renaming (zero to ℕzero; suc to ℕsuc)
open import Data.Nat.Properties
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String as S renaming (_++_ to _+++_)
open import Data.Vec as Vec renaming ([] to []v; _∷_ to _∷v_) hiding ([_]; foldr) 
open import Data.Unit using (⊤)
open import Function using (_∘_; _$_; id)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Relation.Nullary using (yes; no)

-- for debugging
-- open import Debug.Trace
-- open import Data.Nat.Show renaming (show to ℕshow)

open import ArgPrelude hiding (fromℕ) 
open import AIF

MC = Maybe (Carrier la)
MC⊥ = just (LA⊥ la)
MC⊤ = just (LA⊤ la)

ANode    = Node                  -- node
ALNode   = LNode MC              -- labeled node
AContext = Context ALNode Role   -- argumentation context
AGraph   = Graph ALNode Role     -- argumentation graph     
ATree    = Ac.Tree ALNode Role   -- argumentation tree
ALNode3  = LNode (MC × MC × MC)  
ATree3   = Ac.Tree ALNode3 Role 

Sucs : ℕ → Set
Sucs n = List (Role × Fin n)

-- applying a binary operation to the Maybe label (TODO: rewrite with >>=)
_⟪_⟫_ : MC → ((Carrier la) → (Carrier la) → (Carrier la)) → MC → MC
just v1 ⟪ op ⟫ just v2 = just (op v1 v2)
_ ⟪ _ ⟫ _ = nothing

-- same for a unary operation
infixr 10 ⟪_⟫_

⟪_⟫_ : ((Carrier la) → (Carrier la)) → MC → MC
⟪ op ⟫ (just v) = just (op v)
⟪ _ ⟫  nothing  = nothing

infixl 10 _⨂_ _⨁_

_⨂_ : MC → MC → MC
x ⨂ y = x ⟪ _⊗_ la ⟫ y 

_⨁_ : MC → MC → MC
nothing ⨁ just y  = just y 
just x  ⨁ nothing = just x 
nothing ⨁ nothing = nothing 
just x  ⨁ just y  = just (_⊕_ la x y)  

⟪not⟫ = ⟪ ⊘ la ⟫_

⟨_,_⟩ : MC → MC → MC
⟨ x , y ⟩ = x ⟪ op ⟫ y
  where
  op : Carrier la → Carrier la → Carrier la
  op a b = mean la a b 1

⟪mean⟫ : MC → MC → ℕ → MC
⟪mean⟫ nothing   nothing  _ = nothing
⟪mean⟫ nothing  (just va) _ = nothing
⟪mean⟫ (just v)  nothing  _ = nothing
⟪mean⟫ (just v) (just va) n = just (mean la v va n)

⟪adiff⟫ = _⟪ adiff la ⟫_

-- δi-th graph relative to i  
_[_≻_] : ∀ {n} → AGraph (ℕsuc n)
               → (i : Fin (ℕsuc n))
               → (δi : Fin (n - i))
               → AGraph _
g [ i ≻ δi ] = Ac.tail (g [ i ]) [ δi ]

-- i-th context
_!_ : ∀ {n} → AGraph n → (i : Fin n) → AContext (n - suc i)
g ! i = Ac.head (g [ i ])

-- δi-th context relative to i  
_!_≻_ : ∀ {n} → AGraph (ℕsuc n)
                → (i : Fin (ℕsuc n))
                → (δi : Fin (n - i))
                → AContext _ 
g ! i ≻ δi = Ac.head (g [ i ≻ δi ]) --(Ac.tail (g [ i ]) [ δi ])



-- Auxiliary statements

p1 : ∀ n i → (n - suc i) ℕ.≤ n
p1 (ℕsuc n) zero    = ≤-step ≤-refl
p1 (ℕsuc n) (suc i) = ≤-step (p1 n i)

p2 : ∀ n i → ℕsuc ((toℕ i) + (ℕsuc n - i)) ℕ.≤ ℕsuc (ℕsuc n)
p2 0 zero = s≤s (s≤s z≤n)
p2 0 (suc zero) = ≤-reflexive refl
p2 (ℕsuc n)  zero   = s≤s (s≤s (s≤s ≤-refl))
p2 (ℕsuc n) (suc i) = s≤s (s≤s (≤-reflexive (pppp n i)))
  where
  pppp : ∀ n i → toℕ i + (ℕsuc n - i) ≡ ℕsuc n
  pppp 0 zero = refl
  pppp 0 (suc zero) = refl
  pppp (ℕsuc n)  zero = refl
  pppp (ℕsuc n) (suc i) = cong ℕsuc (pppp n i)

p3 : ∀ {n} {i : Fin n} → ℕsuc (ℕsuc (ℕsuc (toℕ i + (n - suc i)))) ℕ.≤ ℕsuc (ℕsuc n)
p3 {ℕsuc n} {zero} = s≤s (s≤s (s≤s ≤-refl))
p3 {ℕsuc n} {suc i} = s≤s (s≤s (s≤s (pppp n i)))
  where
  pppp : ∀ n i → ℕsuc (toℕ i + (n - suc i)) ℕ.≤ n
  pppp (ℕsuc n) zero    = s≤s ≤-refl
  pppp (ℕsuc n) (suc i) = ≤-pred (s≤s (s≤s (pppp n i))) 




-- i₁ and (i₂ + δi₂) denote the same context
theSame : ∀ {n} → Fin n → (i₂ : Fin n) → Fin (n - suc i₂) → Bool
theSame {ℕsuc (ℕsuc _)} i₁ i₂ δi₂ with (toℕ i₁) ℕ.≟ ℕsuc ((toℕ i₂) ℕ.+ (toℕ δi₂))
... | yes _ = true
... | no _  = false
theSame _ _ _ = false  -- for n = 0, 1

-- i, δi → i ("real" index)
_≻_ : ∀ {n} → (i : Fin (ℕsuc n)) → Fin (n - i) → Fin (ℕsuc n)
zero          ≻ δi = inject≤ (suc δi) (s≤s (≤-reflexive refl)) 
(suc zero)    ≻ δi = inject≤ (suc (suc δi)) (s≤s (≤-reflexive refl))
(suc (suc i)) ≻ δi = inject≤ (suc ((suc (suc i)) Fin.+ δi)) p3 

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
ALNode←δi g i δi = ALNode←i g (i ≻ δi)

-- value from the node of the i-th context
val←i : ∀ {n} → AGraph n → Fin n → MC
val←i g i = LNode.value (ALNode←i g i)

-- replace value in context
replaceVal : ∀ {n} → AContext n → MC → AContext n
replaceVal (context (Ln nd _) sucs) v = context (Ln nd v) sucs


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
sucs←δi g i δi = successors (g ! i ≻ δi)


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
roots {n} g = filterb (P g) (Vec.toList (nodes g))
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
roots¬CA {n} g = filterb (P g) (Vec.toList (nodes g))
  where
  P : ∀ {n} → AGraph n → Fin n × ALNode → Bool
  P g (i , nd) with isCAnode nd | (preds¬CA g i)
  ... | true  | _  = false  -- skip CA nodes
  ... | false | [] = true
  ... | false | _  = false


-- fold down on the whole Fin n
{-# TERMINATING #-} 
fold↓ : ∀ {t n}
        → {Ty : Set t}
        → (Fin n → Ty → Ty)
        → Ty  -- initial
        → Ty
fold↓ {n = ℕzero}  f init = init
fold↓ {n = ℕsuc n} f init = fold' f init (fromℕ n)
  where
  fold' : ∀ {t n}
          → {Ty : Set t}
          → (Fin n → Ty → Ty)
          → Ty  -- initial
          → Fin n
          → Ty
  fold' f init zero    = init
  fold' f init (suc i) = f (suc i) (fold' f init (inject₁ i))


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




--   Conflicts  --------------------------------------------

-- 'conflicting' and 'conflicted' indexes
c-ing : ∀ {n} → AGraph n → (ic : Fin n) → Maybe (Fin (n - suc ic))
c-ing {ℕzero} _ _ = nothing
c-ing g ic = RoleIdx←i g ic conflicting

c-ed : ∀ {n} → AGraph n → (ic : Fin n) → Maybe (Fin (n - suc ic))
c-ed g ic = RoleIdx←i g ic conflicted


-- extract the 'conflicted' index for the 'conflicting' i from the (ic-th) CA-node
-- (I don't actually use it)
c-ed←CA : ∀ {n} → AGraph n → (ic : Fin n) → Fin (n - suc ic) → Maybe (Fin (n - suc ic))
c-ed←CA {ℕsuc (ℕsuc (ℕsuc n))} g ic i with c-ing g ic
... | nothing = nothing
... | just δic with theSame (inject≤ i (p1 (ℕsuc (ℕsuc (ℕsuc n))) ic)) ic δic
...           | false = nothing
...           | true = c-ed g ic
c-ed←CA {_} _ _ _ = nothing   -- for n = 0, 1, 2

-- the list of conflicts (= conflicting indexes) of the i-th context
NConflicts : ∀ {n} → AGraph n → Fin n → List (Fin n × Fin n)
NConflicts {ℕzero} _ _ = []
NConflicts {ℕsuc n} g i = fold↓ f (NConflicts0 g i) 
  where
  f : Fin (ℕsuc n) → List (Fin (ℕsuc n) × Fin (ℕsuc n)) → List (Fin (ℕsuc n) × Fin (ℕsuc n))
  f ic l with c-ed g ic
  ... | nothing = l
  ... | just ied with theSame i ic ied | c-ing g ic
  ...            | true | just ing = (ic , ic ≻ ing) ∷ l
  ...            | _    | _ = l

  -- the list of conflicts of the 0-th context
  NConflicts0 : ∀ {n} → AGraph n → Fin n → List (Fin n × Fin n)
  NConflicts0 {ℕsuc n} g i with c-ed g (# 0)
  ... | nothing = []
  ... | just ied with theSame i (# 0) ied | c-ing g (# 0)
  ...            | true | just ing = (# 0 , (inject≤ (suc ing) (s≤s (≤-reflexive refl)))) ∷ []
  ...            | _    | _ = []


-- Conflict iterations

-- replace value in i-th context
replaceInGraph : ∀ {n} → AGraph n → Fin n → MC → AGraph n
replaceInGraph {n} g i v = foldr (λ k → AGraph k) f ∅ g
  where
  f : ∀ {k} → AContext k → AGraph k → AGraph (ℕsuc k)
  f {k} c g with k =ᵇ (n - suc i) 
  ... | true  = (replaceVal c v) & g
  ... | false = c & g

-- the cumulative value of all conflicts of the i-th context
foldConflicts : ∀ {n} → AGraph n → Fin n → MC
foldConflicts {n} g i = List.foldr f MC⊥ (NConflicts g i)
  where
  f : Fin n × Fin n → MC → MC
  f (i1 , i2) v = v ⨁ (val←i g i1 ⨂ val←i g i2)

-- negation of foldConflicts
¬foldConflicts : ∀ {n} → AGraph n → Fin n → MC
¬foldConflicts {n} g i = ⟪ ⊘ la ⟫ foldConflicts g i


zipTree3 : ATree → ATree → ATree → ATree3
zipTree3 (Ac.node (Ln nd1 v1) rts1) (Ac.node (Ln nd2 v2) rts2) (Ac.node (Ln nd3 v3) rts3) 
         = Ac.node (Ln nd1 (v1 , v2 , v3)) (zip' rts1 rts2 rts3)
  where
  zip' : List (Role × ATree) → List (Role × ATree) → List (Role × ATree) → List (Role × ATree3)
  zip' [] [] [] = []
  zip' ((r1 , t1) ∷ rts1) ((r2 , t2) ∷ rts2) ((r3 , t3) ∷ rts3)
     = ((r1 , zipTree3 t1 t2 t3)) ∷ zip' rts1 rts2 rts3
  zip' _ _ _ = []

valTree3 : ATree3 → MC

private
  fff : (Role × ATree3) → MC → MC
  fff (_ , t) v = valTree3 t ⨂ v

-- deduction
foldPremises3 : MC × MC × MC → MC × MC × MC → List (Role × ATree3) → MC
foldPremises3 (nothing , _ , _) (_ , _ , varg) prems = List.foldr fff varg prems
foldPremises3 (just v0 , _ , _) (_ , _ , varg) prems with List.foldr fff varg prems
... | just v  = just v0 ⨂ just v
... | nothing = just v0

-- fold incoming
foldIns3 : MC × MC × MC → List (Role × ATree3) → MC
foldIns3 vroot ins = List.foldr f MC⊥ ins
  where
  f : Role × ATree3 → MC → MC
  f (role "conflicting" , (Ac.node (Ln (Lnr _) _) _)) v = v
  f (role "conflicted"  , (Ac.node (Ln (Lnr _) _) _)) v = v
  f (_ , (Ac.node (Ln (Lnr _) varg) prems)) v = v ⨁ (foldPremises3 vroot varg prems)
  f (_ , (Ac.node _ _)) v = v

{-# TERMINATING #-}
valTree3 (Ac.node (Ln _ (v0 , _ , _)) []) = v0
valTree3 (Ac.node (Ln _ vroot@(nothing , _ , _)) rts) = foldIns3 vroot rts 
valTree3 (Ac.node (Ln _ vroot@(just v0 , _ , _)) rts) = (just v0 ⨁ foldIns3 vroot rts) 

-- gprev currently is not used !
valTree3←i : ∀ {n} → AGraph n → AGraph n → AGraph n → Fin n → MC
valTree3←i g0 gprev g i = valTree3 (zipTree3 (toTree g0 i) (toTree gprev i) (toTree g i))




-- difference for i
valδ : ∀ {n} → AGraph n → AGraph n → Fin n → MC
valδ g0 g i = ⟪adiff⟫ (val←i g i) $ valTree3←i g0 g0 g i ⨂ ⟪not⟫ (foldConflicts' g i)
  where
  foldConflicts' : ∀ {n} → AGraph n → Fin n → MC
  foldConflicts' {n} g i = List.foldr f MC⊥ (NConflicts g i)
    where
    f : Fin n × Fin n → MC → MC
    f (i1 , i2) v = v ⟪ _⊕_ la ⟫ (val←i g i1 ⨂ val←i g i2)

-- среднее от i до zero --- из Fin(n+1) --- max i = # n
Mean′ : ∀ {a n} → (A : Set a) → Fin (ℕsuc n) → Set a
Mean′ {n = n} A i = Mean A (toℕ (suc i))
  
⟪meanv⟫ : ∀ {n i} → Mean′ {n = n} MC i → MC
⟪meanv⟫ {_}      {zero}  (mn1 a) = a
⟪meanv⟫ {ℕsuc n} {suc i} (mn+ nothing  acc) = nothing -- ⟪meanv⟫ acc
⟪meanv⟫ {ℕsuc n} {suc i} (mn+ (just a) acc) = ⟪mean⟫ (just a) (⟪meanv⟫ acc) (toℕ i)


Correctness : ∀ {n} → AGraph n → AGraph n → MC
Correctness {ℕzero} _ _   = nothing
Correctness {ℕsuc n} g0 g = ⟪meanv⟫ $ fold′ Ty f (mn1 (valδ g0 g (# 0))) $ suc (fromℕ n)
  where
  Ty : Fin (ℕsuc (ℕsuc n)) → Set c
  Ty i = Mean′ MC i
  
  f : ∀ i → Mean′ MC (inject₁ i) → Mean′ MC (suc i) 
  f i acc rewrite toℕ-inject₁ i = mn+ (valδ g0 g i) acc 





private
  step' : ∀ {n}
         → AGraph n  -- initial graph
         → AGraph n  -- previous iteration
         → AGraph n  -- current iteration
         → AGraph n  -- next iteration
  step' {ℕzero} ∅ _ _ = ∅
  step' {ℕsuc n} g0 gprev g = foldr (λ k → AGraph k) f ∅ g
    where
    newval : ℕ → MC
    newval k = valTree3←i g0 gprev g (inject≤ (fromℕ (n ∸ k)) (s≤s (m∸n≤m n k)))
               ⨂ ¬foldConflicts gprev (inject≤ (fromℕ (n ∸ k)) (s≤s (m∸n≤m n k)))

    f : ∀ {k} → AContext k → AGraph k → AGraph (ℕsuc k)
    f {k} (context (Ln nd v) sucs) g = context (Ln nd (newval k)) sucs & g

steps : ∀ {n}
        → ℕ         -- number of iterations 
        → AGraph n  -- initial graph
        → AGraph n  -- final iteration
steps 0 g = g
steps 1 g = step' g g g
steps (ℕsuc (ℕsuc i)) g = step' g (steps i g) (steps (ℕsuc i) g) 
