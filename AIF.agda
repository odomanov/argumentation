-- Argument Interchange Format

{- 
# Core ontology

- Аргументы / сеть аргументов
- Коммуникация (locutions, protocols)
- Контекст (агенты, теории,...) (от чего зависит смысл)

## Аргументы

- Направленный граф: I-node (information), S-node (scheme).
- 3 типа схем: inference, preference, conflict (RA, PA, CA).
- Рёбра не имеют атрибутов. Их тип и пр. могут быть вычислены.
- 2 типа рёбер: scheme, data.
  + Data Edge: I-node → S-node (информация для схемы)
  + Scheme Edge: S-node → I-node | S-node (вывод / цель схемы)
- 

## Аргументы: Non-Core features

- Атрибуты узлов: текст, тип, сила, полярность (про, контра),...
- типы рёбер: support, attack, inference,...  (?)

## Коммуникация

- Типы локуций: assert, question, challenge,...
- Свойства локуций: автор, адресат, онтологии, язык, протокол, содержание,...

## Контекст

- Коммуникации: Участники, топик, commitment stores,... 
- Аргументации: схемы, теории, онтологии.

-}

module AIF where

open import Data.Bool
open import Data.Empty using (⊥)
open import Data.Float
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Binary.Equality.DecPropositional --Properties --using (≡-dec)
open import Data.List.Properties --using (≡-dec)
open import Data.Maybe
open import Data.Nat as ℕ using (ℕ)
open import Data.Product
open import Data.String as S renaming (_++_ to _+++_)
open import Data.Unit using (⊤; tt)
open import Data.Vec as Vec renaming (_∷_ to _∷v_)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary

open import ArgPrelude
open import LabelAlgebra   -- nodes are labeled
  renaming (⊤ to LA⊤; ⊥ to LA⊥; _∧_ to _LA∧_; _∨_ to _LA∨_)


instance
  ℕEq : BEq ℕ ℕ
  _=ᵇ_ {{ℕEq}} m n = m ℕ.≡ᵇ n
  
-- Roles ----------------------------------------------------------


data Role    : Set where
  role : String → Role

-- RA-nodes
эксперт      = role "эксперт"
говорит      = role "говорит"
область      = role "область"
факт         = role "факт"
объяснение   = role "объяснение"
вывод        = role "вывод"
пример       = role "пример"
все-признают = role "все-признают"
поддержка    = role "поддержка"
атака        = role "атака"
причина      = role "причина"
причинная-связь = role "причинная-связь"
следствие    = role "следствие"
знак         = role "знак"
связь-со-знаком = role "связь-со-знаком"
цель         = role "цель"
альтернатива = role "альтернатива"
неверно      = role "неверно"
верно        = role "верно"
-- CA-nodes
conflicting  = role "conflicting"
conflicted   = role "conflicted"
-- Logic schemes
AND1         = role "AND1"
AND2         = role "AND2"
OR1          = role "OR1"
OR2          = role "OR2"

Roles : List Role
Roles = 
  эксперт    ∷   
  говорит    ∷
  область    ∷
  факт       ∷
  объяснение ∷
  вывод      ∷
  пример     ∷
  все-признают ∷
  поддержка  ∷
  атака      ∷
  conflicting ∷
  conflicted  ∷
  AND1 ∷
  AND2 ∷
  OR1 ∷
  OR2 ∷
  []

_≡R_ : Role → Role → Set
role r ≡R role r' = r ≡ r'

_≟R_ : Decidable _≡R_
role r ≟R role r' = r S.≟ r'

instance
  REq : BEq Role Role
  _=ᵇ_ {{REq}} (role x) (role y) = x S.== y


-- TODO: get rid of the dependence on order
private
  _=LR_ : List Role → List Role → Bool
  [] =LR [] = true
  [] =LR _  = false
  _  =LR [] = false
  (role x ∷ xs) =LR (role y ∷ ys) = (x S.== y) ∧ xs =LR ys
  
_≡LR_ : List Role → List Role → Set
[] ≡LR [] = ⊤
(_ ∷ _)  ≡LR [] = ⊥
[] ≡LR (_ ∷ _)  = ⊥
x ≡LR y = (∀ z → (z ∈ x → z ∈ y)) × (∀ z → (z ∈ y → z ∈ x))

-- _≟LR_ : Decidable _≡LR_
-- x ≟LR y = _≡?_  ? --_≟R_ x y -- ≡-dec ? --? --x y
-- [] ≟LR [] = yes tt
-- (_ ∷ _) ≟LR [] = no λ()
-- [] ≟LR (_ ∷ _) = no λ()
-- (x ∷ xs) ≟LR (y ∷ ys) with x ≟R y | xs ≟LR ys
-- ... | yes p | yes ps = true because (ofʸ ((λ z x₁ → {!p!}) , {!!})) --yes (p , ps)
-- ... | yes _ | no ps = {!!}
-- -- ... | (role )p = yes {!p!}
-- -- x ≟LR y = ∀ (z : Role) → (z ∈? x ⇔ z ∈? y)
-- -- x ≟LR y = (∀ z → ((z ∈? x) → (_∈?_ z y))) × (∀ z → ((z ∈? y) → (_∈?_ z x)))
-- -- x ≟LR y = (All (λ z → z ∈? y) x) × (All (λ z → z ∈? x) y)

instance
  LREq : BEq (List Role) (List Role)
  _=ᵇ_ {{LREq}} x y = x =LR y
  

private
  _=VR_ : ∀ {n m} → Vec Role n → Vec Role m → Bool
  _=VR_ {ℕ.zero} {ℕ.zero} _ _ = true
  _=VR_ {ℕ.zero} {_} _ _ = false
  _=VR_ {_} {ℕ.zero} _ _ = false
  _=VR_ (x ∷v xs) (y ∷v ys) = x =ᵇ y ∧ xs =VR ys

instance
  VREq : ∀ {m n} → BEq (Vec Role m) (Vec Role n)
  _=ᵇ_ {{VREq}} x y = x =VR y


-- Nodes -------------------------------------------------------


-- first, let's define schemes

record RA-Scheme : Set where
  constructor mkRA
  field
    {ℕprem}      : ℕ
    Premises     : Vec Role ℕprem 
    Conclusion   : Role 
    -- Presumptions : List Role -- critical questions / условия применимости
    -- Exceptions   : List Role -- critical questions / исключения

record CA-Scheme : Set where
  constructor mkCA
  field
    Conflicting : Role
    Conflicted  : Role

record PA-Scheme : Set where
  constructor mkPA
  field
    Preferred    : Role 
    Dispreferred : Role

-- two types of nodes:

-- record I-node : Set where
--   constructor mkI
--   field
--     Body : Statement

-- data S-node : Set where
--   SR : RA-Scheme → S-node
--   SC : CA-Scheme → S-node
--   SP : PA-Scheme → S-node

open RA-Scheme {{...}} public
open CA-Scheme {{...}} public
open PA-Scheme {{...}} public


-- various equalities

private
  _=RA_ : RA-Scheme → RA-Scheme → Bool
  _=RA_ (mkRA {n} p c) (mkRA {m} p' c') = n =ᵇ m ∧ p =ᵇ p' ∧ c =ᵇ c'
  
  _=CA_ : CA-Scheme → CA-Scheme → Bool
  (mkCA x y) =CA (mkCA x' y') = x =ᵇ x' ∧ y =ᵇ y'
  
  _=PA_ : PA-Scheme → PA-Scheme → Bool
  (mkPA x y) =PA (mkPA x' y') = x =ᵇ x' ∧ y =ᵇ y'

instance
  RAEq : BEq RA-Scheme RA-Scheme
  _=ᵇ_ {{RAEq}} x y = x =RA y
  
  CAEq : BEq CA-Scheme CA-Scheme
  _=ᵇ_ {{CAEq}} x y = x =CA y
  
  PAEq : BEq PA-Scheme PA-Scheme
  _=ᵇ_ {{PAEq}} x y = x =PA y
  


module _ {c ℓ₁ ℓ₂} {la : LabelAlgebra c ℓ₁ ℓ₂} where

  mutual
   
    data Node : Set where
      Lni : Statement → Node 
      Lnr : RA-Scheme → Node 
      Lnc : CA-Scheme → Node 
      Lnp : PA-Scheme → Node 

    -- Nodes are labeled. The node's value may be 'nothing'.
    record LNode : Set (c l⊔ ℓ₁ l⊔ ℓ₂) where
      constructor Ln
      field
        node  : Node
        value : Maybe (Carrier la)

    -- Node equality, boolean.
    private
      _=N_ : Node → Node → Bool
      Lni x1  =N Lni x2  = x1  =ᵇ x2 
      Lnr ra1 =N Lnr ra2 = ra1 =ᵇ ra2
      Lnc ca1 =N Lnc ca2 = ca1 =ᵇ ca2
      Lnp pa1 =N Lnp pa2 = pa1 =ᵇ pa2
      _ =N _ = false

      -- Label value is not checked!
      _=LN_ : LNode → LNode → Bool
      Ln x1 _ =LN Ln x2 _ = x1 =N x2
      
    instance 
      NEq : BEq LNode LNode
      _=ᵇ_ {{NEq}} x y = x =LN y

    private
      _=RN_ : (Role × LNode) → (Role × LNode) → Bool
      (r1 , nd1) =RN (r2 , nd2) = r1 =ᵇ r2 ∧ nd1 =ᵇ nd2
    
    instance 
      RNEq : BEq (Role × LNode) (Role × LNode)
      _=ᵇ_ {{RNEq}} x y = x =RN y

    -- TODO: get rid of the order
    private
      _=LRN_ : List (Role × LNode) → List (Role × LNode) → Bool
      [] =LRN [] = true
      [] =LRN _  = false
      _  =LRN [] = false
      (x ∷ xs) =LRN (y ∷ ys) = x =ᵇ y ∧ xs =LRN ys
  
    instance 
      LRNEq : BEq (List (Role × LNode)) (List (Role × LNode))
      _=ᵇ_ {{LRNEq}} x y = x =LRN y

    Prop←N : Node → Proposition
    Prop←N (Lni s) = Statement.stprop s
    Prop←N _ = mkProp ""                  -- should I use Maybe?

  record Argument : Set (c l⊔ ℓ₁ l⊔ ℓ₂) where
    constructor mkArg
    field
      Scheme      : RA-Scheme 
      NPremises   : Vec (Maybe LNode) (RA-Scheme.ℕprem Scheme)
      NConclusion : Maybe LNode 

