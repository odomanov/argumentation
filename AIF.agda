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
open import Data.Maybe
open import Data.Product
open import Data.String renaming (_++_ to _+++_)
open import Data.Unit using (⊤)
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary

open import ArgPrelude
open import LabelAlgebra   -- nodes are labeled
  renaming (⊤ to LA⊤; ⊥ to LA⊥; _∧_ to _LA∧_; _∨_ to _LA∨_)


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
-- CA-nodes
conflicting  = role "conflicting"
conflicted   = role "conflicted"

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
  []

_≡R_ : Role → Role → Set
role r ≡R role r' = r ≡ r'

_≟R_ : Decidable _≡R_
role r ≟R role r' = r Data.String.≟ r'

instance
  REq : BEq Role
  _===_ {{REq}} (role x) (role y) = x == y


-- TODO: get rid of the dependence on order
private
  _=LR_ : List Role → List Role → Bool
  [] =LR [] = true
  [] =LR _  = false
  _  =LR [] = false
  (role x ∷ xs) =LR (role y ∷ ys) = (x == y) ∧ xs =LR ys
  
_≡LR_ : List Role → List Role → Set
[] ≡LR [] = ⊤
(_ ∷ _)  ≡LR [] = ⊥
[] ≡LR (_ ∷ _)  = ⊥
x ≡LR y = (∀ z → (z ∈ x → z ∈ y)) × (∀ z → (z ∈ y → z ∈ x))


instance
  LREq : BEq (List Role)
  _===_ {{LREq}} x y = x =LR y
  



-- Nodes -------------------------------------------------------


-- first, let's define schemes

record RA-Scheme : Set where
  inductive
  constructor mkRA
  field
    Premises     : List Role 
    Conclusion   : Role 
    -- Presumptions : List Role -- critical questions / условия применимости
    -- Exceptions   : List Role -- critical questions / исключения

record CA-Scheme : Set where
  inductive
  constructor mkCA
  field
    Conflicting : Role
    Conflicted  : Role

record PA-Scheme : Set where
  inductive
  constructor mkPA
  field
    Preferred    : Role 
    Dispreferred : Role

-- two types of nodes:

record I-node : Set where
  constructor mkI
  field
    Body : Statement

data S-node : Set where
  SR : RA-Scheme → S-node
  SC : CA-Scheme → S-node
  SP : PA-Scheme → S-node

open RA-Scheme {{...}} public
open CA-Scheme {{...}} public


-- various equalities

private
  _=RA_ : RA-Scheme → RA-Scheme → Bool
  (mkRA p c) =RA (mkRA p' c') = p === p' ∧ c === c'
  
  _=CA_ : CA-Scheme → CA-Scheme → Bool
  (mkCA x y) =CA (mkCA x' y') = x === x' ∧ y === y'
  
  _=PA_ : PA-Scheme → PA-Scheme → Bool
  (mkPA x y) =PA (mkPA x' y') = x === x' ∧ y === y'

instance
  RAEq : BEq RA-Scheme
  _===_ {{RAEq}} x y = x =RA y
  
instance
  CAEq : BEq CA-Scheme
  _===_ {{CAEq}} x y = x =CA y
  
instance
  PAEq : BEq PA-Scheme
  _===_ {{PAEq}} x y = x =PA y
  


module _ {c ℓ₁ ℓ₂} {la : LabelAlgebra c ℓ₁ ℓ₂} where

  mutual
   
    data Node' : Set where
      Lni : Statement → Node' 
      Lnr : RA-Scheme → Node' 
      Lnc : CA-Scheme → Node' 
      Lnp : PA-Scheme → Node' 

    -- Nodes are labeled. The node's value may be 'nothing'.
    data Node : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
      Ln : Node' → Maybe (Carrier la) → Node

    -- Node equality, boolean.
    private
      _=N'_ : Node' → Node' → Bool
      Lni x1  =N' Lni x2  = x1  === x2 
      Lnr ra1 =N' Lnr ra2 = ra1 === ra2
      Lnc ca1 =N' Lnc ca2 = ca1 === ca2
      Lnp pa1 =N' Lnp pa2 = pa1 === pa2
      _ =N' _ = false

      -- Label value is not checked!
      _=N_ : Node → Node → Bool
      Ln x1 _ =N Ln x2 _ = x1 =N' x2
      
    instance 
      NEq : BEq Node
      _===_ {{NEq}} x y = x =N y

    private
      _=RN_ : (Role × Node) → (Role × Node) → Bool
      (r1 , nd1) =RN (r2 , nd2) = r1 === r2 ∧ nd1 === nd2
    
    instance 
      RNEq : BEq (Role × Node)
      _===_ {{RNEq}} x y = x =RN y

    -- TODO: get rid of the order
    private
      _=LRN_ : List (Role × Node) → List (Role × Node) → Bool
      [] =LRN [] = true
      [] =LRN _  = false
      _  =LRN [] = false
      (x ∷ xs) =LRN (y ∷ ys) = x === y ∧ xs =LRN ys
  
    instance 
      LRNEq : BEq (List (Role × Node))
      _===_ {{LRNEq}} x y = x =LRN y
  



