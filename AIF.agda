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

-- open import Agda.Builtin.Equality.Erase
open import Data.Bool
open import Data.Empty using (⊥)
open import Data.Float
open import Data.List
open import Data.List.Membership.Propositional
open import Data.Maybe
open import Data.Product
open import Data.String renaming (_++_ to _+++_)
open import Data.Unit using (⊤)
open import Function.Equivalence using (_⇔_)
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary

open import ArgPrelude
open import LabelAlgebra renaming (⊤ to LA⊤; ⊥ to LA⊥)  -- nodes are labeled


-- Roles ----------------------------------------------------------


data Role    : Set where
  role : String → Role
  
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
  []

_=R_ : Role → Role → Bool
role r =R role r' with r Data.String.≟ r'
... | yes _ = true
... | no _ = false


instance
  REq : BEq Role
  _===_ {{REq}} x y = x =R y
  
-- TODO: get rid of dependence on order
_=LR_ : List Role → List Role → Bool
[] =LR [] = true
[] =LR _  = false
_  =LR [] = false
(x ∷ xs) =LR (y ∷ ys) = (x =R y) ∧ xs =LR ys

_≡LR_ : List Role → List Role → Set
[] ≡LR [] = ⊤
(_ ∷ _)  ≡LR [] = ⊥
[] ≡LR (_ ∷ _)  = ⊥
-- x ≡LR y = ∀ z → (z ∈ x ⇔ z ∈ y)
x ≡LR y = (∀ z → (z ∈ x → z ∈ y)) × (∀ z → (z ∈ y → z ∈ x))
-- x ≡LR y = (All (λ z → z ∈ y) x) × (All (λ z → z ∈ x) y)





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


-- various equalities

_=RA_ : RA-Scheme → RA-Scheme → Bool
(mkRA p c) =RA (mkRA p' c') = p =LR p' ∧ c === c'

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
   
    -- Nodes are labeled. The node's value may be 'nothing'.
    data Node' : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
      In : I-node → Node'
      Sn : S-node → Node'
   
    data Node : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
      Ln : Node' → Maybe (Carrier la) → Node

    -- Node equality, boolean.
    -- Label value is not checked.
    _=N_ : Node → Node → Bool
    Ln (In (mkI x1)) v1 =N Ln (In (mkI x2)) v2 = x1 === x2 -- ∧ (v1 =L v2)
    Ln (Sn (SR ra1)) _  =N Ln (Sn (SR ra2)) _  = ra1 === ra2
    Ln (Sn (SC ca1)) _  =N Ln (Sn (SC ca2)) _  = ca1 === ca2
    Ln (Sn (SP pa1)) _  =N Ln (Sn (SP pa2)) _  = pa1 === pa2
    _ =N _ = false

    instance 
      NEq : BEq Node
      _===_ {{NEq}} x y = x =N y
  
    _=RN_ : (Role × Node) → (Role × Node) → Bool
    (r1 , nd1) =RN (r2 , nd2) = r1 === r2 ∧ nd1 === nd2
    
    instance 
      RNEq : BEq (Role × Node)
      _===_ {{RNEq}} x y = x =RN y

    -- TODO: get rid of the order
    _=LRN_ : List (Role × Node) → List (Role × Node) → Bool
    [] =LRN [] = true
    [] =LRN _ = false
    _ =LRN [] = false
    (x ∷ xs) =LRN (y ∷ ys) = x === y ∧ xs =LRN ys
  
    instance 
      LRNEq : BEq (List (Role × Node))
      _===_ {{LRNEq}} x y = x =LRN y
  









-- printing functions

instance
  shRole : ShowClass Role
  sh {{shRole}} pre (role r) = pre +++ r 

