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

open import Agda.Builtin.Equality.Erase
open import Data.Bool
open import Data.Float
open import Data.List
open import Data.Maybe
open import Data.Product
open import Data.String renaming (_++_ to _+++_)
open import Data.Unit
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary
open import Relation.Nullary.Decidable

open import ArgPrelude
open import ArgSchemes
open import LabelAlgebra  -- nodes are labeled


-- Roles ----------------------------------------------------------


data Role    : Set where
  эксперт    : Role
  говорит    : Role
  область    : Role
  факт       : Role
  объяснение : Role
  вывод      : Role
  -- Q1      : Maybe 
  пример     : Role
  аргумент   : Role

-- ugly definition, yes
_=R?_ : Decidable {A = Role} _≡_
эксперт =R? эксперт       = yes refl    
говорит =R? говорит       = yes refl 
область =R? область       = yes refl 
факт =R? факт             = yes refl 
объяснение =R? объяснение = yes refl 
вывод =R? вывод           = yes refl 
пример =R? пример         = yes refl
аргумент =R? аргумент     = yes refl
эксперт =R? говорит       = no λ()
эксперт =R? область       = no λ()       
эксперт =R? факт          = no λ() 
эксперт =R? объяснение    = no λ() 
эксперт =R? вывод         = no λ() 
эксперт =R? пример        = no λ() 
эксперт =R? аргумент      = no λ() 
говорит =R? эксперт       = no λ() 
говорит =R? область       = no λ() 
говорит =R? факт          = no λ() 
говорит =R? объяснение    = no λ() 
говорит =R? вывод         = no λ() 
говорит =R? пример        = no λ() 
говорит =R? аргумент      = no λ() 
область =R? эксперт       = no λ() 
область =R? говорит       = no λ() 
область =R? факт          = no λ() 
область =R? объяснение    = no λ() 
область =R? вывод         = no λ() 
область =R? пример        = no λ() 
область =R? аргумент      = no λ() 
факт =R? эксперт          = no λ() 
факт =R? говорит          = no λ() 
факт =R? область          = no λ() 
факт =R? объяснение       = no λ() 
факт =R? вывод            = no λ() 
факт =R? пример           = no λ() 
факт =R? аргумент         = no λ() 
объяснение =R? эксперт    = no λ() 
объяснение =R? говорит    = no λ() 
объяснение =R? область    = no λ() 
объяснение =R? факт       = no λ() 
объяснение =R? вывод      = no λ() 
объяснение =R? пример     = no λ() 
объяснение =R? аргумент   = no λ() 
вывод =R? эксперт         = no λ() 
вывод =R? говорит         = no λ() 
вывод =R? область         = no λ() 
вывод =R? факт            = no λ() 
вывод =R? объяснение      = no λ() 
вывод =R? пример          = no λ() 
вывод =R? аргумент        = no λ() 
пример =R? эксперт        = no λ() 
пример =R? говорит        = no λ() 
пример =R? область        = no λ() 
пример =R? факт           = no λ() 
пример =R? объяснение     = no λ() 
пример =R? вывод          = no λ() 
пример =R? аргумент       = no λ() 
аргумент =R? эксперт      = no λ() 
аргумент =R? говорит      = no λ() 
аргумент =R? область      = no λ() 
аргумент =R? факт         = no λ() 
аргумент =R? объяснение   = no λ() 
аргумент =R? вывод        = no λ() 
аргумент =R? пример       = no λ() 

_=R_ : Role → Role → Bool
r =R r' with r =R? r'
... | yes _ = true
... | no _ = false

-- TODO: get rid of dependence on order
_=LR_ : List Role → List Role → Bool
[] =LR [] = true
[] =LR _  = false
_  =LR [] = false
(x ∷ xs) =LR (y ∷ ys) = (x =R y) ∧ xs =LR ys


-- Nodes -------------------------------------------------------

record I-node : Set where
  constructor mkI
  field
    Body : Statement

record CA-Scheme : Set where
  inductive
  constructor mkCA
  field
    Conflicting : Role
    Conflicted  : Role

record RA-Scheme : Set where
  inductive
  constructor mkRA
  field
    Premises     : List Role 
    Conclusion   : Role 
    -- Presumptions : List Role -- critical questions / условия применимости
    -- Exceptions   : List Role -- critical questions / исключения

record PA-Scheme : Set where
  inductive
  constructor mkPA
  field
    Preferred    : Role 
    Dispreferred : Role

data S-node : Set where
  SR : RA-Scheme → S-node
  SC : CA-Scheme → S-node
  SP : PA-Scheme → S-node


-- various equalities

_=RA_ : RA-Scheme → RA-Scheme → Bool
(mkRA p c) =RA (mkRA p' c') = p =LR p' ∧ c =R c'

_=CA_ : CA-Scheme → CA-Scheme → Bool
(mkCA x y) =CA (mkCA x' y') = x =R x' ∧ y =R y'

_=PA_ : PA-Scheme → PA-Scheme → Bool
(mkPA x y) =PA (mkPA x' y') = x =R x' ∧ y =R y'



module _ {c ℓ₁ ℓ₂} {la : LabelAlgebra c ℓ₁ ℓ₂} where

  mutual
   
    -- nodes are labeled
    data Node' : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
      In : I-node → Node'
      Sn : S-node → Node'
   
    data Node : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
      Ln : Node' → Maybe (Carrier la) → Node
   
    _=N_ : Node → Node → Bool
    Ln (In (mkI x1)) v1 =N Ln (In (mkI x2)) v2 = x1 =S x2 -- ∧ (v1 =L v2)
    Ln (Sn (SR ra1)) _  =N Ln (Sn (SR ra2)) _  = ra1 =RA ra2
    Ln (Sn (SC ca1)) _  =N Ln (Sn (SC ca2)) _  = ca1 =CA ca2
    Ln (Sn (SP pa1)) _  =N Ln (Sn (SP pa2)) _  = pa1 =PA pa2
    _ =N _ = false

    _=RN_ : (Role × Node) → (Role × Node) → Bool
    (r1 , nd1) =RN (r2 , nd2) = r1 =R r2 ∧ nd1 =N nd2
    
    _=LRN_ : List (Role × Node) → List (Role × Node) → Bool
    [] =LRN [] = true
    [] =LRN _ = false
    _ =LRN [] = false
    (x ∷ xs) =LRN (y ∷ ys) = x =RN y ∧ xs =LRN ys
  






-- printing functions

showRole : Role → String
showRole  эксперт     = "эксперт"   
showRole  говорит     = "говорит"   
showRole  область     = "область"   
showRole  факт        = "факт"      
showRole  объяснение  = "объяснение"
showRole  вывод       = "вывод"     
showRole  пример      = "пример"    
showRole  аргумент    = "аргумент"    
