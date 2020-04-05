module ArgSchemes where

open import Data.Bool
open import Data.Empty
open import Data.Float
open import Data.List
open import Data.Maybe
open import Data.String renaming (_++_ to _+++_)
open import Data.Unit
open import Data.Vec renaming ([] to []v;  _∷_ to _∷v_)
open import Function using (id)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary
open import Relation.Nullary.Decidable

open import ArgPrelude
open import AIF


------------  Определение схем аргументов  ----------

-- data Argument : Set 

instance
  A-от-эксперта : RA-Scheme
  ℕprem {{A-от-эксперта}} = 3
  Premises {{A-от-эксперта}} = эксперт ∷v говорит ∷v область ∷v []v
  Conclusion {{A-от-эксперта}} = вывод

  A-от-примера : RA-Scheme
  ℕprem {{A-от-примера}} = 1
  Premises {{A-от-примера}} = пример ∷v []v
  Conclusion {{A-от-примера}} = вывод

  A-абдукция : RA-Scheme
  ℕprem {{A-абдукция}} = 1
  Premises {{A-абдукция}} = факт ∷v []v
  Conclusion {{A-абдукция}} = объяснение

  A-ad-populum : RA-Scheme
  ℕprem {{A-ad-populum}} = 1
  Premises {{A-ad-populum}} = все-признают ∷v []v
  Conclusion {{A-ad-populum}} = вывод

  A-от-причины-к-следствию : RA-Scheme
  ℕprem {{A-от-причины-к-следствию}} = 2
  Premises {{A-от-причины-к-следствию}} = причина ∷v причинная-связь ∷v []v
  Conclusion {{A-от-причины-к-следствию}} = следствие

  A-от-знака : RA-Scheme
  ℕprem {{A-от-знака}} = 2
  Premises {{A-от-знака}} = знак ∷v связь-со-знаком ∷v []v
  Conclusion {{A-от-знака}} = цель

  A-от-альтернативы : RA-Scheme
  ℕprem {{A-от-альтернативы}} = 2
  Premises {{A-от-альтернативы}} = альтернатива ∷v неверно ∷v []v
  Conclusion {{A-от-альтернативы}} = верно

  A-LOG-AND : RA-Scheme
  ℕprem {{A-LOG-AND}} = 2
  Premises {{A-LOG-AND}} = AND1 ∷v AND2 ∷v []v
  Conclusion {{A-LOG-AND}} = вывод
  
  A-LOG-OR : RA-Scheme
  ℕprem {{A-LOG-OR}} = 2
  Premises {{A-LOG-OR}} = OR1 ∷v OR2 ∷v []v
  Conclusion {{A-LOG-OR}} = вывод

  -- отрицание = тезис → ⊥
  A-LOG-NOT : RA-Scheme
  ℕprem {{A-LOG-NOT}} = 2
  Premises {{A-LOG-NOT}} = тезис ∷v отрицание ∷v []v
  Conclusion {{A-LOG-NOT}} = противоречие
    
-- record A-ad-hominem : Set where
--   field
--     плохой-человек : Statement
--     говорит        : Statement
--     вывод          : Statement

-- record A-ad-hominem-arg : Set where
--   inductive
--   field
--     плохой-человек : Statement
--     аргумент       : Argument

-- record A-от-альтернативы : Set where
--   field
--     альтернатива : Statement
--     неверно      : Statement
--     верно        : Statement
    
-- data Argument where
--   `dummy : Argument
--   `от-эксперта : A-от-эксперта → Argument
--   `от-примера : A-от-примера → Argument
--   `от-причины-к-следствию : A-от-причины-к-следствию → Argument
--   `от-следствия-к-причине : A-от-следствия-к-причине → Argument
--   `от-знака : A-от-знака → Argument
--   `абдукция : A-абдукция → Argument
--   `ad-hominem : A-ad-hominem → Argument
--   `ad-hominem-arg : A-ad-hominem-arg → Argument
--   `от-альтернативы : A-от-альтернативы → Argument

-- -- Имена схем

-- AName : Argument → String
-- AName `dummy = "DUMMY ARGUMENT"
-- AName (`от-эксперта _) = "От эксперта"
-- AName (`от-примера _) = "От примера"
-- AName (`от-причины-к-следствию _) = "От причины к следствию"
-- AName (`от-следствия-к-причине _) = "От следствия к причине"
-- AName (`от-знака _) = "От знака"
-- AName (`абдукция _) = "Абдукция"
-- AName (`ad-hominem _) = "Ad hominem (против тезиса)"
-- AName (`ad-hominem-arg _) = "Ad hominem (против аргумента)"
-- AName (`от-альтернативы _) = "От альтернативы"






