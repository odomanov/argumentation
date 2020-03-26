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
  ℕprem {{A-абдукция}} = 2
  Premises {{A-абдукция}} = факт ∷v объяснение ∷v []v
  Conclusion {{A-абдукция}} = вывод

  A-ad-populum : RA-Scheme
  ℕprem {{A-ad-populum}} = 1
  Premises {{A-ad-populum}} = все-признают ∷v []v
  Conclusion {{A-ad-populum}} = вывод

  A-от-причины-к-следствию : RA-Scheme
  ℕprem {{A-от-причины-к-следствию}} = 2
  Premises {{A-от-причины-к-следствию}} = причина ∷v причинная-связь ∷v []v
  Conclusion {{A-от-причины-к-следствию}} = следствие

  A-LOG-AND : RA-Scheme
  ℕprem {{A-LOG-AND}} = 2
  Premises {{A-LOG-AND}} = AND1 ∷v AND2 ∷v []v
  Conclusion {{A-LOG-AND}} = вывод
  

