module ArgSchemes where

open import Data.Bool
open import Data.Empty
open import Data.Float
open import Data.List
open import Data.Maybe
open import Data.String renaming (_++_ to _+++_)
open import Data.Unit
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
  Premises {{A-от-эксперта}} = (эксперт) ∷ (говорит) ∷ (область) ∷ []
  Conclusion {{A-от-эксперта}} = вывод

  A-от-примера : RA-Scheme
  Premises {{A-от-примера}} = (пример) ∷ []
  Conclusion {{A-от-примера}} = вывод

  A-абдукция : RA-Scheme
  Premises {{A-абдукция}} = (факт) ∷ (объяснение) ∷ []
  Conclusion {{A-абдукция}} = вывод

  A-ad-populum : RA-Scheme
  Premises {{A-ad-populum}} = (все-признают) ∷ []
  Conclusion {{A-ad-populum}} = вывод
  


-- Печать цели / вывода



concl-line = "----------"
dpre : String → String
dpre pre = pre +++ pre
npre : String → String
npre pre = "\n" +++ pre


