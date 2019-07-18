module ArgPrelude where

open import Data.Bool
open import Data.List
open import Level renaming (zero to lzero; suc to lsuc)

-- boolean filter

filterb : ∀ {ℓ} {A : Set ℓ} → (P : A → Bool) → List A → List A
filterb P [] = []
filterb P (x ∷ xs) with P x
... | true = x ∷ filterb P xs
... | false = filterb P xs

