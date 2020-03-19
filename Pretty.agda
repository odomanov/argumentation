module Pretty where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; if_then_else_)
open import Data.Char renaming (Char to BChar) 
open import Data.Float public hiding (_==_; _-_; _+_)
open import Data.Integer hiding (_*_)
open import Data.List as L
open import Data.Maybe
open import Data.Nat as ℕ using (suc; ℕ; _∸_; _⊔_)
open import Data.Nat.Show renaming (show to ℕshow)
open import Data.String as S using (String) renaming (_++_ to _+++_)
open import Function using (id; _∘_)

open import Text.Pretty 110 public 

-- Pretty printer combinators

nest : ℕ → Doc → Doc
nest n d = spaces n <> d

hang : ℕ → Doc → Doc → Doc
hang n x y = (x <> y) <|> (x $$ nest n y)

private
  -- split a character list at the character ci as a separator
  splitCL : BChar → List BChar → List (List BChar)
  splitCL ci cs with cs
  ... | [] = []
  ... | (c ∷ []) = if c Data.Char.== ci then [] else (c ∷ []) ∷ []
  splitCL ci cs | (c1 ∷ c2 ∷ css) = step ci c1 c2 (splitCL ci (c2 ∷ css))
    where
    -- add c1 taking into account c2
    step : BChar → BChar → BChar → List (List BChar) → List (List BChar)
    step ci c1 c2 cs with ci Data.Char.== c1 | ci Data.Char.== c2 | cs
    ... | true | _    | _        = cs
    ... | _    | true | _        = (c1 ∷ []) ∷ cs     -- start a new list
    ... | _    | _    | []       = (c1 ∷ []) ∷ [] 
    ... | _    | _    | (x ∷ xs) = (c1 ∷ x) ∷ xs      -- add to the existing list

-- split at space
words : String → List String
words s = L.map S.fromList (splitCL ' ' (S.toList s))

-- split at newline
lines : String → List String
lines s = L.map S.fromList (splitCL '\n' (S.toList s))

infixr 5 _</>_
_</>_ : Doc → Doc → Doc
x </> y = x <> newline <> y

fillwords : String → Doc
fillwords = foldDoc _</>_ ∘ L.map text ∘ words

-- replaces spaces and newlines with corresponding Docs
string : String → Doc
string = foldDoc _</>_ ∘ L.map fillwords ∘ lines

bool : Bool → Doc
bool true  = text ("true")
bool false = text ("false")

nat : ℕ → Doc
nat i = text (ℕshow i)

integer : ℤ → Doc
integer i = text (Data.Integer.show i)

float : Float → Doc
float f = text (Data.Float.show f)

-- TODO: add align
encloseSep : Doc → Doc → Doc → List Doc → Doc
encloseSep left right sep [] = left <> right
encloseSep left right sep (x ∷ []) = left <> x <> right 
-- encloseSep left right sep xs = left <> ssep sep xs <> right
encloseSep left right sep xs = left <> foldDoc (λ x y → x <> sep <> y) xs <> right
  --align (cat (zipWith _<>_ (left ∷ repeat sep) ds) <> right)
  -- where
  -- fsep : Doc → Doc → Doc 
  -- fsep x y = x <> sep <> y  
  -- ssep : Doc → List Doc → Doc
  -- ssep _   [] = empty
  -- ssep _   (x ∷ []) = x
  -- ssep sep (x ∷ xs) = x <> sep <> ssep xs

list : List Doc → Doc
list = encloseSep lbracket rbracket comma

tupled : List Doc → Doc
tupled = encloseSep lparen rparen comma

semiBraces : List Doc → Doc
semiBraces = encloseSep lbrace rbrace semi


-----------------------------------------------------------
-- overloading "pretty", the Pretty class
-----------------------------------------------------------

record Pretty {a} (A : Set a) : Set a where
  field
    pretty        : A → Doc
  prettyList : List A → Doc
  prettyList = list ∘ L.map pretty

open Pretty {{...}} public

instance
  ppList : {A : Set} {p : Pretty A} → Pretty (List A) 
  pretty {{ppList {p = p}}} = Pretty.prettyList p 

  ppDoc : Pretty Doc 
  pretty {{ppDoc}} = id

  ppBool : Pretty Bool 
  pretty {{ppBool}} b = bool b

  ppChar : Pretty BChar 
  pretty {{ppChar}} c = char c

  ppString : Pretty String 
  pretty {{ppString}} s = text s

  ppℕ : Pretty ℕ 
  pretty {{ppℕ}} i = nat i

  ppℤ : Pretty ℤ
  pretty {{ppℤ}} i = integer i

  ppFloat : Pretty Float 
  pretty {{ppFloat}} f = float f

  ppMaybe : {A : Set} {p : Pretty A} → Pretty (Maybe A) 
  pretty {{ppMaybe}} nothing  = empty
  pretty {{ppMaybe {p = p}}} (just x) = (Pretty.pretty p) x

  -- instance (Pretty a,Pretty b) => Pretty (a,b) where
    -- pretty (x,y) = tupled [pretty x, pretty y]
  
  -- instance (Pretty a,Pretty b,Pretty c) => Pretty (a,b,c) where
    -- pretty (x,y,z)= tupled [pretty x, pretty y, pretty z]
  
--------------------------------------------
-- the PPrint class
--------------------------------------------

record PPrint {a} (A : Set a) : Set a where
  field
    prettytype : Pretty A
  pprint : A → String
  pprint x = render (pretty {{prettytype}} x)

open PPrint {{...}} public

