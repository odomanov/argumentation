open import LabelAlgebra renaming (⊤ to LA⊤; ⊥ to LA⊥; _∧_ to _LA∧_; _∨_ to _LA∨_) 

module ShowDAG {c ℓ₁ ℓ₂} (la : LabelAlgebra c ℓ₁ ℓ₂) where

open import Data.Bool
open import Data.Empty
open import Data.Fin as Fin
  using (Fin; Fin′; zero; suc; #_; toℕ; _≟_) 
open import Data.List as List using (List; []; _∷_)
open import Data.Maybe
open import Data.Nat as ℕ using (suc; ℕ; _⊔_; _∸_)
open import Data.Nat.Show renaming (show to ℕshow)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String as S renaming (_++_ to _+++_)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.Unit
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import ArgPrelude 
open import AIF
open import LabelAlgebras
open import ArgSchemes
open import WLPretty

open import DAG la

docRole : Role → Doc
docRole (role s) = text s

docRoles : ∀ {n} → Vec Role n → Doc
docRoles [] = empty
docRoles (x ∷ []) = docRole x
docRoles (x ∷ xs) = docRole x <> text ", " <> line <> docRoles xs

docProp : Proposition → Doc
docProp (mkProp s) = string s
docProp (NOT x) = text "NOT " <> docProp x
docProp (x AND y) = docProp x <> text " AND " <> docProp y
docProp (x OR  y) = docProp x <> text " OR " <> docProp y

docStmt : Statement → Doc
docStmt (st nothing p) = text "PROP = " <> nest 7 (docProp p)
docStmt (st (just tx) p) = text "TEXT = " <> nest 7 (string tx)
                                  <> line <> nest 7 (ppp p)
  where
  ppp : Proposition → Doc
  ppp (mkProp t) with tx == t
  ... | true  = text "PROP = TEXT"
  ... | false = text "PROP = " <> docProp p
  ppp _ = text "PROP = " <> docProp p

docMC : MC → Doc
docMC nothing = text (" - " +++ spaces 7)
docMC (just x) = text s <> text (spaces (0 ⊔ (10 ∸ S.length s)))
  where
  s = layout (renderPretty 1.0 8 ((doc la) x))

docLabel : MC → Doc
docLabel nothing = text "NOTHING"
docLabel (just x) = (doc la) x 

docNode : ALNode → Doc
docNode (Ln (Lni s) v) = text "I: " <> nest 3 (docStmt s)
  <> line <> group (text "вес   = " <> docLabel v)
docNode (Ln (Lnr (mkRA p c)) v) = text "SR: "
  <> nest 4 (group (docRoles p <> line <> text "=> " <> docRole c))
  <> line <> group (text "вес   = " <> docLabel v)
docNode (Ln (Lnc (mkCA c1 c2)) v) = text "CONFLICT"
  <> line <> group (text "вес   = " <> docLabel v)
docNode (Ln (Lnp (mkPA p1 p2)) v) = text "PREF"
  <> line <> group (text "вес   = " <> docLabel v)

docNodes : ∀ {n} → List (Fin n × ALNode) → Doc
docNodes [] = empty
docNodes ((i , nd) ∷ xs) = text ((ℕshow (toℕ i)) +++ " : ")
                           <> docNode nd <> docNodes xs

docSucs : ∀ {n} → List (Role × Fin n) → Doc
docSucs [] = empty
docSucs ((r , i) ∷ []) = group (docRole r <> text (":" +++ ℕshow (toℕ i)))
docSucs ((r , i) ∷ xs) = group (docRole r <> text (":" +++ ℕshow (toℕ i) +++ ", ")
                                <> line <> docSucs xs)

docCtx : ∀ {n} → AContext n → Doc
docCtx (context nd [])   = nest 2 (docNode nd)
docCtx (context nd sucs) = nest 2 (docNode nd)
  <> nest 2 (line <> text "связи = ( " <> nest 10 (docSucs sucs) <> text " )")

docGraph : ∀ {n} → AGraph n → Doc
docGraph ∅ = empty 
docGraph (ctx & g) = line <> text "& " <> docCtx ctx <> docGraph g


instance
  ppRole : Pretty Role
  pretty {{ppRole}} x = (docRole x)
  pppRole : PPrint Role
  prettytype {{pppRole}} = ppRole

  ppProp : Pretty Proposition
  pretty {{ppProp}} p = (docProp p)
  pppProp : PPrint Proposition
  prettytype {{pppProp}} = ppProp

  ppMC : Pretty MC
  pretty {{ppMC}} = docMC
  pppMC : PPrint MC
  prettytype {{pppMC}} = ppMC

  ppNode : Pretty ALNode
  pretty {{ppNode}} nd = (docNode nd)
  pppNode : PPrint ALNode
  prettytype {{pppNode}} = ppNode

  ppGraph : ∀ {n} → Pretty (AGraph n)
  pretty {{ppGraph}} g = (docGraph g)
  pppGraph : ∀ {n} → PPrint (AGraph n)
  prettytype {{pppGraph}} = ppGraph


