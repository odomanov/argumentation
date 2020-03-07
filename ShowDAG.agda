module ShowDAG where

open import Data.Bool
open import Data.Empty
open import Data.Fin as Fin
  using (Fin; Fin′; zero; suc; #_; toℕ; _≟_) 
open import Data.Float
open import Data.List as List using (List; []; _∷_)
open import Data.Maybe
open import Data.Nat as Nat using (suc; ℕ)
open import Data.Nat.Show renaming (show to ℕshow)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String renaming (_++_ to _+++_)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.Unit
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import ArgPrelude 
open import AIF
open import LabelAlgebras
open import ArgSchemes
open import WLPretty

open import DAG Pref

docRole : Role → Doc
docRole (role s) = text s

docRoles : List Role → Doc
docRoles [] = empty
docRoles (x ∷ []) = docRole x
docRoles (x ∷ xs) = docRole x <> text ", " <> docRoles xs

docThesis : String → Thesis → Doc
docThesis _ (Pos (th' pos neg)) = text "THESIS.Pos = "
  <> string pos <> text " / " <> string neg
docThesis _ (Neg (th' pos neg)) = text "THESIS.Neg = "
  <> string pos <> text " / " <> string neg
docThesis tx (Th th) with tx == th
... | true  = text "THESIS = TEXT"
... | false = text "THESIS = " <> nest 9 (string th)

docStmt : Statement → Doc
docStmt (st nothing th) = docThesis "" th
docStmt (st (just tx) th) = text "TEXT   = "
  <> nest 9 (string tx) <> line <> docThesis tx th

docLabel : (Maybe FUnit) → Doc
docLabel nothing = text "NOTHING"
docLabel (just (mkFUnit x _ _)) = text (Data.Float.show x)

docNode : LNode → Doc
docNode (Ln (In (mkI s)) v) = text "I: " <> nest 3 (docStmt s)
  <> line <> group (text "вес   = " <> docLabel v)
docNode (Ln (Sn (SR (mkRA p c))) v) = text "SR: "
  <> nest 4 (group (docRoles p <> line <> text "=> " <> docRole c))
  <> line <> group (text "вес   = " <> docLabel v)
docNode (Ln (Sn (SC (mkCA c1 c2))) v) = text "CONFLICT: "
  <> nest 4 (docRole c1 <> text " --> " <> docRole c2) 
  <> line <> group (text "вес   = " <> docLabel v)
docNode (Ln (Sn (SP (mkPA p1 p2))) v) = text "PREF: "
  <> nest 4 (docRole p1 <> text " --> " <> docRole p2)
  <> line <> group (text "вес   = " <> docLabel v)

docNodes : ∀ {n} → List (Fin n × LNode) → Doc
docNodes [] = empty
docNodes ((i , nd) ∷ xs) = text ((ℕshow (toℕ i)) +++ " : ")
                           <> docNode nd <> docNodes xs

docSucs : ∀ {n} → List (Role × Fin n) → Doc
docSucs [] = empty
docSucs ((r , i) ∷ []) = group (docRole r <> text (":" +++ ℕshow (toℕ i)))
docSucs ((r , i) ∷ xs) = group (docRole r <> text (":" +++ ℕshow (toℕ i) +++ ", ") <> docSucs xs)

docCtx : ∀ {n} → AContext n → Doc
docCtx (context nd sucs) = nest 2 (docNode nd)
  <> nest 2 (line <> text "связи = ( " <> docSucs sucs <> text " )")

docGraph : ∀ {n} → AGraph n → Doc
docGraph ∅ = empty 
docGraph (ctx & g) = line <> text "& " <> docCtx ctx <> docGraph g


instance
  ppRole : Pretty Role
  pretty {{ppRole}} x = (docRole x)
  pppRole : PPrint Role
  prettytype {{pppRole}} = ppRole

  ppThesis : Pretty Thesis
  pretty {{ppThesis}} t = (docThesis "" t)
  pppThesis : PPrint Thesis
  prettytype {{pppThesis}} = ppThesis

  ppNode : Pretty LNode
  pretty {{ppNode}} nd = (docNode nd)
  pppNode : PPrint LNode
  prettytype {{pppNode}} = ppNode

  ppGraph : ∀ {n} → Pretty (AGraph n)
  pretty {{ppGraph}} g = (docGraph g)
  pppGraph : ∀ {n} → PPrint (AGraph n)
  prettytype {{pppGraph}} = ppGraph
  
