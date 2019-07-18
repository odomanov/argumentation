-- Examples: Direct Acyclic Graph

module ExDAG where

open import Data.Bool
open import Data.Empty
open import Data.Fin as Fin
  using (Fin; Fin′; zero; suc; #_; toℕ; _≟_) renaming (_ℕ-ℕ_ to _-_)
open import Data.Float
-- open import Data.Graph.Acyclic as Ac
open import Data.List as List using (List; []; _∷_)
open import Data.Maybe
open import Data.Nat as Nat using (ℕ)
open import Data.Product
open import Data.String renaming (_++_ to _+++_)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.Unit
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import ArgPrelude 
open import AIF
open import LabelAlgebras
open import ArgSchemes

open import DAG Pref


module Example1 where

  St1 = let t = "St1"
        in record { text = just t; thesis = Th t; weight = 0.5}
  St2 = let t = "St2"
        in record { text = just t; thesis = Th t; weight = 0.5}
  St3 = let t = "St3"
        in record { text = just t; thesis = Th t; weight = 0.5}
  St5 = let t = "St5"
        in record { text = just t; thesis = Th t; weight = 0.5}
  
  N1 : LNode
  N1 = Ln (In record { Body = St1 }) (just (PV 0.6 {refl} {refl}))

  N2 : LNode
  N2 = Ln (In record { Body = St2 }) (just (PV 0.7 {refl} {refl}))

  N3 : LNode
  N3 = Ln (In record { Body = St3 }) nothing -- (just (PV 0.3 {refl} {refl}))

  N4 : LNode
  N4 = Ln (Sn (SR record
       { Premises = (факт) ∷ (объяснение) ∷ []
       ; Conclusion = (вывод)
       -- ; Presumptions = []
       -- ; Exceptions = []
       })) (just (PV 0.8 {refl} {refl}))

  N5 : LNode
  N5 = Ln (In record { Body = St5 }) (just (PV 0.6 {refl} {refl}))

  N6 : LNode
  N6 = Ln (Sn (SR record
       { Premises = (эксперт) ∷ (говорит) ∷ []
       ; Conclusion = (вывод)
       -- ; Presumptions = []
       -- ; Exceptions = []
       })) (just (PV 0.9 {refl} {refl}))

  G1 : AGraph _
  G1 =
       context N2 ((говорит , # 2) ∷ []) &
       context N1 ((эксперт , # 1) ∷ []) &
       context N4 ((вывод , # 0) ∷ []) &
       context N3 [] &
       ∅
  
  _ : nodes G1 ≡ (# 0 , N2) ∷ (# 1 , N1) ∷ (# 2 , N4) ∷ (# 3 , N3) ∷ []
  _ = refl
  
  _ : edges G1 ≡ (# 0 , говорит , # 2) ∷ (# 1 , эксперт , # 1) ∷ (# 2 , вывод , # 0) ∷ []
  _ = refl
  
  _ : G1 [ # 3 ] ≡ (context N3 [] & ∅)
  _ = refl
  
  _ : G1 [ # 2 ] ≡ (context N4 ((вывод , # 0) ∷ []) & context N3 [] & ∅)
  _ = refl
  
  _ : sucs G1 (# 2) ≡ (вывод , # 0) ∷ []
  _ = refl
  
  _ : sucs G1 (# 1) ≡ (эксперт , # 1) ∷ []
  _ = refl
  
  -- N2 ---- <N4> ---+
  --         /        \
  -- N1 ----+          N3
  --         \        /
  -- N5 ---- <N6> ---+
  G2 : AGraph _
  G2 =
       context N3 ((аргумент , # 0) ∷ (аргумент , # 2) ∷ []) &
       context N6 ((факт     , # 3) ∷ (объяснение , # 0) ∷ []) &
       context N5 [] &
       context N4 ((эксперт  , # 1) ∷ (говорит , # 0) ∷ []) &
       context N2 [] &
       context N1 [] &
       ∅

  -- part of G2
  G3 : AGraph _
  G3 =
       context N4 ((эксперт  , # 1) ∷ (говорит , # 0) ∷ []) &
       context N2 [] &
       context N1 [] &
       ∅
  
  _ : nodes G2 ≡ (# 0 , N3) ∷ (# 1 , N6) ∷ (# 2 , N5) ∷ (# 3 , N4)
               ∷ (# 4 , N2) ∷ (# 5 , N1) ∷ []
  _ = refl
  
  _ : edges G2 ≡ (# 0 , аргумент , # 0) ∷ (# 0 , аргумент , # 2)
               ∷ (# 1 , факт , # 3) ∷ (# 1 , объяснение , # 0)
               ∷ (# 3 , эксперт , # 1) ∷ (# 3 , говорит , # 0) 
               ∷ []
  _ = refl
  
  
  _ : preds G2 (# 0) ≡ []
  _ = refl
  
  _ : preds G2 (# 3) ≡ (# 0 , аргумент) ∷ []
  _ = refl
  
  _ : preds G2 (# 5) ≡ (# 1 , факт) ∷ (# 3 , эксперт) ∷ []
  _ = refl


  _ : NArgs G2 (# 0) ≡ (аргумент , # 0) ∷ (аргумент , # 2) ∷ []
  _ = refl
  
  _ : NArgs G2 (# 4) ≡ []
  _ = refl
  
  _ : roots G2 ≡ (# 0 , N3) ∷ []
  _ = refl
  
  _ : G2 [ (# 0) ] ≡ G2
  _ = refl
  
  _ : G2 [ (# 0) > (# 0) ] ≡ G2 [ (# 1) ]
  _ = refl

  -- G3 is a part of G2
  _ : G2 [ (# 0) > (# 2) ] ≡ G3
  _ = refl
  
  -- не доказывается в общем виде
  -- _ : ∀ {n} (g : AGraph n) (i : Fin n) → Ac.tail (g [ i ]) ≡ g [ (suc i) ]
  -- _ = refl
  
  -- хотя частные случаи доказываются:
  _ : tail (G2 [ (# 2) ]) ≡ G3
  _ = refl
  
  _ : G2 [ suc (# 2) ] ≡ G3
  _ = refl
  
  -- indexes
  
  _ : G2 ! (# 0) ≡ context N3 ((аргумент , # 0) ∷ (аргумент , # 2) ∷ [])
  _ = refl
  
  _ : G2 ! (# 1) ≡ context N6 ((факт     , # 3) ∷ (объяснение , # 0) ∷ [])
  _ = refl
  
  _ : G2 ![ (# 0) > (# 0) ] ≡ context N6 ((факт     , # 3) ∷ (объяснение , # 0) ∷ [])
  _ = refl
  
  _ : G2 ![ (# 1) > (# 2) ] ≡ context N2 []
  _ = refl
  


open Example1 

------------------------------------------------------------------------


open import IO

main = run (putStrLn stringToPrint)
  where
  showlabel : Maybe FUnit → String
  showlabel nothing = "NOTHING"
  showlabel (just (mkFUnit x _ _)) = Data.Float.show x

  showBool : Bool → String
  showBool true  = "TRUE"
  showBool false = "FALSE"
  
  stringToPrint = "--------------------------------------------"
    +++ "\nN1 = " +++ showlabel (val G2 (# 5))
    +++ "\nN2 = " +++ showlabel (val G2 (# 4))
    +++ "\nN3 = " +++ showlabel (val G2 (# 0))
    +++ "\nN4 = " +++ showlabel (val G2 (# 3))
    +++ "\nN5 = " +++ showlabel (val G2 (# 2))
    +++ "\nN6 = " +++ showlabel (val G2 (# 1))
    +++ "\nN1+N2 = " +++ showlabel (val←Ctx G2 (# 5) ⟪ _⊕_ Pref ⟫ val←Ctx G2 (# 4))
    +++ "\nN4+N6 = " +++ showlabel (val←Ctx G2 (# 3) ⟪ _⊕_ Pref ⟫ val←Ctx G2 (# 1))
    +++ "\nN1+N5 = " +++ showlabel (val←Ctx G2 (# 5) ⟪ _⊕_ Pref ⟫ val←Ctx G2 (# 2))
    +++ "\nN1.N2 = " +++ showlabel (val←Ctx G2 (# 5) ⟪ _⊙_ Pref ⟫ val←Ctx G2 (# 4))
    +++ "\nN4.N6 = " +++ showlabel (val←Ctx G2 (# 3) ⟪ _⊙_ Pref ⟫ val←Ctx G2 (# 1))
    +++ "\nN1.N5 = " +++ showlabel (val←Ctx G2 (# 5) ⟪ _⊙_ Pref ⟫ val←Ctx G2 (# 2))
