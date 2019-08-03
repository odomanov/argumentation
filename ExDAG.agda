-- Examples: Direct Acyclic Graph

module ExDAG where

open import Data.Bool
open import Data.Empty
open import Data.Fin as Fin
  using (Fin; Fin′; zero; suc; #_; toℕ; _≟_) 
open import Data.Float
open import Data.List as List using (List; []; _∷_)
open import Data.Maybe
open import Data.Nat as Nat using (suc; ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
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
        in record { text = just t; thesis = Th t}
  St2 = let t = "St2"
        in record { text = just t; thesis = Th t}
  St3 = let t = "St3"
        in record { text = just t; thesis = Th t}
  St5 = let t = "St5"
        in record { text = just t; thesis = Th t}
  St7 = let t = "St7"
        in record { text = just t; thesis = Th t}
  
  N1 : LNode
  N1 = Ln (In record { Body = St1 }) (just (PV 0.2 {refl} {refl}))

  N2 : LNode
  N2 = Ln (In record { Body = St2 }) (just (PV 0.3 {refl} {refl}))

  N3 : LNode
  N3 = Ln (In record { Body = St3 }) nothing -- (just (PV 0.3 {refl} {refl}))

  N4 : LNode
  N4 = Ln (Sn (SR A-от-эксперта)) (just (PV 0.1 {refl} {refl}))

  N5 : LNode
  N5 = Ln (In record { Body = St5 }) (just (PV 0.6 {refl} {refl}))

  N6 : LNode
  N6 = Ln (Sn (SR A-от-эксперта)) (just (PV 0.4 {refl} {refl}))

  N7 : LNode
  N7 = Ln (In record { Body = St7 }) (just (PV 0.9 {refl} {refl}))

  N8 : LNode
  N8 = Ln (Sn (SR A-ad-populum)) (just (PV 0.8 {refl} {refl}))

  -- N1 ---+
  --        \
  --         N4 ---> N3
  --        /
  -- N2 ---+
  G1 : AGraph _
  G1 =
       context N3 ((поддержка , # 0) ∷ []) &
       context N4 ((эксперт , # 1) ∷ (говорит , # 0) ∷ []) &
       context N2 [] &
       context N1 [] &
       ∅
  
  _ : nodes G1 ≡ (# 0 , N3) ∷ (# 1 , N4) ∷ (# 2 , N2) ∷ (# 3 , N1) ∷ []
  _ = refl
  
  _ : edges G1 ≡ (# 0 , поддержка , # 0) ∷ (# 1 , эксперт , # 1) ∷ (# 1 , говорит , # 0) ∷ []
  _ = refl
  
  _ : G1 [ # 3 ] ≡ (context N1 [] & ∅)
  _ = refl
  
  _ : G1 [ # 2 ] ≡ (context N2 [] & context N1 [] & ∅)
  _ = refl
  
  _ : G1 [ # 1 ] ≡ (context N4 ((эксперт , # 1) ∷ (говорит , # 0) ∷ []) &
       context N2 [] & context N1 [] & ∅)
  _ = refl

  _ : roots G1 ≡ (_ , N3) ∷ []
  _ = refl
  
  _ : sucs G1 (# 1) ≡ (эксперт , # 1) ∷ (говорит , # 0) ∷ []
  _ = refl

  -- the same with implicit numbers
  _ : sucs G1 (# 1) ≡ (эксперт , _) ∷ (говорит , _) ∷ []
  _ = refl

  _ : sucs G1 (# 0) ≡ (поддержка , _) ∷ []
  _ = refl



  -- N2 ---- <N4> ---+
  --         /        \
  -- N1 ----+          N3
  --         \        /
  -- N5 ---- <N6> ---+
  G2 : AGraph _
  G2 =
       context N3 ((поддержка , # 0) ∷ (поддержка , # 2) ∷ []) &
       context N6 ((факт     , # 3) ∷ (объяснение , # 0) ∷ []) &
       context N5 [] &
       context N4 ((эксперт  , # 1) ∷ (говорит , # 0) ∷ []) &
       context N2 [] &
       context N1 [] &
       ∅

  -- part of G2, actually
  G3 : AGraph _
  G3 =
       context N4 ((эксперт  , # 1) ∷ (говорит , # 0) ∷ []) &
       context N2 [] &
       context N1 [] &
       ∅
  
  _ : nodes G2 ≡ (# 0 , N3) ∷ (# 1 , N6) ∷ (# 2 , N5) ∷ (# 3 , N4)
               ∷ (# 4 , N2) ∷ (# 5 , N1) ∷ []
  _ = refl
  
  _ : edges G2 ≡ (# 0 , поддержка , # 0) ∷ (# 0 , поддержка , # 2)
               ∷ (# 1 , факт , # 3) ∷ (# 1 , объяснение , # 0)
               ∷ (# 3 , эксперт , # 1) ∷ (# 3 , говорит , # 0) 
               ∷ []
  _ = refl
  
  
  _ : preds G2 (# 0) ≡ []
  _ = refl
  
  _ : preds G2 (# 3) ≡ (# 0 , поддержка) ∷ []
  _ = refl
  
  _ : preds G2 (# 5) ≡ (# 1 , факт) ∷ (# 3 , эксперт) ∷ []
  _ = refl


  _ : NArgs G2 (# 0) ≡ (поддержка , # 0) ∷ (поддержка , # 2) ∷ []
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
  
  _ : G2 ! (# 0) ≡ context N3 ((поддержка , # 0) ∷ (поддержка , # 2) ∷ [])
  _ = refl
  
  _ : G2 ! (# 1) ≡ context N6 ((факт     , # 3) ∷ (объяснение , # 0) ∷ [])
  _ = refl
  
  _ : G2 ![ (# 0) > (# 0) ] ≡ context N6 ((факт     , # 3) ∷ (объяснение , # 0) ∷ [])
  _ = refl
  
  _ : G2 ![ (# 1) > (# 2) ] ≡ context N2 []
  _ = refl
  



  -- N2 ---- <N4> ---+
  --         /        \
  -- N1 ----+          N3
  --         \        /|
  -- N5 ---- <N6> ---+ |
  --                   |
  -- N7 ---- <N8> -----+
  G4 : AGraph _
  G4 =
       context N3 ((атака , # 0) ∷ (поддержка , # 2) ∷ (поддержка , # 4) ∷ []) &
       context N8 ((все-признают , # 0) ∷ []) &
       context N7 [] &
       context N6 ((факт     , # 3) ∷ (объяснение , # 0) ∷ []) &
       context N5 [] &
       context N4 ((эксперт  , # 1) ∷ (говорит , # 0) ∷ []) &
       context N2 [] &
       context N1 [] &
       ∅

  _ : nodes G4 ≡ (# 0 , N3) ∷ (# 1 , N8) ∷ (# 2 , N7)
               ∷ (# 3 , N6) ∷ (# 4 , N5) ∷ (# 5 , N4)
               ∷ (# 6 , N2) ∷ (# 7 , N1) ∷ []
  _ = refl
  
  -- _ : edges G2 ≡ (# 0 , атака , # 0)
  --              ∷ (# 0 , поддержка , # 2) ∷ (# 0 , поддержка , # 4)
  --              ∷ (# 1 , все-признают , _)
  --              ∷ (# 3 , факт , # 3) ∷ (# 3 , объяснение , # 0)
  --              ∷ (# 5 , эксперт , # 1) ∷ (# 5 , говорит , # 0) 
  --              ∷ []
  -- _ = refl
  
  
  _ : preds G4 (# 0) ≡ []
  _ = refl
  
  _ : preds G4 (# 3) ≡ (# 0 , поддержка) ∷ []
  _ = refl
  
  _ : preds G4 (# 1) ≡ (# 0 , атака) ∷ []
  _ = refl
  
  _ : preds G4 (# 7) ≡ (# 3 , факт) ∷ (# 5 , эксперт) ∷ []
  _ = refl


  -- all inputs
  _ : NArgs G4 (# 0) ≡ (атака , # 0) ∷ (поддержка , # 2) ∷ (поддержка , # 4) ∷ []
  _ = refl

  -- only attacks
  _ : NArgs- G4 (# 0) ≡ (атака , # 0) ∷ []
  _ = refl

  -- only supports
  _ : NArgs+ G4 (# 0) ≡ (поддержка , # 2) ∷ (поддержка , # 4) ∷ []
  _ = refl


  _ : NArgs G4 (# 4) ≡ []
  _ = refl
  
  _ : NArgs+ G4 (# 4) ≡ []
  _ = refl
  
  _ : NArgs- G4 (# 4) ≡ []
  _ = refl
  
  _ : roots G4 ≡ (# 0 , N3) ∷ []
  _ = refl
  
  
  -- indexes
  
  _ : G4 ! (# 0) ≡ context N3 ((атака , _) ∷ (поддержка , _) ∷ (поддержка , _) ∷ [])
  _ = refl
  
  _ : G4 ! (# 3) ≡ context N6 ((факт     , _) ∷ (объяснение , _) ∷ [])
  _ = refl
  
  _ : G4 ![ (# 0) > (# 2) ] ≡ context N6 ((факт     , # 3) ∷ (объяснение , # 0) ∷ [])
  _ = refl
  
  _ : G4 ![ (# 3) > (# 2) ] ≡ context N2 []
  _ = refl
  


open Example1 

------------------------------------------------------------------------

open import ShowDAG

open import IO

main = run (putStrLn stringToPrint)
  where
  stringToPrint = "--------------------------------------------"
    -- +++ sh "\nN1 = " (val G2 (# 5))
    -- +++ sh "\nN2 = " (val G2 (# 4))
    -- +++ sh "\nN3 = " (val G2 (# 0))
    -- +++ sh "\nN4 = " (val G2 (# 3))
    -- +++ sh "\nN5 = " (val G2 (# 2))
    -- +++ sh "\nN6 = " (val G2 (# 1))
    +++ sh "\nN1+N2 = " (val←Ctx G2 (# 5) ⟪ _⊕_ Pref ⟫ val←Ctx G2 (# 4))
    +++ sh "\nN4+N6 = " (val←Ctx G2 (# 3) ⟪ _⊕_ Pref ⟫ val←Ctx G2 (# 1))
    +++ sh "\nN1+N5 = " (val←Ctx G2 (# 5) ⟪ _⊕_ Pref ⟫ val←Ctx G2 (# 2))
    +++ sh "\nN1.N2 = " (val←Ctx G2 (# 5) ⟪ _⊙_ Pref ⟫ val←Ctx G2 (# 4))
    +++ sh "\nN4.N6 = " (val←Ctx G2 (# 3) ⟪ _⊙_ Pref ⟫ val←Ctx G2 (# 1))
    +++ sh "\nN1.N5 = " (val←Ctx G2 (# 5) ⟪ _⊙_ Pref ⟫ val←Ctx G2 (# 2))
    +++ sh "\nN1 = " (val G4 (# 7))
    +++ sh "\nN2 = " (val G4 (# 6))
    +++ sh "\nN3 = " (val G4 (# 0))
    +++ sh "\nN4 = " (val G4 (# 5))
    +++ sh "\nN5 = " (val G4 (# 4))
    +++ sh "\nN6 = " (val G4 (# 3))
    +++ sh "\nN7 = " (val G4 (# 2))
    +++ sh "\nN8 = " (val G4 (# 1))
    +++ "\n============================\n"
    +++ sh "  " G2