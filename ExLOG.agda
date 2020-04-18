-- Examples: Logic

module ExLOG where

open import Data.Bool
open import Data.Char renaming (Char to BChar)
open import Data.Empty
open import Data.Fin as Fin
  using (Fin; Fin′; zero; suc; #_; toℕ; _≟_)
open import Data.List as List using (List; []; _∷_)
open import Data.Maybe
open import Data.Nat as ℕ using (suc; ℕ; _∸_; _⊔_)
open import Data.Nat.Show renaming (show to ℕshow)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String as S renaming (_++_ to _+++_)
open import Data.Vec as Vec using (Vec) renaming ([] to []v; _∷_ to _∷v_)
open import Data.Unit

open import ArgPrelude 
open import AIF
open import LabelAlgebras
open import ArgSchemes


-- la = Pref
-- la = Łuk
-- la = Gödel
la = Product
import DAG; module DAGla = DAG la; open DAGla

node : ∀ {n} → ANode
             → (v : Float) → {0.0 [≤] v ≡ true} → {v [≤] 1.0 ≡ true}
             → Sucs n
             → AContext n
node nd v {p0} {p1} sucs = context (Ln nd (just (V v {p0} {p1}))) sucs

-- value = nothing
node0 : ∀ {n} → ANode → Sucs n → AContext n
node0 nd sucs = context (Ln nd nothing) sucs

T1 = mkFrag "St1"
T2 = mkFrag "St2"
T3 = mkFrag "St3"
T5 = mkFrag "St5"
T7 = mkFrag "St7"

St1  = record { sttext = just T1; stprop = mkProp (Fragment.ftext T1)}
St2  = record { sttext = just T2; stprop = mkProp (Fragment.ftext T2)}
St3  = record { sttext = nothing; stprop = mkProp (Fragment.ftext T3)}
¬St3 = record { sttext = nothing; stprop = NOT (mkProp (Fragment.ftext T3))}
St5  = record { sttext = just T5; stprop = mkProp (Fragment.ftext T5)}
St7  = record { sttext = just T7; stprop = mkProp (Fragment.ftext T7)}

-- Statements / I-nodes
I1  : ANode;  I1 = Lni St1
I2  : ANode;  I2 = Lni St2
I3  : ANode;  I3 = Lni St3
¬I3 : ANode; ¬I3 = Lni ¬St3

-- Schemes / S-nodes
SR1 : ANode; SR1 = Lnr A-LOG-NOT
SC  : ANode; SC  = Lnc record {Conflicting = conflicting; Conflicted = conflicted}



-- I3  ---+
--         \
--         SR1 ---> I2
--         /
-- ¬I3 ---+
G1 : AGraph _
G1 =
     node0 I2  ((противоречие , # 0) ∷ []) &
     node  SR1 1.0 {refl} {refl} ((тезис , # 1) ∷ (отрицание , # 0) ∷ []) & 
     node ¬I3  1.0 {refl} {refl} [] &
     node  I3  0.7 {refl} {refl} [] &
     ∅



G10 = steps 0 G1   --compute G1

G11 = steps 1 G1

G12 = steps 2 G1

G13 = steps 3 G1

G14 = steps 4 G1

G1100 = steps 100 G1



-- I2 ---SC---> I2
G2 : AGraph _
G2 =
     node SC 1.0 {refl} {refl} ((conflicting , # 0) ∷ (conflicted , # 1) ∷ []) & 
     node I2 0.5 {refl} {refl} [] &
     node I1 0.7 {refl} {refl} [] &
     ∅



G20 = steps 0 G2 --compute G2

G21 = steps 1 G2

G22 = steps 2 G2

G23 = steps 3 G2

G24 = steps 4 G2

G2100 = steps 100 G2



-- Graph with 2 opposite conflicts  --------------------------------------------

--   --SC1--
--  /       \
-- I1        I2
--  \       /
--   --SC2--

G7 : AGraph _
G7 =
     node SC 1.0 {refl} {refl} ((conflicted , # 2) ∷ (conflicting , # 1) ∷ []) &
     node SC 1.0 {refl} {refl} ((conflicted , # 0) ∷ (conflicting , # 1) ∷ []) &
     node I2 0.3 {refl} {refl} [] &
     node I1 0.1 {refl} {refl} [] &
     ∅

G70 = steps 0 G7  --compute G7

G71 = steps 1 G7

G72 = steps 2 G7

G73 = steps 3 G7

G74 = steps 4 G7

G7100 = steps 100 G7

G7200 = steps 200 G7






------------------------------------------------------------------------

open import ShowDAG la

open import IO

w = 110
ws = 90 -- "section" title width

printG1 : AGraph 4 → (∀ {n} → AGraph n → Fin n → MC) → String
printG1 g f = "\n  I = "    +++ pprint w (f g (# 3))
          +++ " -I = "    +++ pprint w (f g (# 2))
          +++ " Concl = " +++ pprint w (f g (# 0))
          +++ " SR  = "   +++ pprint w (f g (# 1))
printG2 : AGraph 3 → (∀ {n} → AGraph n → Fin n → MC) → String
printG2 g f = "\n  I1 = " +++ pprint w (f g (# 2))
          +++ " I2 = "   +++ pprint w (f g (# 1))
          +++ " C = "    +++ pprint w (f g (# 0))
printG7 : ℕ → String → AGraph 4 → (AGraph 4 → Fin 4 → MC) → String
printG7 n s g f = "\n" +++ (spaces (0 ⊔ (n ∸ S.length s))) +++ s +++ ": "
          +++ " I = "   +++ pprint w (f g (# 3))
          +++ " -I = "  +++ pprint w (f g (# 2))
          +++ " SC1 = " +++ pprint w (f g (# 1))
          +++ " SC2 = " +++ pprint w (f g (# 0))

main = run (putStrLn stringToPrint)
  where
  wh = 12
  stringToPrint = ""  
    -- +++ ppretty ws (docSection ws "G1 original")
    -- +++ printG1 G1 val←i
    -- +++ ppretty ws (docSection ws "G1 w/o conflicts")
    -- +++ printG1 G1 val
    -- +++ ppretty ws (docSection ws "G1 step 0")
    -- +++ printG1 G10 val←i
    -- +++ ppretty ws (docSection ws "G1 step 1")
    -- +++ printG1 G11 val←i
    -- +++ ppretty ws (docSection ws "G1 step 2")
    -- +++ printG1 G12 val←i
    -- +++ ppretty ws (docSection ws "G1 step 3")
    -- +++ printG1 G13 val←i
    -- +++ ppretty ws (docSection ws "G1 step 4")
    -- +++ printG1 G14 val←i
    -- +++ ppretty ws (docSection ws "G1 step 100")
    -- +++ printG1 G1100 val←i

    -- +++ ppretty ws (docSection ws "G2 original")
    -- +++ printG2 G2 val←i
    -- +++ ppretty ws (docSection ws "G2 w/o conflicts")
    -- +++ printG2 G2 valTree←i
    +++ ppretty ws (docSection ws "G2 step 0")
    +++ printG2 G20 val←i
    +++ ppretty ws (docSection ws "G2 step 1")
    +++ printG2 G21 val←i
    +++ ppretty ws (docSection ws "G2 step 2")
    +++ printG2 G22 val←i
    +++ ppretty ws (docSection ws "G2 step 3")
    +++ printG2 G23 val←i
    +++ ppretty ws (docSection ws "G2 step 4")
    +++ printG2 G24 val←i
    +++ ppretty ws (docSection ws "G2 step 100")
    +++ printG2 G2100 val←i

    +++ "\n\nContradiction degree:   step0 = "
    +++ pprint w (val←i G20 (# 1) ⨂ val←i G20 (# 2))
    +++ " step100 = "
    +++ pprint w (val←i G2100 (# 1) ⨂ val←i G2100 (# 2))

    -- +++ printG7 wh "G7 original" G7 val←i
    -- +++ printG7 wh "G7 w/o conflicts" G7 val
    -- -- +++ printG7 wh "G7 step 0" G70 val←i
    -- -- +++ printG7 wh "G7 step 1" G71 val←i
    -- -- +++ printG7 wh "G7 step 2" G72 val←i
    -- -- +++ printG7 wh "G7 step 3" G73 val←i
    -- -- +++ printG7 wh "G7 step 4" G74 val←i
    -- -- +++ printG7 wh "G7 step 100" G7100 val←i
    -- +++ printG7 wh "G7 step 200" G7200 val←i

    -- +++ printG7 17 "NEG foldConflicts" G7 ¬foldConflicts
    -- +++ printG7 17 "val+conflicts" G7 (val+conflicts G7)
    -- +++ printG7 17 "iterationVal"  G7 (iterationVal G7)

    -- +++ (pprint 110 G7)

