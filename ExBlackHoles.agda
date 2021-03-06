module ExBlackHoles where

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


T-хорошо-известно =
  mkFrag "Хорошо известно, что в центре практически каждой крупной галактики находится массивная чёрная дыра."
I-хорошо-известно : ANode
I-хорошо-известно = Lni record
  { sttext = just T-хорошо-известно
  ; stprop = mkProp (Fragment.ftext T-хорошо-известно)
  }

T-в-центре-практически-каждой-крупной-галактики-находится-массивная-чёрная-дыра =
  mkFrag "в центре практически каждой крупной галактики находится массивная чёрная дыра"
I-в-центре-практически-каждой-крупной-галактики-находится-массивная-чёрная-дыра : ANode
I-в-центре-практически-каждой-крупной-галактики-находится-массивная-чёрная-дыра = Lni record
  { sttext = just T-в-центре-практически-каждой-крупной-галактики-находится-массивная-чёрная-дыра
  ; stprop = mkProp (Fragment.ftext T-в-центре-практически-каждой-крупной-галактики-находится-массивная-чёрная-дыра)
  }

T-в-то-же-время-самые-тяжёлые-галактики-окружены-самыми-массивными-гало-из-тёмной-материи =
  mkFrag "В то же время самые тяжёлые галактики окружены самыми массивными гало из тёмной материи."
I-самые-тяжёлые-галактики-окружены-самыми-массивными-гало-из-тёмной-материи : ANode
I-самые-тяжёлые-галактики-окружены-самыми-массивными-гало-из-тёмной-материи = Lni record
  { sttext = just T-в-то-же-время-самые-тяжёлые-галактики-окружены-самыми-массивными-гало-из-тёмной-материи
  ; stprop = mkProp "самые тяжёлые галактики окружены самыми массивными гало из тёмной материи"
  }

T-тёмная-материя-играет-ключевую-роль-в-росте-чёрных-дыр =
  mkFrag "тёмная материя играет ключевую роль в росте чёрных дыр"
I-тёмная-материя-играет-ключевую-роль-в-росте-чёрных-дыр : ANode
I-тёмная-материя-играет-ключевую-роль-в-росте-чёрных-дыр = Lni record
  { sttext = just T-тёмная-материя-играет-ключевую-роль-в-росте-чёрных-дыр
  ; stprop = mkProp (Fragment.ftext T-тёмная-материя-играет-ключевую-роль-в-росте-чёрных-дыр)
  }

T-область-внеземная-физика =
 mkFrag "Исследования учёных из Института внеземной физики общества Макса Планка, Университетской обсерватории Мюниха и Техасского университета в Остине"
I-область-внеземная-физика : ANode
I-область-внеземная-физика = Lni record
  { sttext = just T-область-внеземная-физика
  ; stprop = mkProp "учёные... --- эксперты во внеземной физике"
  }

T-учёные-из-Института-внеземной-физики  =
 mkFrag "Исследования учёных из Института внеземной физики общества Макса Планка, Университетской обсерватории Мюниха и Техасского университета в Остине"
I-учёные-из-Института-внеземной-физики : ANode
I-учёные-из-Института-внеземной-физики = Lni record
  { sttext = just T-учёные-из-Института-внеземной-физики
  ; stprop = mkProp "учёные... --- эксперты"
  }

T-такой-прямой-связи-не-существует =
  mkFrag "такой прямой связи не существует"
I-такой-прямой-связи-не-существует : ANode
I-такой-прямой-связи-не-существует = Lni record
  { sttext = just T-такой-прямой-связи-не-существует
  ; stprop = mkProp "не существует прямой связи между..."
  }

T-рост-чёрной-дыры-определяется-процессом-формирования-галактического-ядра =
  mkFrag "рост чёрной дыры определяется процессом формирования галактического ядра"
I-рост-чёрной-дыры-определяется-процессом-формирования-галактического-ядра : ANode
I-рост-чёрной-дыры-определяется-процессом-формирования-галактического-ядра = Lni record
  { sttext = just T-рост-чёрной-дыры-определяется-процессом-формирования-галактического-ядра
  ; stprop = mkProp (Fragment.ftext T-рост-чёрной-дыры-определяется-процессом-формирования-галактического-ядра)
  }

T-учёные-из-Института-внеземной-физики-показали =
  mkFrag "Исследования учёных из Института внеземной физики общества Макса Планка, Университетской обсерватории Мюниха и Техасского университета в Остине, однако, показали, что такой прямой связи не существует, а рост чёрной дыры определяется процессом формирования галактического ядра."
I-исследования-учёных-показали-что-связи-не-существует : ANode
I-исследования-учёных-показали-что-связи-не-существует = Lni record
  { sttext = just T-учёные-из-Института-внеземной-физики-показали
  ; stprop = mkProp "Исследования показали, что связи нет"
  }
I-исследования-учёных-показали-что-рост-определяется : ANode
I-исследования-учёных-показали-что-рост-определяется = Lni record
  { sttext = just T-учёные-из-Института-внеземной-физики-показали
  ; stprop = mkProp "Исследования показали, что рост ЧД определяется процессом формирования галактического ядра"
  }


SR-от-корреляции-к-причине : ANode
SR-от-корреляции-к-причине = Lnr A-от-корреляции-к-причине
SR-ad-populum : ANode
SR-ad-populum = Lnr A-ad-populum
SR-от-эксперта : ANode
SR-от-эксперта = Lnr A-от-эксперта

SC : ANode
SC = Lnc record {Conflicting = conflicting; Conflicted = conflicted}

S1 = I-хорошо-известно
S2 = I-в-центре-практически-каждой-крупной-галактики-находится-массивная-чёрная-дыра
S3 = I-самые-тяжёлые-галактики-окружены-самыми-массивными-гало-из-тёмной-материи
S4 = I-тёмная-материя-играет-ключевую-роль-в-росте-чёрных-дыр
S5 = I-учёные-из-Института-внеземной-физики
S6 = I-исследования-учёных-показали-что-связи-не-существует
S7 = I-исследования-учёных-показали-что-рост-определяется
S8 = I-такой-прямой-связи-не-существует
S9 = I-рост-чёрной-дыры-определяется-процессом-формирования-галактического-ядра
A1 = SR-ad-populum
A2 = SR-от-корреляции-к-причине
A3 = SR-от-эксперта
A4 = SR-от-эксперта
C1 = SC
C2 = SC
C3 = SC

G : AGraph _
G =
     node C1
       1.0 {refl} {refl}     -- general public
       -- 1.0 {refl} {refl}     -- scientific audience
       ((conflicting , # 5) ∷ (conflicted , # 3) ∷ []) &
     node C2
       0.5 {refl} {refl}     -- general public
       -- 1.0 {refl} {refl}     -- scientific audience
       ((conflicting , # 1) ∷ (conflicted , # 7) ∷ []) &
     node C3
       0.5 {refl} {refl}     -- general public
       -- 1.0 {refl} {refl}     -- scientific audience
       ((conflicting , # 6) ∷ (conflicted , # 0) ∷ []) &
     node0 S4
       ((причинная-связь , # 0) ∷ []) &
     node A2
       0.8 {refl} {refl}     -- general public
       -- 0.8 {refl} {refl}     -- scientific audience
       ((событие1 , # 9) ∷ (событие2 , # 0) ∷ []) &
     node S3
       0.9 {refl} {refl}     -- general public
       -- 0.9 {refl} {refl}     -- scientific audience
       [] &
     node0 S8
       ((вывод , # 0) ∷ []) &
     node A3
       1.0 {refl} {refl}     -- general public
       -- 0.8 {refl} {refl}     -- scientific audience
       ((эксперт , # 5) ∷ (говорит , # 0) ∷ (область , # 4) ∷ []) &
     node S6
       0.7 {refl} {refl}     -- general public
       -- 1.0 {refl} {refl}     -- scientific audience
       [] &
     node0 S9
       ((вывод , # 0) ∷ []) &
     node A4
       1.0 {refl} {refl}     -- general public
       -- 0.8 {refl} {refl}     -- scientific audience
       ((эксперт , # 2) ∷ (говорит , # 0) ∷ (область , # 1) ∷ []) &
     node S7
       1.0 {refl} {refl}     -- general public
       -- 0.9 {refl} {refl}     -- scientific audience
       [] &
     node I-область-внеземная-физика
       1.0 {refl} {refl}     -- general public
       -- 1.0 {refl} {refl}     -- scientific audience
       [] &
     node S5
       1.0 {refl} {refl}     -- general public
       -- 0.8 {refl} {refl}     -- scientific audience
       [] &
     node0 S2
       ((вывод , # 0) ∷ []) &
     node A1
       1.0 {refl} {refl}     -- general public
       -- 0.5 {refl} {refl}     -- scientific audience
       ((все-признают , # 0) ∷ []) &
     node S1
       1.0 {refl} {refl}     -- general public
       -- 0.9 {refl} {refl}     -- scientific audience
       [] &
     ∅

-- _ : NArgs G (# 3) ≡ (record { Scheme = A-от-корреляции-к-причине
--                            ; NPremises = just (Ln S2 _) ∷v just (Ln S3 _) ∷v []v
--                            ; NConclusion = just (Ln S4 _)
--                            } , _) ∷ []
-- _ = refl

-- _ : Arg G (# 3) (# 0) ≡ just (record
--         { Scheme = A-от-корреляции-к-причине
--         ; NPremises = just (Ln S2 (just (V _))) ∷v just (Ln S3 (just (V 0.9))) ∷v []v
--         ; NConclusion = just (Ln S4 nothing)
--         } , just (V 0.8))
-- _ = refl



G0 = steps 0 G

_ : G ≡ G0
_ = refl

G1 = steps 1 G
G2 = steps 2 G
G3 = steps 3 G
G4 = steps 4 G
G5 = steps 5 G
G10 = steps 10 G
G100 = steps 100 G
G200 = steps 200 G

-- _ : G100 ≡ G200
-- _ = refl





------------------------------------------------------------------------

open import ShowDAG la

open import IO

w = 110
ws = 80 -- "section" title width

printG : AGraph 17 → (AGraph 17 → Fin 17 → MC) → String
printG g f = "\n  S1 = " +++ pprint w (f g (# 16))
          +++ " S2 = "  +++ pprint w (f g (# 14))
          +++ " S3 = "  +++ pprint w (f g (# 5))
          +++ " S4 = "  +++ pprint w (f g (# 3))
          +++ " S5 = "  +++ pprint w (f g (# 13))
          +++ "\n  S6 = "  +++ pprint w (f g (# 8))
          +++ " S7 = "  +++ pprint w (f g (# 11))
          +++ " S8 = "  +++ pprint w (f g (# 6))
          +++ " S9 = "  +++ pprint w (f g (# 9))
          +++ "\n  A1 = "  +++ pprint w (f g (# 15))
          +++ " A2 = "  +++ pprint w (f g (# 4))
          +++ " A3 = "  +++ pprint w (f g (# 7))
          +++ " A4 = "  +++ pprint w (f g (# 10))
          +++ " C1 = "  +++ pprint w (f g (# 0))
          +++ " C2 = "  +++ pprint w (f g (# 1))
          +++ " C3 = "  +++ pprint w (f g (# 2))

printContr : AGraph 17 → String
printContr g = pprint w ((val←i g (# 3) ⟪⨂⟫ val←i g (# 9)) ⟪⨁⟫⁺ (val←i g (# 4) ⟪⨂⟫ val←i g (# 6)))

printCSV : String → AGraph 17 → (AGraph 17 → Fin 17 → MC) → String
printCSV s g f = "\n" +++ s
          +++ "; " +++ pprint w (f g (# 16))                    -- S1
          +++ "; "  +++ pprint w (f g (# 14))                   -- S2
          +++ "; "  +++ pprint w (f g (# 5))                    -- S3
          +++ "; "  +++ pprint w (f g (# 3))                    -- S4
          +++ "; "  +++ pprint w (f g (# 13))                   -- S5
          +++ "; "  +++ pprint w (f g (# 8))                    -- S6
          +++ "; "  +++ pprint w (f g (# 11))                   -- S7
          +++ "; "  +++ pprint w (f g (# 6))                    -- S8
          +++ "; "  +++ pprint w (f g (# 9))                    -- S9
          +++ "; "  +++ pprint w (f g (# 15))                   -- A1
          +++ "; "  +++ pprint w (f g (# 4))                    -- A2
          +++ "; "  +++ pprint w (f g (# 7))                    -- A3
          +++ "; "  +++ pprint w (f g (# 10))                   -- A4
          +++ "; "  +++ pprint w (f g (# 0))                    -- C1
          +++ "; "  +++ pprint w (f g (# 1))                    -- C2
          +++ "; "  +++ pprint w (f g (# 2))                    -- C3
          +++ "; "  +++ printContr g                            -- Contr
          +++ "; "  +++ pprint w (Correctness G g)              -- Corr

printCSVh = "Step"
          +++ "; S1"
          +++ "; S2"
          +++ "; S3"
          +++ "; S4"
          +++ "; S5"
          +++ "; S6"
          +++ "; S7"
          +++ "; S8"
          +++ "; S9"
          +++ "; A1"
          +++ "; A2"
          +++ "; A3"
          +++ "; A4"
          +++ "; C1"
          +++ "; C2"
          +++ "; C3"
          +++ "; Contr"
          +++ "; Corr"

main = run (putStrLn stringToPrint)
  where
  wh = 12
  stringToPrint = ""  --S.replicate ws '-'
    -- +++ ppretty ws (docSection ws "original")
    -- +++ printG G val←i
    -- +++ ppretty ws (docSection ws "computed w/o conflicts")
    -- +++ printG G (valTree3←i G G)
    -- +++ ppretty ws (docSection ws "step 0")
    -- +++ printG G0 val←i
    -- +++ ppretty ws (docSection ws "step 1")
    -- +++ printG G1 val←i
    -- -- +++ ppretty ws (docSection ws "step 1 - confl")
    -- -- +++ printG G1 foldConflicts
    -- -- +++ ppretty ws (docSection ws "step 1 - val+confl")
    -- -- +++ printG G1 (val+conflicts G)
    -- +++ ppretty ws (docSection ws "step 2")
    -- +++ printG G2 val←i
    -- +++ ppretty ws (docSection ws "step 3")
    -- +++ printG G3 val←i
    -- +++ ppretty ws (docSection ws "step 4")
    -- +++ printG G4 val←i
    -- -- +++ ppretty ws (docSection ws "step 5")
    -- -- +++ printG G5 val←i
    -- +++ ppretty ws (docSection ws "step 10")
    -- +++ printG G10 val←i
    -- +++ ppretty ws (docSection ws "step 100")
    -- +++ printG G100 val←i
    -- +++ ppretty ws (docSection ws "step 200")
    -- +++ printG G200 val←i

    +++ printCSVh
    +++ printCSV "0" G0 val←i
    +++ printCSV "1" G1 val←i
    +++ printCSV "2" G2 val←i
    +++ printCSV "3" G3 val←i
    +++ printCSV "4" G4 val←i
    +++ printCSV "10" G10 val←i
    +++ printCSV "100" G100 val←i
    +++ printCSV "200" G200 val←i

    -- +++ "\n\nContradiction degree:  step0 = "
    -- +++ pprint w ((val←i G0 (# 3) ⟪⨂⟫ val←i G0 (# 9)) ⟪⨁⟫⁺ (val←i G0 (# 4) ⟪⨂⟫ val←i G0 (# 6)))
    -- +++ " step1 = "
    -- +++ pprint w ((val←i G1 (# 3) ⟪⨂⟫ val←i G1 (# 9)) ⟪⨁⟫⁺ (val←i G1 (# 4) ⟪⨂⟫ val←i G1 (# 6)))
    -- +++ " step10 = "
    -- +++ pprint w ((val←i G10 (# 3) ⟪⨂⟫ val←i G10 (# 9)) ⟪⨁⟫⁺ (val←i G10 (# 4) ⟪⨂⟫ val←i G10 (# 6)))
    -- +++ " step200 = "
    -- +++ pprint w ((val←i G200 (# 3) ⟪⨂⟫ val←i G200 (# 9)) ⟪⨁⟫⁺ (val←i G200 (# 4) ⟪⨂⟫ val←i G200 (# 6)))

    -- +++ "\nCorrectness:"
    -- +++ " step0   = " +++ pprint w (Correctness G G0)
    -- +++ " step1   = " +++ pprint w (Correctness G G1)
    -- +++ " step2   = " +++ pprint w (Correctness G G2)
    -- +++ " step3   = " +++ pprint w (Correctness G G3)
    -- +++ "\n            "
    -- +++ " step10  = " +++ pprint w (Correctness G G10)
    -- +++ " step100 = " +++ pprint w (Correctness G G100)
    -- +++ " step200 = " +++ pprint w (Correctness G G200)

    -- +++ (pprint 110 G)
