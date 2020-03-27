module BarinovaDAG where

open import Data.Bool
open import Data.Fin
open import Data.List
open import Data.Maybe
open import Data.Product
open import Data.String renaming (_++_ to _+++_)

open import ArgPrelude 
open import ArgSchemes
-- open import ArgVariants
open import LabelAlgebras
open import AIF

la = Pref
import DAG; module DAGla = DAG la; open DAGla

node : ∀ {n} → ANode
             → (v : Float) → {0.0 [≤] v ≡ true} → {v [≤] 1.0 ≡ true}
             → Sucs n
             → AContext n
node nd v {p0} {p1} sucs = context (Ln nd (just (V v {p0} {p1}))) sucs

T-британский-литератор-Уильям-Гладстон =
  mkFrag "британский литератор Уильям Гладстон"
T-В-Илиаде-нет-ни-одного-упоминания-о-синем-цвете =
  mkFrag "В Илиаде нет ни одного упоминания о синем цвете."
T-Еще-несколько-столетий-назад-человечество-не-видело-синего-цвета =
  mkFrag "Еще несколько столетий назад человечество не видело синего цвета."
T-способность-четко-различать-цвета-развилась-у-человека-относительно-недавно =
  mkFrag "способность четко различать цвета развилась у человека относительно недавно."
T-по-страницам-Илиады-разбросаны-красочные-и-детальные-описания-оружия =
  mkFrag ("по страницам 'Илиады' разбросаны красочные и детальные описания оружия,"
          +++ " лиц, животных, деталей одежды и так далее")
T-Версия-о-том-что-Гомер-был-слепым-давно-отвергнута-учеными =
  mkFrag "Версия о том, что Гомер был слепым, давно отвергнута учеными"
T-исследователь-подняв-другие-древнегреческие-тексты =
  mkFrag ("Исследователь, подняв другие древнегреческие тексты, обнаружил, "
          +++ "что ни в одном из них нет слова 'синий'.")
T-в-древнегреческих-текстах-нет-слова-синий =
  mkFrag "В древнегреческих текстах нет слова 'синий'."
T-в-природе-же-действительно-синий-цвет-распространен-мало =
  mkFrag "В природе же, действительно, синий цвет распространен мало"

-- Statements

NS-гладстон-литератор : ANode
NS-гладстон-литератор = Lni record
  { sttext = just T-британский-литератор-Уильям-Гладстон
  ; stprop = mkProp "Гладстон --- литератор"
  }
NS-в-илиаде-нет-синего : ANode
NS-в-илиаде-нет-синего = Lni record
  { sttext = just T-В-Илиаде-нет-ни-одного-упоминания-о-синем-цвете
  ; stprop = mkProp (Fragment.ftext T-В-Илиаде-нет-ни-одного-упоминания-о-синем-цвете)
  }
P-в-илиаде-есть-упоминания-синего = NOT (Prop←N NS-в-илиаде-нет-синего)    
P-человечество-в-прошлом-не-видело-синего =
  mkProp "Человечество в прошлом не видело синего"
NS-человечество-не-видело-синего : ANode
NS-человечество-не-видело-синего = Lni record
  { sttext = just T-Еще-несколько-столетий-назад-человечество-не-видело-синего-цвета
  ; stprop = P-человечество-в-прошлом-не-видело-синего
  }
P-человечество-в-прошлом-не-различало-цвета =
  mkProp "Человечество в прошлом не различало цвета"
NS-человечество-в-прошлом-не-различало-цвета : ANode
NS-человечество-в-прошлом-не-различало-цвета = Lni record
  { sttext = just T-способность-четко-различать-цвета-развилась-у-человека-относительно-недавно
  ; stprop = P-человечество-в-прошлом-не-различало-цвета
  }
NS-красочные-описания-в-илиаде : ANode
NS-красочные-описания-в-илиаде = Lni record
  { sttext = just T-по-страницам-Илиады-разбросаны-красочные-и-детальные-описания-оружия
  ; stprop = mkProp (Fragment.ftext T-по-страницам-Илиады-разбросаны-красочные-и-детальные-описания-оружия)
  }
NS-красочные-описания-указывают-на-зрячесть : ANode
NS-красочные-описания-указывают-на-зрячесть = Lni record
 { sttext = nothing
 ; stprop = mkProp "Красочные описания указывают на зрячесть"
 }
P-гомер-был-слепым = mkProp "Гомер был слепым"
NS-гомер-не-был-слепым : ANode
NS-гомер-не-был-слепым = Lni record
  { sttext = just T-Версия-о-том-что-Гомер-был-слепым-давно-отвергнута-учеными
  ; stprop = NOT P-гомер-был-слепым
  }
NS-гомер-мог-быть-либо-слеп-либо-не-слеп : ANode
NS-гомер-мог-быть-либо-слеп-либо-не-слеп = Lni record
  { sttext = nothing
  ; stprop = mkProp "Гомер мог быть либо слеп, либо не слеп"
  }
NS-исследователь-подняв-другие-древнегреческие-тексты : ANode
NS-исследователь-подняв-другие-древнегреческие-тексты = Lni record
  { sttext = just T-исследователь-подняв-другие-древнегреческие-тексты
  ; stprop = mkProp "Гладстон обнаружил, что в др.-греч. текстах нет слова 'синий'."
  }
NS-древнегреческие-тексты-относятся-к-литературе : ANode
NS-древнегреческие-тексты-относятся-к-литературе = Lni record
  { sttext = nothing
  ; stprop = mkProp "Древнегреческие тексты относятся к литературе"
  }
NS-в-древнегреческих-текстах-нет-слова-синий : ANode
NS-в-древнегреческих-текстах-нет-слова-синий = Lni record
  { sttext = just T-в-древнегреческих-текстах-нет-слова-синий
  ; stprop = mkProp (Fragment.ftext T-в-древнегреческих-текстах-нет-слова-синий)
  }
NS-если-цвет-не-встречают-часто-то-его-не-различают : ANode
NS-если-цвет-не-встречают-часто-то-его-не-различают = Lni record
  { sttext = nothing
  ; stprop = mkProp "Если цвет не встречают часто, то его не различают"
  }
NS-в-природе-синий-цвет-распространен-мало : ANode
NS-в-природе-синий-цвет-распространен-мало = Lni record
  { sttext = just T-в-природе-же-действительно-синий-цвет-распространен-мало
  ; stprop = mkProp "В природе синий цвет распространен мало"
  }

NA-от-эксперта : ANode
NA-от-эксперта = Lnr A-от-эксперта

NA-от-примера : ANode
NA-от-примера = Lnr A-от-примера

NA-от-знака : ANode
NA-от-знака = Lnr A-от-знака

NA-абдукция : ANode
NA-абдукция = Lnr A-абдукция

NA-от-альтернативы : ANode
NA-от-альтернативы = Lnr A-от-альтернативы

NA-от-причины-к-следствию : ANode
NA-от-причины-к-следствию = Lnr A-от-причины-к-следствию

-- Arguments

G : AGraph _
G =
    node NS-человечество-не-видело-синего
         0.2 {refl} {refl}
         ((вывод , # 17) ∷ (следствие , # 0) ∷ []) &
    node NA-от-причины-к-следствию
         0.2 {refl} {refl}
         ((причинная-связь , # 1) ∷ (причина , # 0) ∷ []) &
    node NS-в-природе-синий-цвет-распространен-мало
         0.2 {refl} {refl}
         [] &
    node NS-если-цвет-не-встречают-часто-то-его-не-различают
         0.2 {refl} {refl}
         [] &
    node NS-человечество-в-прошлом-не-различало-цвета
         0.2 {refl} {refl}
         ((вывод , # 0) ∷ (вывод , # 12) ∷ []) &
    node NA-от-примера
         0.2 {refl} {refl}
         ((вывод , # 0) ∷ []) &
    node NS-в-древнегреческих-текстах-нет-слова-синий
         0.2 {refl} {refl}
         ((вывод , # 0) ∷ []) &
    node NA-от-эксперта
         0.2 {refl} {refl}
         ((эксперт , # 15) ∷ (говорит , # 1) ∷ (область , # 0) ∷ []) &
    node NS-древнегреческие-тексты-относятся-к-литературе
         0.2 {refl} {refl}
         [] &
    node NS-исследователь-подняв-другие-древнегреческие-тексты
         0.2 {refl} {refl}
         [] &
    node NS-гомер-не-был-слепым
         0.2 {refl} {refl}
         ((цель , # 3) ∷ (объяснение , # 2) ∷ (верно , # 0) ∷ []) &
    node NA-от-альтернативы
         0.2 {refl} {refl}
         ((альтернатива , # 0) ∷ (неверно , # 4) ∷ []) &
    node NS-гомер-мог-быть-либо-слеп-либо-не-слеп
         0.2 {refl} {refl}
         [] &
    node NA-абдукция
         0.2 {refl} {refl}
         ((факт , # 2) ∷ []) &
    node NA-от-знака
         0.2 {refl} {refl}
         ((знак , # 1) ∷ (связь-со-знаком , # 0) ∷ []) &
    node NS-красочные-описания-указывают-на-зрячесть
         0.2 {refl} {refl}
         [] &
    node NS-красочные-описания-в-илиаде
         0.2 {refl} {refl}
         [] &
    node NA-от-примера
         0.2 {refl} {refl}
         ((пример , # 0) ∷ []) &
    node NA-от-примера
         0.2 {refl} {refl}
         ((пример , # 1) ∷ []) &
    node NS-в-илиаде-нет-синего
         0.2 {refl} {refl}
         ((поддержка , # 0) ∷ []) & 
    node NA-от-эксперта
         0.2 {refl} {refl}
         ((эксперт , # 0) ∷ (говорит , # 1) ∷ (область , # 2) ∷ []) & 
    node NS-гладстон-литератор
         0.2 {refl} {refl}
         [] &
    node (Lni record
         { sttext = just (mkFrag ("В 1858 году британский литератор Уильям Гладстон"
           +++ " заметил, что в 'Илиаде' Гомера нет ни одного упоминания о синем цвете."))
         ; stprop = mkProp ("Гладстон говорит, что"
           +++ " в 'Илиаде' Гомера нет ни одного упоминания о синем цвете.")
         })
         0.2 {refl} {refl}
         [] & 
    node (Lni record
         { sttext = nothing
         ; stprop = mkProp "Илиада относится к литературе."
         })
         0.2 {refl} {refl}
         [] & 
    ∅

------------------------------------------------------------------------

open import ShowDAG la

open import IO

main = run (putStr stringToPrint)
  where
    stringToPrint = ""
      +++ pprint 60 G
