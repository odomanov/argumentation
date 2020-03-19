module BarinovaDAG where

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
open import DAG la

-- Statements

S-гладстон-литератор = record
  { sttext = just "британский литератор Уильям Гладстон"
  ; stprop = mkProp "Гладстон --- литератор"
  }
S-в-илиаде-нет-синего =
    let t = "В Илиаде нет ни одного упоминания о синем цвете."
    in record { sttext = just t; stprop = mkProp t }
P-человечество-в-прошлом-не-видело-синего =
  mkProp "Человечество в прошлом не видело синего"
S-человечество-не-видело-синего = record
  { sttext = just "Еще несколько столетий назад человечество не видело синего цвета."
  ; stprop = P-человечество-в-прошлом-не-видело-синего
  }
P-человечество-в-прошлом-не-различало-цвета =
  mkProp "Человечество в прошлом не различало цвета"
S-человечество-в-прошлом-не-различало-цвета = record
  { sttext = just "способность четко различать цвета развилась у человека относительно недавно."
  ; stprop = P-человечество-в-прошлом-не-различало-цвета
  }
S-красочные-описания-в-илиаде =
    let t = "по страницам 'Илиады' разбросаны красочные и детальные описания оружия,"
            +++ " лиц, животных, деталей одежды и так далее"
    in record { sttext = just t; stprop = mkProp t }
P-гомер-был-слепым = mkProp "Гомер был слепым"
S-гомер-не-был-слепым = record
  { sttext = just "Версия о том, что Гомер был слепым, давно отвергнута учеными"
  ; stprop = NOT P-гомер-был-слепым
  }



-- Arguments

G : AGraph _
G =
    context (Ln (Lni S-гомер-не-был-слепым)
              (just (PV 0.2 {refl} {refl})))
           []
  & context (Ln (Lni S-в-илиаде-нет-синего)
              (just (PV 0.2 {refl} {refl})))
           ((поддержка , # 0) ∷ []) 
  & context (Ln (Lnr A-от-эксперта)
              (just (PV 0.2 {refl} {refl})))
          ((эксперт , # 0) ∷ (говорит , # 1) ∷ (область , # 2) ∷ []) 
  & context (Ln (Lni S-гладстон-литератор)
              (just (PV 0.2 {refl} {refl})))
          [] 
  & context (Ln (Lni record
                    { sttext = just ("В 1858 году британский литератор Уильям Гладстон"
                      +++ " заметил, что в 'Илиаде' Гомера нет ни одного упоминания о синем цвете.")
                    ; stprop = mkProp ("Гладстон говорит, что"
                      +++ " в 'Илиаде' Гомера нет ни одного упоминания о синем цвете.")
                    })
              (just (PV 0.2 {refl} {refl})))
          [] 
  & context (Ln (Lni record
                     { sttext = nothing
                     ; stprop = mkProp "Илиада относится к литературе."
                     })
              (just (PV 0.2 {refl} {refl})))
           [] 
  & ∅
  -- where
  -- a1 =
  --   let instance
  --        aa : A-от-эксперта
  --        aa = record
  --          { эксперт = S-гладстон-литератор
  --          ; говорит = record
  --            { sttext = just ("В 1858 году британский литератор Уильям Гладстон"
  --              +++ " заметил, что в 'Илиаде' Гомера нет ни одного упоминания о синем цвете.")
  --            ; stprop = mkProp ("Гладстон говорит, что"
  --              +++ " в 'Илиаде' Гомера нет ни одного упоминания о синем цвете.")
  --            }
  --          ; область = record
  --            { sttext   = nothing
  --            ; stprop = mkProp "Илиада относится к литературе."
  --            }
  --          ; вывод = S-в-илиаде-нет-синего
  --          ; Q1 = nothing
  --          }
  --   in `от-эксперта aa

  -- a2 =
  --   let instance
  --        aa : A-от-примера
  --        aa = record
  --          { пример = S-в-илиаде-нет-синего
  --          ; вывод = S-человечество-не-видело-синего
  --          }
  --   in `от-примера aa

  -- a2' =
  --   let instance
  --        aa : A-от-примера
  --        aa = record
  --          { пример = S-человечество-не-видело-синего
  --          ; вывод = S-человечество-в-прошлом-не-различало-цвета
  --          }
  --   in `от-примера aa

  -- a3 =
  --   let instance
  --        aa : A-от-знака
  --        aa = record
  --          { знак            = S-красочные-описания-в-илиаде
  --          ; связь-со-знаком = record
  --            { sttext   = nothing
  --            ; stprop = mkProp "Красочные описания указывают на зрячесть"
  --            }
  --          ; цель            = S-гомер-не-был-слепым
  --          }
  --   in `от-знака aa

  -- a4 =
  --   let instance
  --        aa : A-абдукция
  --        aa = record
  --          { факт       = S-красочные-описания-в-илиаде
  --          ; объяснение = S-гомер-не-был-слепым
  --          ; вывод      = S-гомер-не-был-слепым
  --          }
  --   in `абдукция aa

  -- a5 =
  --   let instance
  --        aa : A-от-альтернативы
  --        

------------------------------------------------------------------------

open import ShowDAG la

open import IO

main = run (putStr stringToPrint)
  where
    stringToPrint = ""
      +++ pprint G
