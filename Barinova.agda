module Barinova where

open import Data.Product -- using (_×_; proj₁; proj₂) -- renaming (_,_ to ⟨_,_⟩)
open import Data.Unit -- using (⊤; tt)
open import Data.List 
-- open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.String renaming (_++_ to _+++_)
open import Data.Maybe

open import ArgSchemes
open import ArgVariants

-- Statements

S-гладстон-литератор = record
  { text = just "британский литератор Уильям Гладстон"
  ; thesis = Th "Гладстон --- литератор"
  ; weight = 0.5
  }
S-в-илиаде-нет-синего =
    let t = "В Илиаде нет ни одного упоминания о синем цвете."
    in record { text = just t; thesis = Th t; weight = 0.5}
T-человечество-в-прошлом-не-видело-синего = Pos record
  { pos = "Человечество в прошлом не видело синего"
  ; neg = "Человечество в прошлом видело синий"
  }
S-человечество-не-видело-синего = record
  { text = just "Еще несколько столетий назад человечество не видело синего цвета."
  ; thesis = T-человечество-в-прошлом-не-видело-синего
  ; weight = 0.5
  }
T-человечество-в-прошлом-не-различало-цвета = Pos record
  { pos = "Человечество в прошлом не различало цвета"
  ; neg = "Человечество в прошлом различало цвета"
  }
S-человечество-в-прошлом-не-различало-цвета = record
  { text = just "способность четко различать цвета развилась у человека относительно недавно."
  ; thesis = T-человечество-в-прошлом-не-различало-цвета
  ; weight = 0.5
  }
S-красочные-описания-в-илиаде =
    let t = "по страницам 'Илиады' разбросаны красочные и детальные описания оружия,"
            +++ " лиц, животных, деталей одежды и так далее"
    in record { text = just t; thesis = Th t; weight = 0.5 }
T-гомер-был-слепым = Pos record
  { pos = "Гомер был слепым"
  ; neg = "Гомер не был слепым"
  }
S-гомер-не-был-слепым = record
  { text = just "Версия о том, что Гомер был слепым, давно отвергнута учеными"
  ; thesis = Neg T-гомер-был-слепым
  ; weight = 0.5
  }



-- Arguments

AList = a8 ∷ a7 ∷ a6 ∷ a5 ∷ a4 ∷ a3 ∷ a2' ∷ a2 ∷ a1 ∷ []  where
  a1 = 
    let instance
         aa : A-от-эксперта
         aa = record
           { эксперт = S-гладстон-литератор
           ; говорит = record
             { text = just ("В 1858 году британский литератор Уильям Гладстон"
               +++ " заметил, что в 'Илиаде' Гомера нет ни одного упоминания о синем цвете.")
             ; thesis = Th ("Гладстон говорит, что"
               +++ " в 'Илиаде' Гомера нет ни одного упоминания о синем цвете.")
             ; weight = 0.5
             }
           ; область = record
             { text   = nothing
             ; thesis = Th "Илиада относится к литературе."
             ; weight = 0.5
             }
           ; цель = S-в-илиаде-нет-синего
           ; Q1 = nothing
           }
    in `от-эксперта aa

  a2 = 
    let instance
         aa : A-от-примера
         aa = record
           { пример = S-в-илиаде-нет-синего
           ; цель = S-человечество-не-видело-синего
           }
    in `от-примера aa
  
  a2' = 
    let instance
         aa : A-от-примера
         aa = record
           { пример = S-человечество-не-видело-синего
           ; цель = S-человечество-в-прошлом-не-различало-цвета
           }
    in `от-примера aa
  
  a3 =   
    let instance
         aa : A-от-знака
         aa = record
           { знак            = S-красочные-описания-в-илиаде
           ; связь-со-знаком = record
             { text   = nothing
             ; thesis = Th "Красочные описания указывают на зрячесть"
             ; weight = 0.5
             }
           ; цель            = S-гомер-не-был-слепым
           }
    in `от-знака aa

  a4 =    
    let instance
         aa : A-абдукция
         aa = record
           { факт       = S-красочные-описания-в-илиаде
           ; объяснение = S-гомер-не-был-слепым
           ; цель      = S-гомер-не-был-слепым
           }
    in `абдукция aa

  a5 =
    let instance
         aa : A-от-альтернативы
         aa = record
           { альтернатива = record
             { text = nothing
             ; thesis = Th "Гомер мог быть либо слеп, либо не слеп"
             ; weight = 0.5
             }
           ; неверно = S-красочные-описания-в-илиаде
           ; цель = S-гомер-не-был-слепым
           }
    in `от-альтернативы aa

  a6 =
    let instance
         aa : A-от-эксперта
         aa = record
           { эксперт = S-гладстон-литератор
           ; говорит = record
             { text = just ("Исследователь, подняв другие древнегреческие тексты, обнаружил, "
               +++ "что ни в одном из них нет слова 'синий'.")
             ; thesis = Th "Гладстон обнаружил, что в др.-греч. текстах нет слова 'синий'."
             ; weight = 0.5
             }
           ; область = record
             { text = nothing
             ; thesis = Th "Древнегреческие тексты относятся к литературе"
             ; weight = 0.5
             }
           ; цель = record
             { text = just "В древнегреческих текстах нет слова 'синий'."
             ; thesis = Th "В древнегреческих текстах нет слова 'синий'."
             ; weight = 0.5
             }
           ; Q1 = nothing
           }
    in `от-эксперта aa

  a7 =
    let instance
         aa : A-от-примера
         aa = record
           { пример =
               let t = "в древнегреческих текстах нет слова 'синий'."
               in record { text = just t; thesis = Th t; weight = 0.5 }
           ; цель = S-человечество-в-прошлом-не-различало-цвета
           }             
    in `от-примера aa

  a8 =
    let instance
         aa : A-от-причины-к-следствию
         aa = record
           { причинная-связь = record
             { text = nothing
             ; thesis = Th "Если цвет не встречают часто, то его не различают"
             ; weight = 0.5
             }
           ; причина = record
             { text = just "В природе же, действительно, синий цвет распространен мало"
             ; thesis = Th "В природе синий цвет распространен мало"
             ; weight = 0.5
             }
           ; цель = S-человечество-не-видело-синего 
           }
    in `от-причины-к-следствию aa
  



open import IO

main = run (putStrLn stringToPrint)
  where
    =line = "\n= = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = "
    pre-line = "  "
    ListString : List Argument → String
    ListString [] = ""
    ListString (a ∷ l) = ListString l +++ "\n\n===== " +++ AName a
      +++ " =============================================="
      +++ AString pre-line a 

    stringToPrint = ""
      +++ =line +++ ListString VList
      -- +++ =line +++ ListString AList
