#lang racket
(require redex)

;;Language;;
(define-language AE
                           ;terms
  (t ::= true              ;constant true
     false                 ;constant false
     (if t then t else t)  ;conditional
     0                     ;constant zero
     (succ t)              ;successor
     (pred t)              ;predecessor
     (iszero t)            ;zero test
     )
                           ;values
  (v ::= true              ;true value
     false                 ;false value
     nv                    ;numeric values
     )

                           ;numeric values
  (nv ::= 0                ;zero value
      (succ nv)            ;successor value
      )

  
  ;Context Evaluation
  (E ::= hole
     (if E then t else t)  ;E-IF
     (succ E)              ;E-SUCC
     (pred E)              ;E-PRED
     (iszero E)            ;E-ISZERO
     )

                           ;types
  (T ::= Bool              ;type of booleans
     Nat                   ;type of natural numbers
     )
  )

;;Reduction Relations;;
(define s->ßs
  (reduction-relation AE
  #:domain (t)
   ;Arithmetic Expressions
   (--> [(in-hole E (if true then t_1 else t_2))]
        [(in-hole E t_1)]
        "E-IFTRUE")
   (--> [(in-hole E (if false then t_1 else t_2))]
        [(in-hole E t_2)]
        "E-IFFALSE")
   (--> [(in-hole E (pred 0))]
        [(in-hole E 0)]
        "E-PREDZERO")
   (--> [(in-hole E (pred (succ nv)))]
        [(in-hole E nv)]
        "E-PREDSUCC")
   (--> [(in-hole E (iszero 0))]
        [(in-hole E true)]
        "E-ISZEROZERO")
   (--> [(in-hole E (iszero (succ nv)))]
        [(in-hole E false)]
        "E-ISZEROSUCC")
   ))


;(traces s->ßs (term ( (if true then (pred (succ 0)) else false) )))

(define-judgment-form
  AE
  #:mode(⊢ I O)
  #:contract(⊢ t T)
  [-------------
   (⊢ true Bool)]                      ;T-TRUE
  [-------------
   (⊢ false Bool)]                     ;T-FALSE
  [-------------
   (⊢ false Bool)]
  [(⊢ t_1 Bool) (⊢ t_2 T)  (⊢ t_3 T)
   --------------------------------
   (⊢ (if t_1 then t_2 else t_3) T)]   ;T-IF
  [---------
   (⊢ 0 Nat)]                          ;T-ZERO
  [(⊢ t_1 Nat)
   ------------------
   (⊢ (succ t_1) Nat)]                 ;T-SUCC
  [(⊢ t_1 Nat)
   ------------------
   (⊢ (pred t_1) Nat)]                 ;T-PRED
  [(⊢ t_1 Nat)
   ------------------
   (⊢ (iszero t_1) Bool)]              ;T-ISZERP
  )

;(judgment-holds (⊢ true Bool))
;(judgment-holds (⊢ (if true then true else false) Bool))
;(judgment-holds (⊢ (if (iszero (succ 0)) then (pred 0) else (succ 0)) _))
;(judgment-holds (⊢ (if (iszero (succ 0)) then (pred 0) else false) _))