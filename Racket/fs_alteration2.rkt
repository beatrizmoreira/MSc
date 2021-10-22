#lang racket
(require redex)

;;;;;Language;;;;;
(define-language FS
  ;Main language specification

  ;Contract Declaration
  (SC ::= (contract C {(T x)... K F ...}))

  ;Constructor Declaration
  (K ::= (C ((T x) ... ) { (this -> s = x)... }))

  ;Funtion Declaration
  (F ::= (T f ((T x) ... ) {return e})
     (unit fb () {return e}))

  ;Expressions
  (e ::= vv
     b x this ea
     (this -> f)
     (msg -> sender)
     ;(msg -> value)
     (address (e))
     ;(e -> s)
     (e -> transfer (e))
     (new C -> value (e) ((x : e) ...) (c a))
     (C (e))
     (e e)
     (T x = e)
     (x = e)
     (e -> s = e)
     ;(e [e])
     (e [e -> e])
     (e -> f -> value (e) ((x : e) ...))
     (e -> value (e) ((x : e) ...))
     (e -> f -> value (e) -> sender (e) ((x : e) ...))
     (if e then e else e)
     (return e)
     ;(ea a-op ea)
     revert
     )

  (ea ::= n x 
      (msg -> value)
      (e -> s)
      (e [e])
      (ea a-op ea))

  ;Values
  (v ::= booll n a u M c)
  (vv ::= v (c -> f))
  
  ;Types
  (T ::= bool uint address unit (mapping (T => T)) C (T ... -> T))

  (x ::= variable-not-otherwise-mentioned)
  (s ::= variable-not-otherwise-mentioned)
  (C ::= variable-not-otherwise-mentioned)
  (f ::= variable)
  (c ::= (variable-prefix c))
  (a ::= (variable-prefix a))
  (vars ::= (x : v))
  (contracts ::= ((c a) -> (C (s : vv)... n) -> (x -> vv) ...))
  (var ::= (x -> vv))
  (n ::= number)
  (M ::= ((v v) ...))

  (a-op ::= + - *)
  (b-op1 ::= < <= == >= >)
  (b-op2 ::= &&)
  (b-op3 ::= not)
  (b ::= booll x
     ;(b ...)
     (e b-op1 e)
     (e b-op2 e)
     (b-op3 b))
  (booll ::= true false)

  ;;;Environments;;;
  ;Contract Table
  (CT ::= (SC ...))

  ;Blockchain
  (ß ::= var contracts)
  (ß-v ::= (ß ...))
  (env-ß ::= (ß-v ...))

  ;Call Stack
  (σ ::= a)
  (σ-v ::= (σ ...))
  (env-σ ::= (ß-v ... σ-v ...))

  

  ;;;Context Evaluation;;;
  (E ::= hole
     (address (E))
     (E -> s)
     (E -> transfer (e))
     (a -> transfer (E))
     (new C -> value (E) ((x : e) ...) (c a))
     (new C -> value (n) ((x : v) ... (x : E) (x : e) ...) (c a))
     (C (E))
     (E e)
     (E -> f -> value (e) ((x : e) ...))
     (c -> f -> value (E) ((x : e) ...))
     (c -> f -> value (n) ((x : v) ... (x : E) (x : e) ...))
     (E -> value (e) ((x : e) ...))
     (c -> value (E) ((x : e) ...))
     (c -> value (n) ((x : v) ... (x : E) (x : e) ...))
     (E -> f -> value (e) -> sender (e) ((x : e) ...))
     (c -> f -> value (E) -> sender (e) ((x : e) ...))
     (c -> f -> value (n) -> sender (E) ((x : e) ...))
     (c -> f -> value (n) -> sender (a) ((x : v)... (x : E) (x : e) ...))
     (T x = E)
     (x = E)
     (E -> s = e)
     (c -> s = E)
     (E [e])
     (M [E])
     (E [e -> e])
     (M [E -> e])
     (M [v -> E])
     (if E then e else e)
     (return E)

     (E a-op ea)
     (n a-op E)
     (E b-op1 e)
     (v b-op1 E)
     (E b-op2 e)
     (booll b-op2 E)
     (b-op3 E)
     )
  
  )

;;;;;;;;;;;;;;;
(define s->ßs
  (reduction-relation
   FS
   #:domain (e env-ß env-σ CT)
   ;Arithmetic Expressions
   (--> [(in-hole E (n_1 + n_2)) env-ß env-σ CT]
        [(in-hole E ,(+ (term n_1)(term n_2))) env-ß env-σ CT]
        "ADD")
   (--> [(in-hole E (n_1 - n_2)) env-ß env-σ CT]
        [(in-hole E ,(- (term n_1)(term n_2))) env-ß env-σ CT]
        "SUB")
   (--> [(in-hole E (n_1 * n_2)) env-ß env-σ CT]
        [(in-hole E ,(* (term n_1)(term n_2))) env-ß env-σ CT]
        "MULT")
   ;Boolean Expressions
   (--> [(in-hole E (v_1 == v_2)) env-ß env-σ CT]
        [(in-hole E ,(if (equal? (term v_1) (term v_2)) (term true) (term false))) env-ß env-σ CT]
        "EQUALS")
   (--> [(in-hole E (n_1 <= n_2)) env-ß env-σ CT]
        [(in-hole E ,(if (<= (term n_1) (term n_2)) (term true) (term false))) env-ß env-σ CT]
        "LESS-EQ")
   (--> [(in-hole E (n_1 < n_2)) env-ß env-σ CT]
        [(in-hole E ,(if (< (term n_1) (term n_2)) (term true) (term false))) env-ß env-σ CT]
        "LESS")
   (--> [(in-hole E (n_1 >= n_2)) env-ß env-σ CT]
        [(in-hole E ,(if (>= (term n_1) (term n_2)) (term true) (term false))) env-ß env-σ CT]
        "GREATER-EQ")
   (--> [(in-hole E (n_1 > n_2)) env-ß env-σ CT]
        [(in-hole E ,(if (> (term n_1) (term n_2)) (term true) (term false))) env-ß env-σ CT]
        "GREATER")
   (--> [(in-hole E (booll_1 && booll_2)) env-ß env-σ CT]
        [(in-hole E ,(if (equal? (term booll_1) (term booll_2)) (term true) (term false))) env-ß env-σ CT]
        "AND")
   (--> [(in-hole E (not booll)) env-ß env-σ classes]
        [(in-hole E ,(if (equal? (term booll) true) (term false) (term true))) env-ß env-σ CT]
        "NOT")
   ;If Expression
   (--> [(in-hole E (if true then e_1 else e_2)) env-ß env-σ CT]
        [(in-hole E e_1) env-ß env-σ CT]
        "IF-TRUE")
   (--> [(in-hole E (if false then e_1 else e_2)) env-ß env-σ CT]
        [(in-hole E e_2) env-ß env-σ CT]
        "IF-FALSE")
   ;Sequential Composition
   (--> [(in-hole E (v e)) env-ß env-σ CT]
        [(in-hole E e) env-ß (check-σ env-σ env-ß) CT]
        "SEQ")
   #|(--> [(in-hole E (v e)) env-ß (ß-v ...) CT]
        [(in-hole E e) env-ß env-ß CT]
        "SEQ-C")
   (--> [(in-hole E (v e)) env-ß (ß-v ... σ-v ...) CT]
        [(in-hole E e) env-ß (ß-v ... σ-v ...) CT]
        "SEQ")|#
   (--> [(in-hole E (revert e)) env-ß env-σ CT]
        [(in-hole E revert) (rev env-σ) env-σ CT]
        "SEQ-R")
   ;Variables
   ;Declaration
   (--> [(in-hole E (T x = v)) env-ß env-σ CT]
        [(in-hole E v) (decl env-ß (x -> v)) env-σ CT]
        "DECL")
   #|(--> [(in-hole E x) (env-ß_1 ... (ß_1 ... (x -> vv) ß_2 ...) env-ß_2 ...) env-σ CT]
        [(in-hole E vv) (env-ß_1 ... (ß_1 ... (x -> vv) ß_2 ...) env-ß_2 ...) env-σ CT]
        "VAR")|#
   (--> [(in-hole E x) env-ß env-σ CT]
        [(in-hole E (findvar env-ß (top-σ env-σ ) x)) env-ß env-σ CT]
        "VAR")
   (--> [(in-hole E (x = v)) env-ß env-σ CT]
        [(in-hole E v) (assign env-ß x v) env-σ CT]
        "ASS")
   ;Mappings
   (--> [(in-hole E (M [v])) env-ß env-σ CT]
        [(in-hole E (mappsel M v)) env-ß env-σ CT]
        "MAPPSEL")
   (--> [(in-hole E (M [v_1 -> v_2])) env-ß env-σ CT]
        [(in-hole E (mappass M v_1 v_2)) env-ß env-σ CT]
        "MAPPASS")
   ;Balance and Address
   (--> [(in-hole E (address (c))) (env-ß_1 ... (ß_1 ... (x -> c) ß_2 ...) env-ß_2 ...) env-σ CT]
        [(in-hole E (ref (env-ß_1 ... (ß_1 ... (x -> c) ß_2 ...) env-ß_2 ...) c)) (env-ß_1 ... (ß_1 ... (x -> c) ß_2 ...) env-ß_2 ...) env-σ CT]
        "ADDRESS")
   
   ;Contract instantiation
   (--> [(in-hole E (new C -> value (n) ((s : vv) ...) (c a))) env-ß env-σ
                                                              ((contract C_1 {(T_1 x_11) ... K_1 F_1 ...}) ... (contract C {(T_0 x_01) ... (C ((T x) ...) {(this -> s = x) ...}) F ...}) (contract C_2 {(T_2 x_21) ... K_2 F_2 ...}) ...)]
        [(in-hole E c) (decl env-ß ((c a) -> (C (s : vv)... n) ->)) env-σ
                       ((contract C_1 {(T_1 x_11) ... K_1 F_1 ...}) ... (contract C {(T_0 x_01) ... (C ((T x) ...) {(this -> s = x) ...}) F ...}) (contract C_2 {(T_2 x_21) ... K_2 F_2 ...}) ...)]
        "NEW-2")
   ;Cast
   (--> [(in-hole E (C (a))) (env-ß_1 ... (ß_1 ... ((c a) -> (C (s : vv)... n) -> (x -> v) ...) ß_2 ...) env-ß_2 ...) env-σ
                             ((contract C_1 {(T_1 x_11) ... K_1 F_1 ...}) ... (contract C {(T_0 x_01) ... K F ...}) (contract C_2 {(T_2 x_21) ... K_2 F_2 ...}) ...)]
        [(in-hole E c) (env-ß_1 ... (ß_1 ... ((c a) -> (C (s : vv)... n) -> (x -> v) ...) ß_2 ...) env-ß_2 ...) env-σ
                       ((contract C_1 {(T_1 x_11) ... K_1 F_1 ...}) ... (contract C {(T_0 x_01) ... K F ...}) (contract C_2 {(T_2 x_21) ... K_2 F_2 ...}) ...)]
        "CONTRRETR")
   ;State variables
   (--> [(in-hole E (c -> s)) (env-ß_1 ... (ß_1 ... (x -> c) ß_2 ...) env-ß_2 ...) env-σ ((contract C_1 {(T_1 x_11) ... K_1 F_1 ...}) ... (contract C {(T_0 x_01) ... (T_s s) (T_02 x_02) ... K F ...}) (contract C_2 {(T_2 x_21) ... K_2 F_2 ...}) ...)]
        [(in-hole E (state-sel (env-ß_1 ... (ß_1 ... (x -> c) ß_2 ...) env-ß_2 ...) c s)) (env-ß_1 ... (ß_1 ... (x -> c) ß_2 ...) env-ß_2 ...) env-σ ((contract C_1 {(T_1 x_11) ... K_1 F_1 ...}) ... (contract C {(T_0 x_01) ... (T_s s) (T_02 x_02) ... K F ...}) (contract C_2 {(T_2 x_21) ... K_2 F_2 ...}) ...)]
        "STATESEL")
   (--> [(in-hole E (c -> s)) env-ß env-σ CT]
        [(in-hole E (state-sel env-ß c s)) env-ß env-σ CT])
   (--> [(in-hole E (c -> s = v)) (env-ß_1 ... (ß_1 ... (x -> c) ß_2 ...) env-ß_2 ...) env-σ CT]
        [(in-hole E v) (state-ass (env-ß_1 ... (ß_1 ... (x -> c) ß_2 ...) env-ß_2 ...) c s v) env-σ CT]
        "STATEASS")
   ;Function Calls
   (--> [(in-hole E (c -> f -> value (n) ((s : v) ...))) (env-ß_1 ... (ß_1 ... (x -> c) ß_2 ...) env-ß_2 ...) env-σ CT]
        [(in-hole E (return (call (env-ß_1 ... (ß_1 ... (x -> c) ß_2 ...) env-ß_2 ...) CT c ;(ref (env-ß_1 ... (ß_1 ... (x -> c) ß_2 ...) env-ß_2 ...) c)
                                  (top-σ env-σ) f n ((s : v) ...)))) (declcall (uptbal (uptbal (env-ß_1 ... (ß_1 ... (x -> c) ß_2 ...) env-ß_2 ...) (ref (env-ß_1 ... (ß_1 ... (x -> c) ß_2 ...) env-ß_2 ...) c) n) (top-σ env-σ) ,(- (term 0)(term n))) c ((s -> v) ...)) (call-σ env-σ (ref (env-ß_1 ... (ß_1 ... (x -> c) ß_2 ...) env-ß_2 ...) c)) CT]
        "CALL")
   (--> [(in-hole E (c -> f -> value (n) ((s : (c_0 -> f_0)) ))) env-ß env-σ ((contract C_1 {(T_1 x_11) ... K_1 F_1 ...}) ... (contract C {(T_0 x_01) ... (T_s s_s) (T_02 x_02) ... K F_01 ... (T_f f_0 ((T_fx x_f) ...) {return e}) F_02 ...}) (contract C_2 {(T_2 x_21) ... K_2 F_2 ...}) ...)]
        [(in-hole E (return (call env-ß
                                  ((contract C_1 {(T_1 x_11) ... K_1 F_1 ...}) ... (contract C {(T_0 x_01) ... (T_s s_s) (T_02 x_02) ... K F_01 ... (T_f f_0 ((T_fx x_f) ...) {return e}) F_02 ...}) (contract C_2 {(T_2 x_21) ... K_2 F_2 ...}) ...) c 
                                  (top-σ env-σ) f n ((s : (c_0 -> f_0)) )))) (declcall (uptbal (uptbal env-ß (ref env-ß c) n) (top-σ env-σ) ,(- (term 0)(term n))) c ((s -> (c_0 -> f_0)) )) (call-σ env-σ (ref env-ß c))
                                                                             ((contract C_1 {(T_1 x_11) ... K_1 F_1 ...}) ... (contract C {(T_0 x_01) ... (T_s s_s) (T_02 x_02) ... K F_01 ... (T_f f_0 ((T_fx x_f) ...) {return e}) F_02 ...}) (contract C_2 {(T_2 x_21) ... K_2 F_2 ...}) ...)]
        
        "CALL2") 
   #|(--> [(in-hole E (c -> f -> value (n) ((s : (c_p -> f_p)) (s_v : vv_v) ...))) env-ß env-σ CT]
        [(in-hole E ()) env-ß env-σ CT]
        "CALL3")|#
   (--> [(in-hole E (c -> f -> value (n) ((s : (c_1 -> x)) ...))) env-ß env-σ CT]
        [(in-hole E (c -> f -> value (n) ((s : (state-sel env-ß c_1 x)) ...))) env-ß env-σ CT]
        "CALL3")
   
   (--> [(in-hole E (c -> f -> value (n) -> sender (a) ((s : v) ...))) (env-ß_1 ... (ß_1 ... (x -> c) ß_2 ...) env-ß_2 ...) env-σ CT]
        [(in-hole E (return (call (env-ß_1 ... (ß_1 ... (x -> c) ß_2 ...) env-ß_2 ...) CT (find (env-ß_1 ... (ß_1 ... (x -> c) ß_2 ...) env-ß_2 ...) c) a f n ((s : v) ...)))) (declcall (uptbal (uptbal (env-ß_1 ... (ß_1 ... (x -> c) ß_2 ...) env-ß_2 ...) (ref (env-ß_1 ... (ß_1 ... (x -> c) ß_2 ...) env-ß_2 ...) c) n) a ,(- (term 0)(term n))) c ((s -> v) ...)) (call-σ env-σ (ref (env-ß_1 ... (ß_1 ... (x -> c) ß_2 ...) env-ß_2 ...) c)) CT]
        "CALLTOPLEVEL")
   #|(--> [(in-hole E (c -> f -> value (n) -> sender (a) ((s : v) ...))) env-ß env-σ CT]
        [(in-hole E (return (call env-ß CT (find env-ß c) a f n ((s : v) ...)))) (decl (uptbal (uptbal env-ß (ref env-ß c) n) a ,(- (term 0)(term n))) ((s -> v) ...)) (call-σ env-σ (ref env-ß c)) CT]
        "CALLTOPLEVEL")|#
   (--> [(in-hole E (return v)) env-ß env-σ CT]
        [(in-hole E v) env-ß (rem-σ env-σ) CT]
        "RETURN")
   (--> [(in-hole E (return revert)) env-ß env-σ CT]
        [(in-hole E revert) env-ß (rem-σ env-σ) CT]
        "RETURN-R")
   ;Money transfer
   (--> [(in-hole E (a -> transfer (n))) env-ß env-σ CT]
        [(in-hole E ;u) 
                  (return (callfb env-ß CT (ref env-ß a) (top-σ env-σ) n)))
                  (decl (uptbal (uptbal env-ß a n) (top-σ env-σ) ,(- (term 0)(term n))) ()) (call-σ env-σ a) CT]
        "TRANSFER")
   (--> [(in-hole E ((c -> f) -> value (n) ((s : vv) ...))) env-ß env-σ CT]
        [(in-hole E (c -> f -> value (n) ((s : vv) ...))) env-ß env-σ CT]
        "REM-PARENTHESIS")
   (--> [(in-hole E (a -> f -> value (n) ((s : v) ...))) env-ß env-σ CT]
        [(in-hole E ((ref env-ß a) -> f -> value (n) ((s : v) ...))) env-ß env-σ CT]
        "REF-ADDRESS")
   (--> [(in-hole E (return (return (return (e))))) env-ß env-σ CT]
        [(in-hole E s) env-ß env-σ CT]
        )
   ))

;;;;;Reduction Relations;;;;;
(define-metafunction FS
  decl : env-ß any -> env-ß
  [(decl ((ß_1 ...) env-ß ...) (s -> vv)) ((ß_1 ... (s -> vv)) env-ß ...)
                                  (side-condition (not (member (term (s -> _)) (term (ß_1 ...)))))
                                  (side-condition (not (member (term (s -> _)) (term (env-ß ...)))))]
  [(decl ((ß_1 ...) env-ß ...) contracts) ((ß_1 ... contracts) env-ß ...)
                                  (side-condition (not (member (term contracts) (term (ß_1 ...)))))]
  [(decl ((ß_1 ...) env-ß ...) ((s -> vv) ...)) ((ß_1 ... (s -> vv) ...) env-ß ...)
                                  (side-condition (not (member (term ((s -> _) ...)) (term (ß_1 ...)))))
                                  (side-condition (not (member (term ((s -> _) ...)) (term (env-ß ...)))))        ])

(define-metafunction FS
  declcall : env-ß c any -> env-ß
  [(declcall (env-ß_1 ... (ß_1 ... ((c a) -> (C (s_0 : v)... n) -> (s -> v_0) ...) ß_2 ...) env-ß_2 ...) c ((s -> vv) ...))
   (env-ß_1 ... (ß_1 ... ((c a) -> (C (s_0 : v)... n) -> (s -> vv) ...) (s -> v_0) ... ß_2 ...) env-ß_2 ...)]
  [(declcall (env-ß_1 ... (ß_1 ... ((c a) -> (C (s_0 : v)... n) -> (x -> v_0) ...) ß_2 ...) env-ß_2 ...) c ((s -> vv) ...))
   (env-ß_1 ... (ß_1 ... ((c a) -> (C (s_0 : v)... n) -> (x -> v_0) ... (s -> vv) ...) ß_2 ...) env-ß_2 ...)]
  )




(define-metafunction FS
  ref : env-ß any -> any
  [(ref (env-ß_1 ... (ß_1 ... ((c a) -> (C (s : v)... n) -> (x -> v_0) ...) ß_2 ...) env-ß_2 ...) c) a
                                   (side-condition (not (member (term ((c a) -> (C (s : v)... n) -> (x -> v_0) ...)) (term (ß_1 ...)))))]
  [(ref (env-ß_1 ... (ß_1 ... ((c a) -> (C (s : v)... n) -> (x -> v_0) ...) ß_2 ...) env-ß_2 ...) a) c
                                   (side-condition (not (member (term ((c a) -> (C (s : v)... n) -> (x -> v_0) ...)) (term (ß_1 ...)))))]
  [(ref (env-ß_1 ... (ß_1 ... (x -> c) ß_2 ...) env-ß_2 ...) x) (ref (env-ß_1 ... (ß_1 ... (x -> c) ß_2 ...) env-ß_2 ...) c)
                                   (side-condition (not (member (term (x -> c)) (term (ß_1 ...)))))]
  ;[(find env-ß v) v
  ;                                 (side-condition (not (member (term v) (term env-ß))))]
  )

(define-metafunction FS
  find : env-ß any -> any
  [(find (env-ß_1 ... (ß_1 ... ((c a) -> (C (s : v)... n) -> (x_1 -> v_1) ... (x -> v_0) (x_2 -> v_2) ...) ß_2 ...) env-ß_2 ...) x) v_0
                                    (side-condition (not (member (term (x -> _)) (term (ß_2 ...)))))]
  [(find (env-ß_1 ... (ß_1 ... (x -> v) ß_2 ...) env-ß_2 ...) x) v
                                   (side-condition (not (member (term (x -> _)) (term (ß_2 ...)))))
                                   (side-condition (not (member (term (x -> _)) (term (ß_1 ...)))))]
  [(find env-ß v) v
                                   ;(side-condition (not (member (term v) (term env-ß))))
]
  )

(define-metafunction FS
  findvar : env-ß any any -> any
  [(findvar (env-ß_1 ... (ß_1 ... ((c a) -> (C (s : v)... n) -> (x_1 -> v_1) ... (x -> v_0) (x_2 -> v_2) ...) ß_2 ...) env-ß_2 ...) c x) v_0]
  [(findvar (env-ß_1 ... (ß_1 ... ((c a) -> (C (s : v)... n) -> (x_1 -> v_1) ... (x -> v_0) (x_2 -> v_2) ...) ß_2 ...) env-ß_2 ...) a x) v_0]
  [(findvar (env-ß_1 ... (ß_1 ... (x -> v) ß_2 ...) env-ß_2 ...) _ x) v]
  [(findvar env-ß _ v) v]
  [(findvar env-ß _ x) x])

(define-metafunction FS
  assign : env-ß x v -> env-ß
  [(assign (env-ß_1 ... (ß_1 ... ((c a) -> (C (x_1 : v_1)... (x : v_old) (x_2 : v_2)... n) -> (x_0 -> v_0) ...) var ...) ) x v)
           (env-ß_1 ... (ß_1 ... ((c a) -> (C (x_1 : v_1) ... (x : v) (x_2 : v_2)... n) -> (x_0 -> v_0) ...) var ...) )]
  [(assign (env-ß_1 ... (ß_1 ... (x -> v_old) ß_2 ...) env-ß_2 ...) x v)
           (env-ß_1 ... (ß_1 ... (x -> v) ß_2 ...) env-ß_2 ...)]
  
  
  )

(define-metafunction FS
  mappass : M v_1 v_2 -> M
  [(mappass (M_1 ...  (v_01 v_001)... (v_1 v_old) (v_02 v_002)... M_2 ...) v_1 v)
   (M_1 ... (v_01 v_001)... (v_1 v) (v_02 v_002)... M_2 ...) ]
 
  [(mappass ((v_01 v_02) ...) v_1 v_2)
   ((v_01 v_02) ... (v_1 v_2)) (side-condition (not (member (term v_1) (term ((v_01 v_02)...)))))])

(define-metafunction FS
  mappsel : M v -> v
  [(mappsel (M_1 ... (v_01 v_001)... (v v_1) (v_02 v_002)... M_2 ...) v) v_1]
  [(mappsel M v) 0])

(define-metafunction FS
  call : env-ß CT c a f n ((s : vv) ...) -> e
  [(call (env-ß_1 ... (ß_1 ... ((c a_0) -> (C (x_01 : vv_01)... n_0) -> (x_0 -> v_0) ...) ß_2 ...) env-ß_2 ...)
         ((contract C_1 {(T_1 x_11) ... K_1 F_1 ...}) ... (contract C {(T_0 x_01) ... K F_01 ... (T f ((T_00 x_00) ... ) {return e}) F_02 ...}) (contract C_2 {(T_2 x_21) ... K_2 F_2 ...}) ...)
         c a f n ((s : vv) ...))
   (subst-x ((s : vv) ...) (subst-e c a n e)) (side-condition (not (member (term ((s : _) ...)) (term (ß_1 ...)))))
   (side-condition (not (member (term ((s : _) ...)) (term (ß_2 ...)))))
   (side-condition (not (member (term ((s : _) ...)) (term (env-ß_1 ...)))))
   (side-condition (not (member (term ((s : _) ...)) (term (env-ß_2 ...)))))]
  [(call (env-ß_1 ... (ß_1 ... ((c a_0) -> (C (x_01 : vv_01)... n_0) -> (x_0 -> v_0) ...) ß_2 ...) env-ß_2 ...)
         ((contract C_1 {(T_1 x_11) ... K_1 F_1 ...}) ... (contract C {(T_0 x_01) ... K F_01 ... (T f ((T_00 x_00) ... ) {return e}) F_02 ...}) (contract C_2 {(T_2 x_21) ... K_2 F_2 ...}) ...)
         a_0 a f n ((s : vv) ...))
   (subst-x ((s : vv) ...) (subst-e c a_0 n e)) (side-condition (not (member (term ((s : _) ...)) (term (ß_1 ...))))) (side-condition (not (member (term ((s : _) ...)) (term (ß_2 ...)))))
   (side-condition (not (member (term ((s : _) ...)) (term (env-ß_1 ...)))))
   (side-condition (not (member (term ((s : _) ...)) (term (env-ß_2 ...)))))]
  [(call (env-ß_1 ... (ß_1 ... ((c a_0) -> (C (x_01 : vv_01)... n_0) -> (x_0 -> v_0) ...) ß_2 ...) env-ß_2 ...)
         ((contract C_1 {(T_1 x_11) ... K_1 F_1 ...}) ... (contract C {(T_0 x_01) ... K F_01 ... (T f ((T_00 x_00) ... ) {return e}) F_02 ...}) (contract C_2 {(T_2 x_21) ... K_2 F_2 ...}) ...)
         c a f n ((s : vv) ...))
   (subst-x ((s : vv) ...) (subst-e c a n e)) (side-condition (not (member (term ((s : _) ...)) (term (ß_1 ...)))))
   (side-condition (not (member (term ((s : _) ...)) (term (ß_2 ...)))))
   (side-condition (not (member (term ((s : _) ...)) (term (env-ß_1 ...)))))
   (side-condition (not (member (term ((s : _) ...)) (term (env-ß_2 ...)))))]
)
#|(define-metafunction FS
  call : env-ß CT c a f n ((s : v) ...) -> e
  [(call (env-ß_1 ... (ß_1 ... ((c a_0) -> (C (x_01 : v_01)... n_0)) ß_2 ...) env-ß_2 ...)
         ((contract C_1 {(T_1 x_11) ... K_1 F_1 ...}) ... (contract C {(T_0 x_01) ... K F_01 ... (T f ((T_00 x_00) ... ) {return e}) F_02 ...}) (contract C_2 {(T_2 x_21) ... K_2 F_2 ...}) ...)
         c a f n ((s : v) ...))
   (subst-x ((s : v) ...) (subst-e c a n e))]
  [(call (env-ß_1 ... (ß_1 ... ((c a_0) -> (C (x_01 : v_01)... n_0)) ß_2 ...) env-ß_2 ...)
         ((contract C_1 {(T_1 x_11) ... K_1 F_1 ...}) ... (contract C {(T_0 x_01) ... K F_01 ... (T f ((T_00 x_00) ... ) {return e}) F_02 ...}) (contract C_2 {(T_2 x_21) ... K_2 F_2 ...}) ...)
         a_0 a f n ((s : v) ...))
   (subst-x ((s : v) ...) (subst-e c a_0 n e))]
  [(call (env-ß_1 ... (ß_1 ... ((c a_0) -> (C (x_01 : v_01)... n_0)) ß_2 ...) env-ß_2 ...)
         ((contract C_1 {(T_1 x_11) ... K_1 F_1 ...}) ... (contract C {(T_0 x_01) ... K F_01 ... (T f ((T_00 x_00) ... ) {return e}) F_02 ...}) (contract C_2 {(T_2 x_21) ... K_2 F_2 ...}) ...)
         c a f n ((s : v) ...))
   (subst-x ((s : v) ...) (subst-e c a n e))]
)|#

(define-metafunction FS
  callfb : env-ß CT c a n -> e
  [(callfb (env-ß_1 ... (ß_1 ... ((c a_0) -> (C (x_01 : v_01)... n_0) -> (x_0 -> v_0) ...) ß_2 ...) env-ß_2 ...)
          ((contract C_1 {(T_1 x_11) ... K_1 F_1 ...}) ... (contract C {(T_0 x_01) ... K F_01 ... (unit fb () {return e}) F_02 ...}) (contract C_2 {(T_2 x_21) ... K_2 F_2 ...}) ...) c a n)
   (subst-e c a n e)])

(define-metafunction FS
  state-sel : env-ß c s -> any
  [(state-sel (env-ß_1 ... (ß_1 ... ((c a) -> (C (s_1 : v_1) ... (s : v) (s_2 : v_2) ... n)  -> (x_0 -> v_0) ...) ß_2 ...) env-ß_2 ...) c s)
   v (side-condition (not (member (term ((c a) -> (C (s_1 : v_1) ... (s : v) (s_2 : v_2) ... n) -> (x_0 -> v_0) ...)) (term (ß_1 ...)))))]
  [(state-sel env-ß c s)
   (c -> s)]
  )

(define-metafunction FS
  state-ass : env-ß c s v -> env-ß
  [(state-ass (env-ß_1 ... (ß_1 ... ((c a) -> (C (s_1 : v_1) ... (s : v_old) (s_2 : v_2) ... n) -> (x_0 -> v_0) ...) ß_2 ...) env-ß_2 ...) c s v)
   (env-ß_1 ... (ß_1 ... ((c a) -> (C (s_1 : v_1) ... (s : v) (s_2 : v_2) ... n) -> (x_0 -> v_0) ...) ß_2 ...) env-ß_2 ...)])

(define-metafunction FS
  uptbal : env-ß any n -> env-ß
  [(uptbal (env-ß_1 ... (ß_1 ... ((c a) -> (C (s : vv)... n_old) -> (x_0 -> vv_0) ...) ß_2 ...) env-ß_2 ...) a n)
   (env-ß_1 ... (ß_1 ... ((c a) -> (C (s : vv)... ,(+ (term n_old)(term n))) -> (x_0 -> vv_0) ...) ß_2 ...) env-ß_2 ...)]
  [(uptbal (env-ß_1 ... (ß_1 ... ((c a) -> (C (s : vv)... n_old) -> (x_0 -> vv_0) ...) ß_2 ...) env-ß_2 ...) c n)
   (env-ß_1 ... (ß_1 ... ((c a) -> (C (s : vv)... ,(+ (term n_old)(term n))) -> (x_0 -> vv_0) ...) ß_2 ...) env-ß_2 ...)])

;Checks if there's an address on top
(define-metafunction FS
  check-σ : env-σ env-ß -> any
  [(check-σ (ß-v_1 ...) (ß-v_2 ...))
   (ß-v_2 ...)]
  [(check-σ env-σ env-ß)
   env-σ])

;Adds address to the top of the stack
(define-metafunction FS
  call-σ : env-σ σ -> env-σ
  [(call-σ (ß-v ... σ-v ... ) σ) ( ß-v ... σ-v ... (σ) )])

;Removes address on top of the stack
(define-metafunction FS
  rem-σ : env-σ -> env-σ
  [(rem-σ (ß-v ... σ-v ... (σ))) ( ß-v ... σ-v ...)])

(define-metafunction FS
  top-σ : env-σ -> any
  [(top-σ ( ß-v ... σ-v ... (σ) )) σ]
  [(top-σ ( ß-v ...  )) ()]
  [(top-σ (())) ()]
  )

(define-metafunction FS
  rev : env-σ -> env-ß
  [(rev (ß-v ... σ-v ... )) (ß-v ...)])


;Replaces parameters for their values
(define-metafunction FS
  subst-x : ((x : vv) ...) any -> any
  [(subst-x ((x : vv) ...) (e_0 [e_1 -> e_2]))
   ((subst-x ((x : vv) ...) e_0) [(subst-x ((x : vv) ...) e_1) -> (subst-x ((x : vv) ...) e_2)])]
  [(subst-x ((x : v) ...) (e_1 -> f -> value (e_2) ((x_1 : vv_1) ...)))
   ((subst-x ((x : v) ...) e_1) -> f -> value (e_2) (subst-x ((x : v) ...) ((x_1 : vv_1) ...)))]
  [(subst-x ((x : vv) ...) (f -> value (e_2) ((x_1 : vv_1) ...)))
   ((subst-x ((x : vv) ...) f) -> value (e_2) (subst-x ((x : vv) ...) ((x_1 : vv_1) ...)))]
  [(subst-x ((x : vv) ...) (e_1 -> e_2))
   ((subst-x ((x : vv) ...) e_1) -> (subst-x ((x : vv) ...) e_2))]
  [(subst-x ((x : vv) ...) (e_0 -> s = e_1))
   ((subst-x ((x : vv) ...) e_0) -> s = (subst-x ((x : vv) ...) e_1))]
  
  [(subst-x ((x : vv) ...) (if e_1 then e_2 else e_3))
   (if (subst-x ((x : vv) ...) e_1) then (subst-x ((x : vv) ...) e_2) else (subst-x ((x : vv) ...) e_3))]
  [(subst-x ((x : vv) ...) (e_1 e_2))
   ((subst-x ((x : vv) ...) e_1) (subst-x ((x : vv) ...) e_2))]
  [(subst-x ((x : vv) ...) (e_1 a-op e_2))
   ((subst-x ((x : vv) ...) e_1) a-op (subst-x ((x : vv) ...) e_2))]
  [(subst-x ((x : vv) ...) (e_1 b-op1 e_2))
   ((subst-x ((x : vv) ...) e_1) b-op1 (subst-x ((x : vv) ...) e_2))]
  [(subst-x ((x : vv) ...) (e_1 b-op2 e_2))
   ((subst-x ((x : vv) ...) e_1) b-op2 (subst-x ((x : vv) ...) e_2))]
  [(subst-x ((x : vv) ...) ((x : vv_1) ...))
   ((x : vv) ...)]
  [(subst-x ((x_1 : vv_1) ... (x : vv) (x_2 : vv_2) ...) x)
   vv]
  [(subst-x ((x_1 : vv_1) ... (x : vv) (x_2 : vv_2) ...) (x_0 : vv_0))
   (x_0 : vv_0)]
  [(subst-x ((x : vv)...) ((x_0 : vv_0)...))
   ((x_0 : vv_0) ...)]
  [(subst-x ((x : vv) ...) x_0)
   x_0]
  [(subst-x ((x : vv) ...) vv_0)
   vv_0]
  
  [(subst-x ((x : vv) ...) e)
   e]
  )

#|(define-metafunction FS
  subst-x : ((x : v) ...) any -> any
  [(subst-x ((x : v) ...) (e_0 [e_1 -> e_2]))
   ((subst-x ((x : v) ...) e_0) [(subst-x ((x : v) ...) e_1) -> (subst-x ((x : v) ...) e_2)])]
  [(subst-x ((x : v) ...) (e_1 -> f -> value (e_2) ((x_1 : v_1) ...)))
   ((subst-x ((x : v) ...) e_1) -> f -> value (e_2) (subst-x ((x : v) ...) ((x_1 : v_1) ...)))]
  [(subst-x ((x : v) ...) (e_1 -> e_2))
   ((subst-x ((x : v) ...) e_1) -> (subst-x ((x : v) ...) e_2))]
  [(subst-x ((x : v) ...) (e_0 -> s = e_1))
   ((subst-x ((x : v) ...) e_0) -> s = (subst-x ((x : v) ...) e_1))]
  
  [(subst-x ((x : v) ...) (if e_1 then e_2 else e_3))
   (if (subst-x ((x : v) ...) e_1) then (subst-x ((x : v) ...) e_2) else (subst-x ((x : v) ...) e_3))]
  [(subst-x ((x : v) ...) (e_1 e_2))
   ((subst-x ((x : v) ...) e_1) (subst-x ((x : v) ...) e_2))]
  [(subst-x ((x : v) ...) (e_1 * e_2))
   ((subst-x ((x : v) ...) e_1) * (subst-x ((x : v) ...) e_2))]
  [(subst-x ((x : v) ...) ((x : v_1) ...))
   ((x : v) ...)]
  [(subst-x ((x_1 : v_1) ... (x : v) (x_2 : v_2) ...) x)
   v]
  [(subst-x ((x_1 : v_1) ... (x : v) (x_2 : v_2) ...) (x_0 : v_0))
   (x_0 : v_0)]
  [(subst-x ((x : v)...) ((x_0 : v_0)...))
   ((x_0 : v_0) ...)]
  [(subst-x ((x : v) ...) x_0)
   x_0]
  [(subst-x ((x : v) ...) v_0)
   v_0]
  
  [(subst-x ((x : v) ...) e)
   e]
  )|#
;Replaces the object identifier
(define-metafunction FS
  subst-e : c a n e -> e
  [(subst-e c a n this)
   c]
  [(subst-e c a n (msg -> sender))
   a]
  [(subst-e c a n (msg -> value))
   n]
  [(subst-e c a n (this -> x))
   (c -> x)]
  [(subst-e c a n (this -> x = e))
   (c -> x = (subst-e c a n e))]
  [(subst-e c a n (T x = e))
   (T x = (subst-e c a n e))]
  [(subst-e c a n (e_0 [e_1 -> e_2]))
   ((subst-e c a n e_0) [(subst-e c a n e_1) -> (subst-e c a n e_2)])]
  [(subst-e c a n (e_1 (e_2)))
   ((subst-e c a n e_1) ((subst-e c a n e_2)))]
  
  [(subst-e c a n (e_1 -> e_2))
   ((subst-e c a n e_1) -> (subst-e c a n e_2))]
  [(subst-e c a n (e_1 -> f -> value (e_2) ((x : e_3) ...)))
   ((subst-e c a n e_1) -> f -> value ((subst-e c a n e_2)) ((x : (subst-e c a n e_3)) ...))]
  [(subst-e c a n (e_1 -> f -> value (e_2) -> sender (e_4) ((x : e_3) ...)))
   ((subst-e c a n e_1) -> f -> value ((subst-e c a n e_2)) -> sender ((subst-e c a n e_4)) ((x : (subst-e c a n e_3)) ...))]
  [(subst-e c a n (f -> value (e_2) ((x : e_3) ...)))
   (f -> value ((subst-e c a n e_2)) ((x : (subst-e c a n e_3)) ...))]
  [(subst-e c a n (if e_1 then e_2 else e_3))
   (if (subst-e c a n e_1) then (subst-e c a n e_2) else (subst-e c a n e_3))]
  [(subst-e c a n (e_1 a-op e_2))
   ((subst-e c a n e_1) a-op (subst-e c a n e_2))]
  [(subst-e c a n (e_1 b-op1 e_2))
   ((subst-e c a n e_1) b-op1 (subst-e c a n e_2))]
  [(subst-e c a n (e_1 b-op2 e_2))
   ((subst-e c a n e_1) b-op2 (subst-e c a n e_2))]
  [(subst-e c a n (e_1 -> transfer (e_2)))
   ((subst-e c a n e_1) -> transfer ((subst-e c a n e_2)))]
  ;[(subst-e c a n (e)) ((subst-e c a n e))]
  [(subst-e c a n vv) vv]
  [(subst-e c a n revert) revert]
  [(subst-e c a n (e_1 e_2))
   ((subst-e c a n e_1) (subst-e c a n e_2))]
  [(subst-e c a n u) u]
  [(subst-e c a n x) x]
  ;[(subst-e c a n e) e]
  )


;testing
;decl
;(traces s->ßs (term ( (xEOA := 4) (()) (()) ((contract C {})))))
;(traces s->ßs (term ( (xEOA := (new C -> value (3) () (cC cA))) (()) (()) ((contract C {})))))

;com construtor
;(traces s->ßs (term ( (xEOA := (new C -> value (3) () (cC cA))) (()) (()) ((contract C {(C (a) {(this -> s = a)})})))))

;com tipos
;(traces s->ßs (term ( (C xEOA = (new C -> value (3) () (cC cA))) (()) (()) ((contract C {(bool s) (C ((bool a)) {(this -> s = a)})})))))
;(traces s->ßs (term ( (C xEOA = (new C -> value (3) ((s : 4)) (cC cA))) (()) (()) ((contract C {(bool s) (C ((bool a)) {(this -> s = a)})})))))

;BloodBank
;(traces s->ßs (term ( (BloodBank xEOA = (new BloodBank -> value (3) ((doctor : 4) (blood : 3)) (cC cA))) (()) (()) ((contract BloodBank {(address doctor) (uint blood) (BloodBank ((address doctor) (uint blood)) {(this -> doctor = doctor) (this -> blood = blood)})})))))
;(traces s->ßs (term ( (BloodBank yBank = (new BloodBank -> value (3) ((healthy : ()) (doctor : 4) (blood : 3)) (cBank aBank))) (()) (()) ((contract EOC {(EOC () {}) (unit fb () {return u})}) (contract BloodBank {((mapping (address => bool)) healthy) (address doctor) (uint blood) (BloodBank (((mapping (address => bool)) healthy) (address doctor) (uint blood)) {(this -> healthy = healthy) (this -> doctor = doctor) (this -> blood = blood)})})))))

#|(traces s->ßs (term ( ((EOC xDoctor = (new EOC -> value (0) () (cDoctor aDoctor))) (EOC wHumanDonor = (new EOC -> value (0) () (cHumanDonor aHumanDonor))) (BloodBank yBank = (new BloodBank -> value (0) ((healthy : ()) (doctor : 0) (blood : 0)) (cBank aBank))) (Donor zDonor = (new Donor -> value (0) ((blood : 5000) (bank : (address (yBank)))) (cDonor aDonor)))) (()) (())
              ((contract EOC {(EOC () {}) (unit fb () {return u})})
              (contract BloodBank {
                                   ((mapping (address => bool)) healthy)
                                   (address doctor)
                                   (uint blood)
                                   (BloodBank (((mapping (address => bool)) healthy) (address doctor) (uint blood)) {(this -> healthy = healthy) (this -> doctor = doctor) (this -> blood = blood)})})
              (contract Donor {
                               (uint blood)
                               (address bank)
                               (Donor ((uint blood) (address bank)) {(this -> blood = blood) (this -> bank = bank)})})))))|#

#|(traces s->ßs (term ( ((EOC xDoctor = (new EOC -> value (0) () (cDoctor aDoctor))) (EOC wHumanDonor = (new EOC -> value (0) () (cHumanDonor aHumanDonor))) (BloodBank yBank = (new BloodBank -> value (0) ((healthy : ()) (doctor : (address (xDoctor))) (blood : 0)) (cBank aBank))) (Donor zDonor = (new Donor -> value (0) ((blood : 5000) (bank : (address (yBank)))) (cDonor aDonor)))) (()) (())
              ((contract EOC {(EOC () {}) (unit fb () {return u})})
              (contract BloodBank {
                                   ((mapping (address => bool)) healthy)
                                   (address doctor)
                                   (uint blood)
                                   (BloodBank (((mapping (address => bool)) healthy) (address doctor) (uint blood)) {(this -> healthy = healthy) (this -> doctor = doctor) (this -> blood = blood)})})
              (contract Donor {
                               (uint blood)
                               (address bank)
                               (Donor ((uint blood) (address bank)) {(this -> blood = blood) (this -> bank = bank)})})))))|#

#|(traces s->ßs (term ( ((EOC xDoctor = (new EOC -> value (0) () (cDoctor aDoctor))) (EOC wHumanDonor = (new EOC -> value (0) () (cHumanDonor aHumanDonor))) (BloodBank yBank = (new BloodBank -> value (0) ((healthy : ()) (doctor : (address (xDoctor))) (blood : 0)) (cBank aBank))) (Donor zDonor = (new Donor -> value (0) ((blood : 5000) (bank : (address (yBank)))) (cDonor aDonor))) (yBank -> setHealth -> value (0) -> sender ((address (xDoctor))) ())) (()) (())
              ((contract EOC {(EOC () {}) (unit fb () {return u})})
              (contract BloodBank {
                                   ((mapping (address => bool)) healthy)
                                   (address doctor)
                                   (uint blood)
                                   (BloodBank (((mapping (address => bool)) healthy) (address doctor) (uint blood)) {(this -> healthy = healthy) (this -> doctor = doctor) (this -> blood = blood)})
                                   (unit setHealth ((address donor) (bool isHealthy)) {return (0)})})
              (contract Donor {
                               (uint blood)
                               (address bank)
                               (Donor ((uint blood) (address bank)) {(this -> blood = blood) (this -> bank = bank)})})))))|#

#|(traces s->ßs (term ( ((EOC xDoctor = (new EOC -> value (0) () (cDoctor aDoctor))) (EOC wHumanDonor = (new EOC -> value (0) () (cHumanDonor aHumanDonor))) (BloodBank yBank = (new BloodBank -> value (0) ((healthy : ()) (doctor : (address (xDoctor))) (blood : 0)) (cBank aBank))) (Donor zDonor = (new Donor -> value (0) ((blood : 5000) (bank : (address (yBank)))) (cDonor aDonor))) (yBank -> setHealth -> value (0) -> sender ((address (xDoctor))) ((donor : (address (xDoctor))) (isHealthy : true)))) (()) (())
              ((contract EOC {(EOC () {}) (unit fb () {return u})})
              (contract BloodBank {
                                   ((mapping (address => bool)) healthy)
                                   (address doctor)
                                   (uint blood)
                                   (BloodBank (((mapping (address => bool)) healthy) (address doctor) (uint blood)) {(this -> healthy = healthy) (this -> doctor = doctor) (this -> blood = blood)})
                                   (unit setHealth ((address donor) (bool isHealthy)) {return (if ((msg -> sender) == (this -> doctor)) then (this -> healthy = ((this -> healthy) [1 -> 3])) else 3)})})
              (contract Donor {
                               (uint blood)
                               (address bank)
                               (Donor ((uint blood) (address bank)) {(this -> blood = blood) (this -> bank = bank)})})))))|#

#|(traces s->ßs (term ( ((EOC xDoctor = (new EOC -> value (0) () (cDoctor aDoctor))) ((EOC wHumanDonor = (new EOC -> value (0) () (cHumanDonor aHumanDonor))) ((BloodBank yBank = (new BloodBank -> value (0) ((healthy : ()) (doctor : (address (xDoctor))) (blood : 0)) (cBank aBank))) ((Donor zDonor = (new Donor -> value (0) ((blood : 5000) (bank : (address (yBank)))) (cDonor aDonor))) (yBank -> setHealth -> value (0) -> sender ((address (xDoctor))) ((donor : (address (xDoctor))) (isHealthy : true))))))) (()) (())
              ((contract EOC {(EOC () {}) (unit fb () {return u})})
              (contract BloodBank {
                                   ((mapping (address => bool)) healthy)
                                   (address doctor)
                                   (uint blood)
                                   (BloodBank (((mapping (address => bool)) healthy) (address doctor) (uint blood)) {(this -> healthy = healthy) (this -> doctor = doctor) (this -> blood = blood)})
                                   (unit setHealth ((address donor) (bool isHealthy)) {return (if ((msg -> sender) == (this -> doctor)) then (this -> healthy = ((this -> healthy) [donor -> isHealthy])) else revert)})})
              (contract Donor {
                               (uint blood)
                               (address bank)
                               (Donor ((uint blood) (address bank)) {(this -> blood = blood) (this -> bank = bank)})})))))|#

#|(traces s->ßs (term ( ((EOC xDoctor = (new EOC -> value (0) () (cDoctor aDoctor))) ((EOC wHumanDonor = (new EOC -> value (0) () (cHumanDonor aHumanDonor))) ((BloodBank yBank = (new BloodBank -> value (0) ((healthy : ()) (doctor : (address (xDoctor))) (blood : 0)) (cBank aBank))) ((Donor zDonor = (new Donor -> value (0) ((blood : 5000) (bank : (address (yBank)))) (cDonor aDonor))) ((yBank -> setHealth -> value (0) -> sender ((address (xDoctor))) ((donor : (address (xDoctor))) (isHealthy : true))) (zDonor -> donate -> value (0) -> sender ((address (wHumanDonor))) ((amount : 500)) )))))) (()) (())
              ((contract EOC {(EOC () {}) (unit fb () {return u})})
              (contract BloodBank {
                                   ((mapping (address => bool)) healthy)
                                   (address doctor)
                                   (uint blood)
                                   (BloodBank (((mapping (address => bool)) healthy) (address doctor) (uint blood)) {(this -> healthy = healthy) (this -> doctor = doctor) (this -> blood = blood)})
                                   (unit setHealth ((address donor) (bool isHealthy)) {return (if ((msg -> sender) == (this -> doctor)) then (this -> healthy = ((this -> healthy) [donor -> isHealthy])) else revert)})})
              (contract Donor {
                               (uint blood)
                               (address bank)
                               (Donor ((uint blood) (address bank)) {(this -> blood = blood) (this -> bank = bank)})
                               (unit donate ((uint amount)) {return (BloodBank (this -> bank))})})))))|#

#|(traces s->ßs (term ( ((EOC xDoctor = (new EOC -> value (0) () (cDoctor aDoctor))) ((EOC wHumanDonor = (new EOC -> value (0) () (cHumanDonor aHumanDonor))) ((BloodBank yBank = (new BloodBank -> value (0) ((healthy : ()) (doctor : (address (xDoctor))) (blood : 0)) (cBank aBank))) ((Donor zDonor = (new Donor -> value (0) ((blood : 5000) (bank : (address (yBank)))) (cDonor aDonor))) ((yBank -> setHealth -> value (0) -> sender ((address (xDoctor))) ((donor : (address (xDoctor))) (isHealthy : true))) (zDonor -> donate -> value (0) -> sender ((address (wHumanDonor))) ((amount : 500)) )))))) (()) (())
              ((contract EOC {(EOC () {}) (unit fb () {return u})})
              (contract BloodBank {
                                   ((mapping (address => bool)) healthy)
                                   (address doctor)
                                   (uint blood)
                                   (BloodBank (((mapping (address => bool)) healthy) (address doctor) (uint blood)) {(this -> healthy = healthy) (this -> doctor = doctor) (this -> blood = blood)})
                                   (unit setHealth ((address donor) (bool isHealthy)) {return (if ((msg -> sender) == (this -> doctor)) then (this -> healthy = ((this -> healthy) [donor -> isHealthy])) else revert)})
                                   (bool donate ((uint amount)) {return (uint donorBlood = ((msg -> sender) -> getBlood -> value (0) ()))})
                                   (uint getBlood () {return (this -> blood)})})
              (contract Donor {
                               (uint blood)
                               (address bank)
                               (Donor ((uint blood) (address bank)) {(this -> blood = blood) (this -> bank = bank)})
                               (unit donate ((uint amount)) {return ((this -> bank) -> donate -> value (0) ((amount : amount)))})
                               (uint getBlood () {return (this -> blood)})})))))|#

#|(traces s->ßs (term ( ((EOC xDoctor = (new EOC -> value (0) () (cDoctor aDoctor))) ((EOC wHumanDonor = (new EOC -> value (0) () (cHumanDonor aHumanDonor))) ((BloodBank yBank = (new BloodBank -> value (0) ((healthy : ()) (doctor : (address (xDoctor))) (blood : 0)) (cBank aBank))) ((Donor zDonor = (new Donor -> value (0) ((blood : 5000) (bank : (address (yBank)))) (cDonor aDonor))) ((yBank -> setHealth -> value (0) -> sender ((address (xDoctor))) ((donor : (address (xDoctor))) (isHealthy : true))) (zDonor -> donate -> value (0) -> sender ((address (wHumanDonor))) ((amount : 500)) )))))) (()) (())
              ((contract EOC {(EOC () {}) (unit fb () {return u})})
              (contract BloodBank {
                                   ((mapping (address => bool)) healthy)
                                   (address doctor)
                                   (uint blood)
                                   (BloodBank (((mapping (address => bool)) healthy) (address doctor) (uint blood)) {(this -> healthy = healthy) (this -> doctor = doctor) (this -> blood = blood)})
                                   (unit setHealth ((address donor) (bool isHealthy)) {return (if ((msg -> sender) == (this -> doctor)) then (this -> healthy = ((this -> healthy) [donor -> isHealthy])) else revert)})
                                   (bool donate ((uint amount)) {return ((uint donorBlood = ((msg -> sender) -> getBlood -> value (0) ())) (if ((this -> healhy)[(msg -> sender)]) then true else false))})
                                   (uint getBlood () {return (this -> blood)})})
              (contract Donor {
                               (uint blood)
                               (address bank)
                               (Donor ((uint blood) (address bank)) {(this -> blood = blood) (this -> bank = bank)})
                               (unit donate ((uint amount)) {return ((this -> bank) -> donate -> value (0) ((amount : amount)))})
                               (uint getBlood () {return (this -> blood)})})))))|#

#|(traces s->ßs (term ( ((EOC xDoctor = (new EOC -> value (0) () (cDoctor aDoctor))) ((EOC wHumanDonor = (new EOC -> value (0) () (cHumanDonor aHumanDonor))) ((BloodBank yBank = (new BloodBank -> value (0) ((healthy : ()) (doctor : (address (xDoctor))) (blood : 0)) (cBank aBank))) ((Donor zDonor = (new Donor -> value (0) ((blood : 5000) (bank : (address (yBank)))) (cDonor aDonor))) ((yBank -> setHealth -> value (0) -> sender ((address (xDoctor))) ((donor : (address (zDonor))) (isHealthy : true))) (zDonor -> donate -> value (0) -> sender ((address (wHumanDonor))) ((amount : 500)) )))))) (()) (())
              ((contract EOC {(EOC () {}) (unit fb () {return u})})
              (contract BloodBank {
                                   ((mapping (address => bool)) healthy)
                                   (address doctor)
                                   (uint blood)
                                   (BloodBank (((mapping (address => bool)) healthy) (address doctor) (uint blood)) {(this -> healthy = healthy) (this -> doctor = doctor) (this -> blood = blood)})
                                   (unit setHealth ((address donor) (bool isHealthy)) {return (if ((msg -> sender) == (this -> doctor)) then (this -> healthy = ((this -> healthy) [donor -> isHealthy])) else revert)})
                                   (bool donate ((uint amount)) {return ((uint donorBlood = ((msg -> sender) -> getBlood -> value (0) ())) (if (((this -> healthy)[(msg -> sender)]) && ((donorBlood > 3000) && ((donorBlood - amount) > 0))) then ((this -> blood = ((this -> blood) + amount)) true) else false))})
                                   (uint getBlood () {return (this -> blood)})})
              (contract Donor {
                               (uint blood)
                               (address bank)
                               (Donor ((uint blood) (address bank)) {(this -> blood = blood) (this -> bank = bank)})
                               (unit donate ((uint amount)) {return (if ((this -> bank) -> donate -> value (0) ((amount : amount))) then ((this -> blood = ((this -> blood) - amount)) u) else u)})
                               (uint getBlood () {return (this -> blood)})})))))|#


;applier
#|(traces s->ßs (term ( ((EOC xEOA = (new EOC -> value (0) () (cEOA aEOA))) ((Applier yApp = (new Applier -> value (0) ((state : 10)) (cApp aApp))) ((Test zTest = (new Test -> value (0) ((app : yApp)) (cTest aTest))) (zTest -> f1 -> value (0) -> sender ((address (xEOA))) ()) ))) (()) (())
              ((contract EOC {(EOC () {}) (unit fb () {return u})})
               (contract Applier {(uint state)
                                  (Applier ((uint state)) {(this -> state = state)})
                                  (unit apply (((uint -> uint) f)) {return (f -> value (0) ((n : (this -> state))))})})
               (contract Test {(Applier app)
                               (Test ((Applier app)) {(this -> app = app)})
                               (unit f1 () {return ((this -> app) -> apply -> value (0) ((f : (this -> square))))})
                               (unit square ((uint n)) {return (n * n)})})
              ))))|#



;Bank
#|(traces s->ßs (term ( ((EOC xEOA = (new EOC -> value (0) () (cEOA aEOA))) ((Bank yBank = (new Bank -> value (0) ((balances : ())) (cBank aBank))) (yBank -> deposit -> value (500) -> sender ((address (xEOA))) ()))) (()) (())
              ((contract EOC {(EOC () {}) (unit fb () {return u})})
               (contract Bank {
                               ((mapping (address => unit)) balances)
                               (Bank (((mapping (address => unit)) balances)) {(this -> balances = balances)})
                               (unit deposit () {return (this -> balances = ((this -> balances)[(msg -> sender) -> (((this -> balances)[msg -> sender]) + (msg -> value))]))})})
               
              ))))|#

#|(traces s->ßs (term ( ((EOC xEOA = (new EOC -> value (0) () (cEOA aEOA))) ((Bank yBank = (new Bank -> value (0) ((balances : ())) (cBank aBank))) (yBank -> deposit -> value (500) -> sender ((address (xEOA))) ()))) (()) (())
              ((contract EOC {(EOC () {}) (unit fb () {return u})})
               (contract Bank {
                               ((mapping (address => unit)) balances)
                               (Bank (((mapping (address => unit)) balances)) {(this -> balances = balances)})
                               (unit deposit () {return (this -> balances = ((this -> balances)[(msg -> sender) -> (((this -> balances)[(msg -> sender)]) + (msg -> value))]))})})
               
              ))))|#

#|(traces s->ßs (term ( ((EOC xEOA = (new EOC -> value (1000) () (cEOA aEOA))) ((Bank yBank = (new Bank -> value (0) ((balances : ())) (cBank aBank))) ((yBank -> deposit -> value (500) -> sender ((address (xEOA))) ()) (yBank -> withdraw -> value (0) -> sender ((address (xEOA))) ((amount : 100)))))) (()) (())
              ((contract EOC {(EOC () {}) (unit fb () {return u})})
               (contract Bank {
                               ((mapping (address => unit)) balances)
                               (Bank (((mapping (address => unit)) balances)) {(this -> balances = balances)})
                               (unit deposit () {return (this -> balances = ((this -> balances)[(msg -> sender) -> (((this -> balances)[(msg -> sender)]) + (msg -> value))]))})
                               (unit withdraw ((uint amount)) {return (if (((this -> balances)[(msg -> sender)]) >= amount) then ((this -> balances = ((this -> balances)[(msg -> sender) -> (((this -> balances)[(msg -> sender)]) - amount)])) (3)) else 2)})})
               
              ))))|#

#|(traces s->ßs (term ( ((EOC xEOA = (new EOC -> value (1000) () (cEOA aEOA))) ((Bank yBank = (new Bank -> value (0) ((balances : ())) (cBank aBank))) ((yBank -> deposit -> value (500) -> sender ((address (xEOA))) ()) (yBank -> withdraw -> value (0) -> sender ((address (xEOA))) ((amount : 100)))))) (()) (())
              ((contract EOC {(EOC () {}) (unit fb () {return u})})
               (contract Bank {
                               ((mapping (address => unit)) balances)
                               (Bank (((mapping (address => unit)) balances)) {(this -> balances = balances)})
                               (unit deposit () {return (this -> balances = ((this -> balances)[(msg -> sender) -> (((this -> balances)[(msg -> sender)]) + (msg -> value))]))})
                               (unit withdraw ((uint amount)) {return (if (((this -> balances)[(msg -> sender)]) >= amount) then ((this -> balances = ((this -> balances)[(msg -> sender) -> (((this -> balances)[(msg -> sender)]) - amount)])) ((msg -> sender) -> transfer (amount))) else 2)})})
               
              ))))|#

#|(traces s->ßs (term ( ((EOC xEOA = (new EOC -> value (1000) () (cEOA aEOA))) ((Bank yBank = (new Bank -> value (0) ((balances : ())) (cBank aBank))) ((yBank -> deposit -> value (500) -> sender ((address (xEOA))) ()) (yBank -> withdraw -> value (0) -> sender ((address (xEOA))) ((amount : 100)))))) (()) (())
              ((contract EOC {(EOC () {}) (unit fb () {return (4 + 4)})})
               (contract Bank {
                               ((mapping (address => unit)) balances)
                               (Bank (((mapping (address => unit)) balances)) {(this -> balances = balances)})
                               (unit deposit () {return (this -> balances = ((this -> balances)[(msg -> sender) -> (((this -> balances)[(msg -> sender)]) + (msg -> value))]))})
                               (unit withdraw ((uint amount)) {return (if (((this -> balances)[(msg -> sender)]) >= amount) then ((this -> balances = ((this -> balances)[(msg -> sender) -> (((this -> balances)[(msg -> sender)]) - amount)])) ((msg -> sender) -> transfer (amount))) else u)})})
               
              ))))|#

#|(traces s->ßs (term ( ((EOC xEOA = (new EOC -> value (1000) () (cEOA aEOA))) ((Bank yBank = (new Bank -> value (0) ((balances : ())) (cBank aBank))) ((yBank -> deposit -> value (500) -> sender ((address (xEOA))) ()) (yBank -> withdraw -> value (0) -> sender ((address (xEOA))) ((amount : 100)))))) (()) (())
              ((contract EOC {(EOC () {}) (unit fb () {return u})})
               (contract Bank {
                               ((mapping (address => unit)) balances)
                               (Bank (((mapping (address => unit)) balances)) {(this -> balances = balances)})
                               (unit deposit () {return (this -> balances = ((this -> balances)[(msg -> sender) -> (((this -> balances)[(msg -> sender)]) + (msg -> value))]))})
                               (unit withdraw ((uint amount)) {return (if (((this -> balances)[(msg -> sender)]) >= amount) then ((this -> balances = ((this -> balances)[(msg -> sender) -> (((this -> balances)[(msg -> sender)]) - amount)])) ((msg -> sender) -> transfer (amount))) else u)})})
               
              ))))|#





#|(traces s->ßs (term ( ((EOC xEOA = (new EOC -> value (1000) () (1 1))) ((Bank yBank = (new Bank -> value (0) ((balances : ())) (2 2))) ((yBank -> deposit -> value (500) -> sender ((address (xEOA))) ()) (yBank -> withdraw -> value (0) -> sender ((address (xEOA))) ((amount : 100)))))) (()) (())
              ((contract EOC {(EOC () {}) (unit fb () {return u})})
               (contract Bank {
                               ((mapping (address => unit)) balances)
                               (Bank (((mapping (address => unit)) balances)) {(this -> balances = balances)})
                               (unit deposit () {return (this -> balances = ((this -> balances)[(msg -> sender) -> (((this -> balances)[(msg -> sender)]) + (msg -> value))]))})
                               (unit withdraw ((uint amount)) {return (if (((this -> balances)[(msg -> sender)]) >= amount) then ((this -> balances = ((this -> balances)[(msg -> sender) -> (((this -> balances)[(msg -> sender)]) - amount)])) ((msg -> sender) -> transfer (amount))) else u)})})
               
              ))))|#

#|(traces s->ßs (term ( ((EOC xEOA = (new EOC -> value (0) () (1 1))) ((Applier yApp = (new Applier -> value (0) ((state : 10)) (2 2))) ((Test zTest = (new Test -> value (0) ((app : yApp)) (3 3))) (zTest -> f1 -> value (0) -> sender ((address (xEOA))) ()) ))) (()) (())
              ((contract EOC {(EOC () {}) (unit fb () {return u})})
               (contract Applier {(uint state)
                                  (Applier ((uint state)) {(this -> state = state)})
                                  (unit apply (((uint -> uint) f)) {return (f -> value (0) ((n : (this -> state))))})})
               (contract Test {(Applier app)
                               (Test ((Applier app)) {(this -> app = app)})
                               (unit f1 () {return ((this -> app) -> apply -> value (0) ((f : (this -> square))))})
                               (unit square ((uint n)) {return (n * n)})})
              ))))|#

#|(traces s->ßs (term ( ((EOC xDoctor = (new EOC -> value (0) () (1 1))) ((EOC wHumanDonor = (new EOC -> value (0) () (2 2))) ((BloodBank yBank = (new BloodBank -> value (0) ((healthy : ()) (doctor : (address (xDoctor))) (blood : 0)) (3 3))) ((Donor zDonor = (new Donor -> value (0) ((blood : 5000) (bank : (address (yBank)))) (4 4))) ((yBank -> setHealth -> value (0) -> sender ((address (xDoctor))) ((donor : (address (zDonor))) (isHealthy : true))) (zDonor -> donate -> value (0) -> sender ((address (wHumanDonor))) ((amount : 500)) )))))) (()) (())
              ((contract EOC {(EOC () {}) (unit fb () {return u})})
              (contract BloodBank {
                                   ((mapping (address => bool)) healthy)
                                   (address doctor)
                                   (uint blood)
                                   (BloodBank (((mapping (address => bool)) healthy) (address doctor) (uint blood)) {(this -> healthy = healthy) (this -> doctor = doctor) (this -> blood = blood)})
                                   (unit setHealth ((address donor) (bool isHealthy)) {return (if ((msg -> sender) == (this -> doctor)) then (this -> healthy = ((this -> healthy) [donor -> isHealthy])) else revert)})
                                   (bool donate ((uint amount)) {return ((uint donorBlood = ((msg -> sender) -> getBlood -> value (0) ())) (if (((this -> healthy)[(msg -> sender)]) && ((donorBlood > 3000) && ((donorBlood - amount) > 0))) then ((this -> blood = ((this -> blood) + amount)) true) else false))})
                                   (uint getBlood () {return (this -> blood)})})
              (contract Donor {
                               (uint blood)
                               (address bank)
                               (Donor ((uint blood) (address bank)) {(this -> blood = blood) (this -> bank = bank)})
                               (unit donate ((uint amount)) {return (if ((this -> bank) -> donate -> value (0) ((amount : amount))) then ((this -> blood = ((this -> blood) - amount)) u) else u)})
                               (uint getBlood () {return (this -> blood)})})))))|#


#|(traces s->ßs (term ( ((EOC xEOA = (new EOC -> value (0) () (cEOA aEOA))) ((Applier yApp = (new Applier -> value (0) ((state : 10)) (cApp aApp))) ((Test zTest = (new Test -> value (0) ((app : yApp)) (cTest aTest))) (zTest -> f1 -> value (0) -> sender ((address (xEOA))) ()) ))) (()) (())
              ((contract EOC {(EOC () {}) (unit fb () {return u})})
               (contract Applier {(uint state)
                                  (Applier ((uint state)) {(this -> state = state)})
                                  (unit apply (((uint -> uint) f)) {return (f -> value (0) ((n : (this -> state))))})})
               (contract Test {(Applier app)
                               (Test ((Applier app)) {(this -> app = app)})
                               (unit f1 () {return ((this -> app) -> apply -> value (0) ((f : (this -> square))))})
                               (unit square ((uint n)) {return (n * n)})})
              ))))

(traces s->ßs (term ( ((EOC xDoctor = (new EOC -> value (0) () (cDoctor aDoctor))) ((EOC wHumanDonor = (new EOC -> value (0) () (cHumanDonor aHumanDonor))) ((BloodBank yBank = (new BloodBank -> value (0) ((healthy : ()) (doctor : (address (xDoctor))) (blood : 0)) (cBank aBank))) ((Donor zDonor = (new Donor -> value (0) ((blood : 5000) (bank : (address (yBank)))) (cDonor aDonor))) ((yBank -> setHealth -> value (0) -> sender ((address (xDoctor))) ((donor : (address (zDonor))) (isHealthy : true))) (zDonor -> donate -> value (0) -> sender ((address (wHumanDonor))) ((amount : 500)) )))))) (()) (())
              ((contract EOC {(EOC () {}) (unit fb () {return u})})
              (contract BloodBank {
                                   ((mapping (address => bool)) healthy)
                                   (address doctor)
                                   (uint blood)
                                   (BloodBank (((mapping (address => bool)) healthy) (address doctor) (uint blood)) {(this -> healthy = healthy) (this -> doctor = doctor) (this -> blood = blood)})
                                   (unit setHealth ((address donor) (bool isHealthy)) {return (if ((msg -> sender) == (this -> doctor)) then (this -> healthy = ((this -> healthy) [donor -> isHealthy])) else revert)})
                                   (bool donate ((uint amount)) {return ((uint donorBlood = ((msg -> sender) -> getBlood -> value (0) ())) (if (((this -> healthy)[(msg -> sender)]) && ((donorBlood > 3000) && ((donorBlood - amount) > 0))) then ((this -> blood = ((this -> blood) + amount)) true) else false))})
                                   (uint getBlood () {return (this -> blood)})})
              (contract Donor {
                               (uint blood)
                               (address bank)
                               (Donor ((uint blood) (address bank)) {(this -> blood = blood) (this -> bank = bank)})
                               (unit donate ((uint amount)) {return (if ((this -> bank) -> donate -> value (0) ((amount : amount))) then ((this -> blood = ((this -> blood) - amount)) u) else u)})
                               (uint getBlood () {return (this -> blood)})})))))

(traces s->ßs (term ( ((EOC xEOA = (new EOC -> value (1000) () (cEOA aEOA))) ((Bank yBank = (new Bank -> value (0) ((balances : ())) (cBank aBank))) ((yBank -> deposit -> value (500) -> sender ((address (xEOA))) ()) (yBank -> withdraw -> value (0) -> sender ((address (xEOA))) ((amount : 100)))))) (()) (())
              ((contract EOC {(EOC () {}) (unit fb () {return u})})
               (contract Bank {
                               ((mapping (address => unit)) balances)
                               (Bank (((mapping (address => unit)) balances)) {(this -> balances = balances)})
                               (unit deposit () {return (this -> balances = ((this -> balances)[(msg -> sender) -> (((this -> balances)[(msg -> sender)]) + (msg -> value))]))})
                               (unit withdraw ((uint amount)) {return (if (((this -> balances)[(msg -> sender)]) >= amount) then ((this -> balances = ((this -> balances)[(msg -> sender) -> (((this -> balances)[(msg -> sender)]) - amount)])) ((msg -> sender) -> transfer (amount))) else u)})})
               
              ))))
|#

#| NEW TESTS

(traces s->ßs (term ( ((EOC xEOA = (new EOC -> value (1000) () (cEOA aEOA))) ((Bank yBank = (new Bank -> value (0) ((balances : ())) (cBank aBank))) ((yBank -> deposit -> value (500) -> sender ((address (xEOA))) ()) (yBank -> getBalance -> value (0) -> sender ((address (xEOA))) ())))) (()) (())
              ((contract EOC {(EOC () {}) (unit fb () {return u})})
               (contract Bank {
                               ((mapping (address => unit)) balances)
                               (Bank (((mapping (address => unit)) balances)) {(this -> balances = balances)})
                               (unit deposit () {return (this -> balances = ((this -> balances)[(msg -> sender) -> (((this -> balances)[(msg -> sender)]) + (msg -> value))]))})
                               (unit withdraw ((uint amount)) {return (if (((this -> balances)[(msg -> sender)]) >= amount) then ((this -> balances = ((this -> balances)[(msg -> sender) -> (((this -> balances)[(msg -> sender)]) - amount)])) ((msg -> sender) -> transfer (amount))) else u)})
                               (uint getBalance() {return ((this -> balances)[(msg -> sender)])})})
               
              ))))
(traces s->ßs (term ( ((EOC xEOA = (new EOC -> value (1000) () (cEOA aEOA))) ((Bank yBank = (new Bank -> value (0) ((balances : ())) (cBank aBank))) ((yBank -> deposit -> value (500) -> sender ((address (xEOA))) ()) (yBank -> transfer -> value (0) -> sender ((address (xEOA))) ((to : (address (yBank))) (amount : 87)))))) (()) (())
              ((contract EOC {(EOC () {}) (unit fb () {return u})})
               (contract Bank {
                               ((mapping (address => unit)) balances)
                               (Bank (((mapping (address => unit)) balances)) {(this -> balances = balances)})
                               (unit deposit () {return (this -> balances = ((this -> balances)[(msg -> sender) -> (((this -> balances)[(msg -> sender)]) + (msg -> value))]))})
                               (unit withdraw ((uint amount)) {return (if (((this -> balances)[(msg -> sender)]) >= amount) then ((this -> balances = ((this -> balances)[(msg -> sender) -> (((this -> balances)[(msg -> sender)]) - amount)])) ((msg -> sender) -> transfer (amount))) else u)})
                               (uint getBalance() {return ((this -> balances)[(msg -> sender)])})
                               (unit transfer ((address to) (uint amount)) {return (if (((this -> balances)[(msg -> sender)]) >= amount) then ((this -> balances = ((this -> balances)[(msg -> sender) -> (((this -> balances)[(msg -> sender)]) - amount)])) (this -> balances = ((this -> balances)[to -> (((this -> balances)[to]) + amount)]))) else u)})})
               
              ))))

(traces s->ßs (term ( ((Owner o = (new Owner -> value (0) () (cOwner aOwner)))
                         ((Auction x = (new Auction -> value (0) ((pendingReturns : ()) (auctionEnded : false) (highestBid : 0) (highestBidder : a) (owner : aOwner))  (cAuction aAuction)) )
                          ((x -> init -> value (0) -> sender(aOwner) ())
                           ((Client c1 = (new Client -> value (500) ((balance : 500)) (cC1 aC1)))
                            ((x -> bid -> value (3) -> sender((address(c1))) ((bid : 9)))
                             ((Client c2 = (new Client -> value (560) ((balance : 800)) (cC2 aC2)))
                              ((x -> bid -> value (0) -> sender ((address(c2))) ((bid : 19)))
                               ((x -> withdraw -> value (0) -> sender ((address(c1))) ())
                                ((x -> end -> value (0) -> sender(aOwner) ())
                                 (x -> win -> value (0) -> sender(aC2) ())))) ) )))))  (()) (())
              ((contract Auction {
                                  ((mapping (address => unit)) pendingReturns)
                                  (bool auctionEnded)
                                  (uint highestBid)
                                  (address highestBidder)
                                  (address owner)
                                  (Auction (((mapping (uint => unit)) pendingReturns) (bool auctionEnded) (uint highestBid) (address highestBidder) (address owner)) {
                                     (this -> pendingReturns = pendingReturns)
                                     (this -> auctionEnded = auctionEnded)
                                     (this -> highestBid = highestBid)
                                     (this -> highestBidder = highestBidder)
                                     (this -> owner = owner)
                                    })
                                  (unit init () {return (if (((msg -> sender) == (this -> owner) ) && ((this -> auctionEnded) == true)) then (this -> auctionEnded = false) else u)})
                                  (unit end () {return (if (((msg -> sender) == (this -> owner) ) && ((this -> auctionEnded) == false)) then (this -> auctionEnded = true) else u)})
                                  (unit bid ((uint bid)) {
                                     return (if ((msg -> sender) == (this -> owner) )  then u
                                      else (if ((this -> auctionEnded) == true) then u
                                       else (if ((this -> highestBidder) == (msg -> sender)) then u
                                        else (if (((this -> pendingReturns)[(msg -> sender)]) > 0) then u else (if (bid < 0) then u
                                         else (if (bid <= (this -> highestBid)) then u
                                          else ((this -> pendingReturns = ((this -> pendingReturns)[(msg -> sender) -> bid])) ((this -> highestBidder = (msg -> sender)) (this -> highestBid = bid)))))))))})
                                  (unit withdraw () {
                                      return (if ((msg -> sender) == (this -> owner) ) then u
                                       else (if ((this -> highestBidder) == (msg -> sender)) then u
                                        else (if (((this -> pendingReturns)[(msg -> sender)]) == 0) then u
                                         else (this -> pendingReturns = ((this -> pendingReturns)[(msg -> sender) -> 0])))))})
                                  (unit win () {
                                       return (if ((msg -> sender) == (this -> owner) ) then u
                                        else (if ((this -> auctionEnded) == false) then u
                                         else (if (((this -> pendingReturns)[(msg -> sender)]) == 0) then u
                                          else (if ((this -> highestBidder) == (msg -> sender)) then
                                                   (((Client ((msg -> sender))) -> withdraw -> value(0) -> sender((msg -> sender)) ((amount : ((this -> pendingReturns)[(msg -> sender)])))) (this -> pendingReturns = ((this -> pendingReturns)[(msg -> sender) -> 0])) )
                                                   else u))))
                                       })
                                  
                                  })
               (contract Owner {(Owner () {})})
               (contract Client {
                                 (uint balance)
                                 (Client ((uint balance)) {(this -> balance = balance)})
                                 (uint getBalance () {return (this -> balance)})
                                 (unit withdraw ((uint amount)) {return (this -> balance = ((this -> balance) - amount))})})
              ))))

(traces s->ßs (term ( ((BlockKing bk = (new BlockKing -> value (0) ((warrior : a) (warriorGold : 8) (myid : 9) (king : aBK)) (cBK aBK))) ((EOC x = (new EOC -> value (6) () (cBx aBx))) ((bk -> enter -> value (2) -> sender (aBx) ()) ((EOC y = (new EOC -> value (4) () (cBy aBy))) ((bk -> enter -> value (3) -> sender (aBy) ()) ((bk -> process_payment -> value (0) -> sender (aBK) ()) ()))))))  (()) (())
              ((contract BlockKing {
                     (address warrior)
                     (uint warriorGold)
                     (uint myid)
                     (address king)
                     (BlockKing ((address warrior) (uint warriorGold) (uint myid) (address king)) {(this -> warrior = warrior) (this -> warriorGold = warriorGold) (this -> myid = myid) (this -> king = king)})
                     (uint enter () {return ((this -> warrior = (msg -> sender)) (this -> warriorGold = (msg -> value)))})
                     (uint process_payment () {return (this -> king = (this -> warrior))})})
               (contract EOC {(EOC () {}) (unit fb () {return u})})
              ))))


(traces s->ßs (term ( ((EtherStore es = (new EtherStore -> value (0) ((balances : ()) (Owner : aES) (Creator : aES) (price : 9)) (cBK aBK))) ((EOC alice = (new EOC -> value (8) () (cAlice aAlice))) ((EOC bob = (new EOC -> value (8) () (cBob aBob))) ((es -> foo -> value (0) -> sender (aAlice) ((newOwner : aAlice))) ((es -> bar -> value (7) -> sender (aBob) ()) ())))))  (()) (())
              ((contract EtherStore {
                     ((mapping (address => uint)) balances)
                     (address Owner)
                     (address Creator)
                     (uint price)
                     (EtherStore (((mapping (address => uint)) balances) (address Owner) (address Creator) (uint price)) {(this -> balances = balances) (this -> Owner = Owner) (this -> Creator = Creator) (this -> price = price)})
                     (unit foo ((address newOwner)) {return ((this -> Owner = newOwner) u)})
                     (unit bar () {return ((this -> price = (msg -> value)) ((this -> balances = ((this -> balances)[(msg -> sender) -> (((this -> balances)[(msg -> sender)]) + (this -> price))])) (((this -> Owner) -> transfer ((this -> price))) u)))})})
               (contract EOC {(EOC () {}) (unit fb () {return u})})
              ))))

(traces s->ßs (term ( ((Counter -> init () -> aCounter) (aCounter -> set ((value : 3)) -> sender (aCounter)) (aCounter -> get () -> sender (aCounter)) ) () () () (
           (contract Counter (canSet cannotSet)
                     { (var x : Int = 0) }
                     (Counter :: (any_caller) {
                        (public init () {(become canSet)})
                        (public func get () -> Int {return (self -> x)})
                        })
                     (Counter @ (canSet) :: (any_caller) {
                        (public func set ((value : Int)) -> Int {(become cannotSet) (self -> x = value) (become canSet) return (self -> x)})
                        })
                     )
           (contract EOC () {} (EOC :: (any_caller) {(public init () {})}))
           ))))

(traces s->ßs (term ( ((EOC xEOA = (new EOC -> value (1000) () (cEOA aEOA))) ((Counter yCounter = (new Counter -> value (0) ((x : 0)) (cCounter aCounter))) ((yCounter -> set -> value (500) -> sender ((address (xEOA))) ((x : 3))) (yCounter -> get -> value (0) -> sender ((address (xEOA))) ())))) (()) (())
              ((contract EOC {(EOC () {}) (unit fb () {return u})})
               (contract Counter {
                                  (uint x)
                                  (Counter ((uint x)) {(this -> x = x)})
                                  (uint get () {return (this -> x)})
                                  (uint set ((uint x)) {return (this -> x = x)})})
              ))))

(traces s->ßs (term ( ((BlockKing bk = (new BlockKing -> value (0) ((warrior : aBK) (warriorGold : 8) (myid : 9) (king : aBK)) (cBK aBK))) ((EOC x = (new EOC -> value (6) () (cBx aBx))) ((EOC y = (new EOC -> value (4) () (cBy aBy))) ((bk -> enter -> value (2) -> sender (aBx) ()) ((bk -> enter -> value (3) -> sender (aBy) ()) ((bk -> process_payment -> value (0) -> sender (aBK) ()) ((bk -> process_payment -> value (0) -> sender (aBK) ()) ())))))))  (()) (())
              ((contract BlockKing {
                     (address warrior)
                     (uint warriorGold)
                     (uint myid)
                     (address king)
                     (BlockKing ((address warrior) (uint warriorGold) (uint myid) (address king)) {(this -> warrior = warrior) (this -> warriorGold = warriorGold) (this -> myid = myid) (this -> king = king)})
                     (uint enter () {return ((this -> warrior = (msg -> sender)) (this -> warriorGold = (msg -> value)))})
                     (uint process_payment () {return (this -> king = (this -> warrior))})})
               (contract EOC {(EOC () {}) (unit fb () {return u})})
              ))))
 |#


(define-extended-language FS-t FS
  (Γ-v ::= (x : T)
     )
  (Γ ::= (Γ-v ...)))

(define-judgment-form
  FS-t
  #:mode (⊢wfσ I I I)
  #:contract (⊢wfσ CT Γ env-σ)
  [(⊢wfσ CT Γ (σ-v ...))
   (⊢wfß CT Γ (ß-v ...))
   (⊢ CT Γ σ address CT Γ)
   ---------------
   (⊢wfσ CT Γ (ß-v ... σ-v ... (σ)))]
  [
   ---------------
   (⊢wfσ CT Γ (()))]
  )

(define-judgment-form
  FS-t
  #:mode (⊢wfß I I I)
  #:contract (⊢wfß CT Γ env-ß)
  [(⊢wfß CT Γ ((ß ...)))
   (⊢ CT Γ c C CT Γ)
   (⊢ CT Γ a address CT Γ)
   (⊢ CT Γ n uint CT Γ)
   ----------------
   (⊢wfß CT Γ ((ß ... ((c a) -> (C (s : v) ... n)))))]
  [(⊢wfß CT Γ ((ß ...)))
   (⊢ CT Γ x T CT Γ)
   (⊢ CT Γ vv T CT Γ)
   ----------------
   (⊢wfß CT Γ ((ß ... (x -> vv))))]
  [----------------
   (⊢wfß CT Γ (()))]
  )

(define-judgment-form
  FS-t
  #:mode (⊢wf I I I I I O)
  #:contract (⊢wf CT env-ß env-σ Γ e T)
  [(⊢wfß CT Γ env-ß)
   (⊢wfσ CT Γ env-σ)
   (⊢ CT Γ e T CT Γ_1)
   ---------------
   (⊢wf CT env-ß env-σ Γ e T)]

  )

;Typing rules
(define-judgment-form
  FS-t
  #:mode (⊢ I I I O O O)
  #:contract (⊢ CT Γ e T CT Γ)
  ;Axioms
  ;T-TRUE
  [------------------
   (⊢ CT Γ true bool CT Γ)]
  ;T-FALSE
  [------------------
   (⊢ CT Γ false bool CT Γ)]
  ;T-UNIT
  [--------------
   (⊢ CT Γ u unit CT Γ)]
  ;T-NAT
  [--------------
   (⊢ CT Γ n uint CT Γ)]
  ;T-ADDRESS VAR REF
  [--------------
   (⊢ CT Γ x (find-type Γ x) CT Γ)]
  ;T-REVERT
  ;[--------------
   ;(⊢ env-ß env-σ CT Γ revert T env-ß env-σ CT Γ)]
  ;Standard rules
  ;T-ADDR
  [(⊢ ((contract C_1 {(T_1 x_11) ... K_1 F_1 ...}) ... (contract C {(T_0 x_01) ... (C ((T x) ...) {(this -> s = x) ...}) F ...}) (contract C_2 {(T_2 x_21) ... K_2 F_2 ...}) ...)
       Γ e C ((contract C_1 {(T_1 x_11) ... K_1 F_1 ...}) ... (contract C {(T_0 x_01) ... (C ((T x) ...) {(this -> s = x) ...}) F ...}) (contract C_2 {(T_2 x_21) ... K_2 F_2 ...}) ...)
       Γ)
    --------------
   (⊢ ((contract C_1 {(T_1 x_11) ... K_1 F_1 ...}) ... (contract C {(T_0 x_01) ... (C ((T x) ...) {(this -> s = x) ...}) F ...}) (contract C_2 {(T_2 x_21) ... K_2 F_2 ...}) ...)
      Γ (address(e)) address
      ((contract C_1 {(T_1 x_11) ... K_1 F_1 ...}) ... (contract C {(T_0 x_01) ... (C ((T x) ...) {(this -> s = x) ...}) F ...}) (contract C_2 {(T_2 x_21) ... K_2 F_2 ...}) ...)
      Γ)]
  ;T-RETURN
  [(⊢ CT Γ e T CT Γ)
   --------------
   (⊢ CT Γ (return e) T CT Γ)]
  ;T-SEQ
  [(⊢ CT Γ e_1 T_1 CT Γ_1)
   (⊢ CT Γ_1 e_2 T_2 CT Γ_2)
   --------------
   (⊢ CT Γ (e_1 e_2) T_2 CT Γ_2)]
  ;T-DECL
  [(⊢ CT Γ e T CT Γ_1)
   --------------
   (⊢ CT Γ (T x = e) T CT  (assign-typing CT Γ x T) )]
  ;T-IF
  [(⊢ CT Γ e_1 bool CT Γ_1)
   (⊢ CT Γ e_2 T CT Γ_2)
   (⊢ CT Γ e_3 T CT Γ_3)
   --------------
   (⊢ CT Γ (if e_1 then e_2 else e_3) T CT (union Γ_2 Γ_3))]
  ;T-ASS
  [(⊢ CT Γ x T CT Γ)
   (⊢ CT Γ e T CT Γ)
   --------------
   (⊢ CT Γ (x = e) T CT Γ)]
  ;Mapping
  ;T-MAPPING
  [(⊢ CT Γ ((v_k1 v_v2) ... ) (mapping (T_1 => T_2)) CT Γ_1)
   (⊢ CT Γ_1 v_k T_1 CT Γ_2)
   (⊢ CT Γ_2 v_v T_2 CT Γ_3)
   --------------
   (⊢ CT Γ ( (v_k1 v_v2) ... (v_k v_v) ) (mapping (T_1 => T_2)) CT Γ_3)]
  [(⊢ CT Γ v_k T_1 CT Γ_2)
   (⊢ CT Γ_2 v_v T_2 CT Γ_3)
   --------------
   (⊢ CT Γ ((v_k v_v)) (mapping (T_1 => T_2)) CT Γ_3)]
  ;T-MAPPASS
  [(⊢ CT Γ e_1 (mapping (T_1 => T_2)) CT Γ_1)
   (⊢ CT Γ_1 e_2 T_1 CT Γ_2)
   (⊢ CT Γ_1 e_3 T_2 CT Γ_3)
   --------------
   (⊢ CT Γ (e_1[e_2 -> e_3]) (mapping (T_1 => T_2)) CT Γ_3)]
  ;T-MAPPSEL
  [(⊢ CT Γ e_1 (mapping(T_1 => T_2)) CT Γ_1)
   (⊢ CT Γ_1 e_2 T_2 CT Γ_2)
   --------------
   (⊢ CT Γ (e_1[e_2]) T_2 CT Γ_2)]
  ;Contract instantiation and access
  ;T-STATESEL
  [(⊢ (SC_1 ... (contract C {(T_0 x_01) ... (T s) (T_02 x_02) ... K F ...}) SC_2 ...) Γ e C (SC_1 ... (contract C {(T_0 x_01) ... (T s) (T_02 x_02) ... K F ...}) SC_2 ...) Γ)
   --------------
   (⊢ (SC_1 ... (contract C {(T_0 x_01) ... (T s) (T_02 x_02) ... K F ...}) SC_2 ...) Γ (e -> s) T (SC_1 ... (contract C {(T_0 x_01) ... (T s) (T_02 x_02) ... K F ...}) SC_2 ...) Γ)]
  ;T-STATEASS
  [(⊢ CT Γ (e_1 -> s) T CT Γ)
   (⊢ CT Γ e_2 T CT Γ)
   --------------
   (⊢ CT Γ (e_1 -> s = e_2) T CT Γ)]
  ;T-NEW
  [(⊢ (SC_1 ... (contract C {(T_0 x_01) ... (T s) (T_02 x_02) ... K F ...}) SC_2 ...) Γ e_1 uint (SC_1 ... (contract C {(T_0 x_01) ... (T s) (T_02 x_02) ... K F ...}) SC_2 ...) Γ_2)
   ;(⊢ env-ß env-σ CT Γ_1 (e_2 ...) (T ...) env-ß env-σ CT Γ_2)
   (⊢ (SC_1 ... (contract C {(T_0 x_01) ... (T s) (T_02 x_02) ... K F ...}) SC_2 ...) Γ_2 e_3 C (SC_1 ... (contract C {(T_0 x_01) ... (T s) (T_02 x_02) ... K F ...}) SC_2 ...) Γ_3)
   (⊢ (SC_1 ... (contract C {(T_0 x_01) ... (T s) (T_02 x_02) ... K F ...}) SC_2 ...) Γ_3 e_4 address (SC_1 ... (contract C {(T_0 x_01) ... (T s) (T_02 x_02) ... K F ...}) SC_2 ...) Γ_4)
   --------------
   (⊢ (SC_1 ... (contract C {(T_0 x_01) ... (T s) (T_02 x_02) ... K F ...}) SC_2 ...) Γ (new C -> value (e_1) (( x : e_2 ) ...) (e_3 e_4)) C (SC_1 ... (contract C {(T_0 x_01) ... (T s) (T_02 x_02) ... K F ...}) SC_2 ...) Γ)]
  ;Functions
  ;T-FUN
  [(⊢ CT Γ c C CT Γ_1)
   --------------
   (⊢ CT Γ (c -> f) (ftype CT C f) CT Γ_1)]
  ;T-CALL
  [(⊢ CT Γ e_1 C CT Γ)
   (⊢ CT Γ e_2 uint CT Γ)
   ;(⊢ CT Γ (e_3 ...) (ftype CT C f) CT Γ)
   --------------
   (⊢ CT Γ (e_1 -> f -> value (e_2) ((x : e_3) ...)) (getftype2 (ftype CT C f)) CT Γ)]
  ;T-CALLTOPLEVEL
  [(⊢ CT Γ e_3 address CT Γ)
   (⊢ CT Γ (e_1 -> f -> value (e_2) ((x : e_4) ...)) T_2 CT Γ)
   -------------
   (⊢ CT Γ (e_1 -> f -> value (e_2) -> sender (e_3) ((x : e_4) ...)) T_2 CT Γ)]
  ;Money transfer
  ;T-TRANSFER
  [(⊢ CT Γ e_1 address CT Γ)
   (⊢ CT Γ e_2 uint CT Γ)
   -------------
   (⊢ CT Γ (e_1 -> transfer (e_2)) unit CT Γ)
   ]



  ;;;;;;;;
  ;[(⊢ CT Γ e_1 T CT Γ_1)
   ;(⊢ CT Γ_1 (e_2 ...) T CT Γ_2)
   ;--------------
   ;(⊢ CT Γ (e_1 e_2 ...) T CT Γ_2)]
  [--------------
   (⊢ CT Γ () unit CT Γ)]
  ;[(⊢ CT Γ e_1 T_1 CT Γ)
   ;(⊢ CT Γ (e_2 ...) (T_2 ... -> T) CT Γ)
   ;--------------
   ;(⊢ CT Γ (e_1 e_2 ...) (T_1 T_2 ... -> T) CT Γ)]
  ;
  [(⊢ CT Γ e_1 T_1 CT Γ)
   --------------
   (⊢ CT Γ (e_1) (T_1 -> T_1) CT Γ)]
  )


(define-metafunction FS-t
  assign-typing : CT Γ any T -> Γ
  [(assign-typing CT ((x_1 : T_1) ...) a address)
   ((x_1 : T_1) ... (a : address))]
  [(assign-typing ((contract C_1 {(T_1 x_11) ... K_1 F_1 ...}) ... (contract C {(T_0 x_01) ... (C ((T x) ...) {(this -> s = x) ...}) F ...}) (contract C_2 {(T_2 x_21) ... K_2 F_2 ...}) ...) ((x_t : T_t) ...) c C)
   ((x_t : T_t) ... (c : C))]
  [(assign-typing CT ((x_1 : T_1) ...) x T)
   ((x_1 : T_1) ... (x : T))]
  )

(define-metafunction FS-t
  find-type : Γ x -> T
  [(find-type ((x_1 : T_1) ... (x : T) (x_2 : T_2) ...) x)
   T])

(define-metafunction FS-t
  union : Γ Γ -> Γ
  [(union ((x_1 : T_1) ...) ((x_2 : T_2) ...))
   ((x_1 : T_1) ... (x_2 : T_2) ...)])

(define-metafunction FS-t
  ftype : CT C f -> (T ... -> T)
  [(ftype (SC_1 ... (contract C {(T_s s) ... K F_01 ... (T f ((T_00 x_00) ... ) {return e}) F_02 ...}) SC_2 ...) C f)
   (T_00 ... -> T)])

#|(define-metafunction FS-t
  ftype1 : CT C f -> (T ...)
  [(ftype1 (SC_1 ... (contract C {(T_s s) ... K F_01 ... (T f ((T_00 x_00) ... ) {return e}) F_02 ...}) SC_2 ...) C f)
   (T_00 ...)])

(define-metafunction FS-t
  ftype2 : CT C f -> T
  [(ftype2 (SC_1 ... (contract C {(T_s s) ... K F_01 ... (T f ((T_00 x_00) ... ) {return e}) F_02 ...}) SC_2 ...) C f)
   T])|#

(define-metafunction FS-t
  getftype2 : (T ... -> T) -> T
  [(getftype2 (T_1 ... -> T))
   T])

;(judgment-holds (⊢ () true _ _))
;(judgment-holds (⊢ () true _ bool))
;(judgment-holds (⊢ () () () () 1 uint _ _ _ _))
;(judgment-holds (⊢ () () ((contract EOC {(EOC () {}) (unit fb () {return u})})) () 1 uint _ _ ((contract EOC {(EOC () {}) (unit fb () {return u})})) _))
;(judgment-holds (⊢ ((contract EOC {(EOC () {}) (unit fb () {return u})})) () cEOA ((contract EOC {(EOC () {}) (unit fb () {return u})})) () EOC))
;(judgment-holds (⊢ ((contract EOC {(EOC () {}) (unit fb () {return u})})) () cEOA ((contract EOC {(EOC () {}) (unit fb () {return u})})) ((cEOA : EOC)) EOC))
;(judgment-holds (⊢ () () () ((x : uint)) x uint _ _ _ _))
;(judgment-holds (⊢ () () ((contract EOC {(EOC () {}) (unit fb () {return u})})) ((x : EOC)) (address(x)) address _ _ _ _))
;(judgment-holds (⊢ () () ((contract EOC {(EOC () {}) (unit fb () {return u})})) ((x : A)) (return 1) uint _ _ _ _))
;(judgment-holds (⊢ () () ((contract EOC {(EOC () {}) (unit fb () {return u})})) ((x : EOC)) (if false then 1 else 2) uint _ _ _ _))
;(judgment-holds (⊢ () () ((contract EOC {(EOC () {}) (unit fb () {return u})})) ((x : uint)) (x = 3) uint _ _ _ _))
;(judgment-holds (⊢ () () ((contract EOC {(uint a) (EOC () {}) (unit fb () {return u})})) ((x : EOC)) ((3 5)) (mapping (uint => uint)) _ _ _ _))
;(judgment-holds (⊢ () () ((contract EOC {(uint a) (EOC () {}) (unit fb () {return u})})) ((x : EOC)) ((true 5)) (mapping (bool => uint)) _ _ _ _))
;(judgment-holds (⊢ () () ((contract EOC {(uint a) (EOC () {}) (unit fb () {return u})})) ((x : EOC)) (x -> a) uint _ _ _ _))
;(judgment-holds (⊢ () () ((contract EOC {(uint a) (EOC () {}) (unit fb () {return u})})) ((x : EOC)) (x -> a = 7) uint _ _ _ _))
;(judgment-holds (⊢ () () ((contract EOC {(uint a) (EOC () {}) (unit fb () {return u})})) ((x : EOC)) (new EOC -> value (9) () (cEOC aEOC)) EOC _ _ _ _))
;(judgment-holds (⊢ () () ((contract EOC {(uint a) (EOC () {}) (unit fb () {return u})})) ((cEOC : EOC) (aEOC : address)) (cEOC -> fb) unit _ _ _ _))
;(judgment-holds (⊢ () () ((contract EOC {(uint a) (EOC () {}) (unit fb () {return u})})) ((cEOC : EOC) (aEOC : address)) (cEOC -> fb -> value (4) ()) unit _ _ _ _))
;(judgment-holds (⊢ () () ((contract EOC {(uint a) (EOC () {}) (unit fb () {return u})})) ((cEOC : EOC) (cSender : EOC)) (cEOC -> fb -> value (4) -> sender(cSender) ()) unit _ _ _ _))
;(judgment-holds (⊢ () () ((contract EOC {(uint a) (EOC () {}) (unit fb () {return u})})) ((cEOC : EOC) (aEOC : address)) (aEOC -> transfer (9)) unit _ _ _ _))
;(judgment-holds (⊢wf ((contract EOC {(EOC () {}) (unit fb () {return u})})) ((aEOA : address)) ((aEOA))))
;(judgment-holds (⊢wfß ((contract EOC {(EOC () {}) (unit fb () {return u})})) ((x : uint)) (((x -> 3)))))
;(judgment-holds (⊢wfß ((contract EOC {(EOC () {}) (unit fb () {return u})})) ((cEOA : EOA) (aEOA : address)) ((((cEOA aEOA) -> (EOA 4))))))
;(judgment-holds (⊢wfσ ((contract EOC {(EOC () {}) (unit fb () {return u})})) ((cEOA : EOA) (aEOA : address)) ((((cEOA aEOA) -> (EOA 4))) (aEOA))))
#|(judgment-holds (⊢wf ((contract EOC {(EOC () {}) (unit fb () {return u})})
               (contract Bank {
                               ((mapping (address => unit)) balances)
                               (Bank (((mapping (address => unit)) balances)) {(this -> balances = balances)})
                               (unit deposit () {return (this -> balances = ((this -> balances)[(msg -> sender) -> (((this -> balances)[(msg -> sender)]) + (msg -> value))]))})
                               (unit withdraw ((uint amount)) {return (if (((this -> balances)[(msg -> sender)]) >= amount) then ((this -> balances = ((this -> balances)[(msg -> sender) -> (((this -> balances)[(msg -> sender)]) - amount)])) ((msg -> sender) -> transfer (amount))) else u)})})
               
              ) ((((cEOC aEOC) -> (EOC 4)) (xEOC -> cEOC))) ((((cEOC aEOC) -> (EOC 4)) (xEOC -> cEOC))) ((xEOC : EOC) (cEOC : EOC) (aEOC : address)) ((EOC xEOA = (new EOC -> value (1000) () (cEOA aEOA))) ((Bank yBank = (new Bank -> value (0) ((balances : ())) (cBank aBank))) ((yBank -> deposit -> value (500) -> sender ((address (xEOA))) ()) (yBank -> withdraw -> value (0) -> sender ((address (xEOA))) ((amount : 100)))))) _))
|#
#|(judgment-holds (⊢ ((contract EOC {(EOC () {}) (unit fb () {return u})})
               (contract Bank {
                               ((mapping (address => unit)) balances)
                               (Bank (((mapping (address => unit)) balances)) {(this -> balances = balances)})
                               (unit deposit () {return (this -> balances = ((this -> balances)[(msg -> sender) -> (((this -> balances)[(msg -> sender)]) + (msg -> value))]))})
                               (unit withdraw ((uint amount)) {return (if (((this -> balances)[(msg -> sender)]) >= amount) then ((this -> balances = ((this -> balances)[(msg -> sender) -> (((this -> balances)[(msg -> sender)]) - amount)])) ((msg -> sender) -> transfer (amount))) else u)})})
               
              ) ((xEOC : EOC) (cEOC : EOC) (aEOC : address)) (new EOC -> value (9) () (cEOC aEOC)) _ _ _))|#

;(judgment-holds (⊢wf ((contract EOC {(uint a) (EOC () {}) (unit fb () {return u})}))  ((((cEOC aEOC) -> (EOC 1000)))) ((((cEOC aEOC) -> (EOC 4))) (aEOC)) ((cEOC : EOC) (aEOC : address)) (EOC xEOA = (new EOC -> value (1000) () (cEOC aEOC))) _ ))
;(judgment-holds (⊢wf ((contract EOC {(uint a) (EOC () {}) (unit fb () {return u})}))  ((((cEOC aEOC) -> (EOC 1000)))) ((((cEOC aEOC) -> (EOC 4))) (aEOC)) ((cEOC : EOC) (aEOC : address)) (EOC xEOA = (new EOC -> value (1000) () (cEOC aEOC))) EOC ))

#|(judgment-holds (⊢wf ((contract EOC {(uint a) (EOC () {}) (unit fb () {return u})})
               (contract Bank {
                               ((mapping (address => unit)) balances)
                               (Bank (((mapping (address => unit)) balances)) {(this -> balances = balances)})
                               (unit deposit () {return (this -> balances = ((this -> balances)[(msg -> sender) -> (((this -> balances)[(msg -> sender)]) + (msg -> value))]))})
                               (unit withdraw ((uint amount)) {return (if (((this -> balances)[(msg -> sender)]) >= amount) then ((this -> balances = ((this -> balances)[(msg -> sender) -> (((this -> balances)[(msg -> sender)]) - amount)])) ((msg -> sender) -> transfer (amount))) else u)})})
               
              ) (()) (()) ((x : EOC) (cEOC : EOC) (aEOC : address)) (new EOC -> value (9) () (cEOC aEOC)) _ ))|#

#|(judgment-holds (⊢wf ((contract EOC {(uint a) (EOC () {}) (unit fb () {return u})})
               (contract Bank {
                               ((mapping (address => unit)) balances)
                               (Bank (((mapping (address => unit)) balances)) {(this -> balances = balances)})
                               (unit deposit () {return (this -> balances = ((this -> balances)[(msg -> sender) -> (((this -> balances)[(msg -> sender)]) + (msg -> value))]))})
                               (unit withdraw ((uint amount)) {return (if (((this -> balances)[(msg -> sender)]) >= amount) then ((this -> balances = ((this -> balances)[(msg -> sender) -> (((this -> balances)[(msg -> sender)]) - amount)])) ((msg -> sender) -> transfer (amount))) else u)})})
               
              ) (()) (()) ((x : EOC) (cEOC : EOC) (aEOC : address)) (EOC x = (new EOC -> value (9) () (cEOC aEOC))) _ ))|#

#|(judgment-holds (⊢wf ((contract EOC {(uint a) (EOC () {}) (unit fb () {return u})})
               (contract Bank {
                               ((mapping (address => unit)) balances)
                               (Bank (((mapping (address => unit)) balances)) {(this -> balances = balances)})
                               (unit deposit () {return (this -> balances = ((this -> balances)[(msg -> sender) -> (((this -> balances)[(msg -> sender)]) + (msg -> value))]))})
                               (unit withdraw ((uint amount)) {return (if (((this -> balances)[(msg -> sender)]) >= amount) then ((this -> balances = ((this -> balances)[(msg -> sender) -> (((this -> balances)[(msg -> sender)]) - amount)])) ((msg -> sender) -> transfer (amount))) else u)})})
               
              ) (()) (()) ((cEOC : EOC) (aEOC : address) (cBank : Bank) (aBank : address)) ((EOC x = (new EOC -> value (9) () (cEOC aEOC))) ((Bank y = (new Bank -> value (0) ((balances : ())) (cBank aBank))) (y -> deposit -> value (1) -> sender ((address (x))) ()))) _ ))|#



#|(judgment-holds (⊢wf ((contract Auction {
                                  ((mapping (address => unit)) pendingReturns)
                                  (bool auctionEnded)
                                  (uint highestBid)
                                  (address highestBidder)
                                  (address owner)
                                  (Auction (((mapping (uint => unit)) pendingReturns) (bool auctionEnded) (uint highestBid) (address highestBidder) (address owner)) {
                                     (this -> pendingReturns = pendingReturns)
                                     (this -> auctionEnded = auctionEnded)
                                     (this -> highestBid = highestBid)
                                     (this -> highestBidder = highestBidder)
                                     (this -> owner = owner)
                                    })
                                  (unit init () {return (if (((msg -> sender) == (this -> owner) ) && ((this -> auctionEnded) == true)) then (this -> auctionEnded = false) else u)})
                                  (unit end () {return (if (((msg -> sender) == (this -> owner) ) && ((this -> auctionEnded) == false)) then (this -> auctionEnded = true) else u)})
                                  (unit bid ((uint bid)) {
                                     return (if ((msg -> sender) == (this -> owner) )  then u
                                      else (if ((this -> auctionEnded) == true) then u
                                       else (if ((this -> highestBidder) == (msg -> sender)) then u
                                        else (if (((this -> pendingReturns)[(msg -> sender)]) > 0) then u else (if (bid < 0) then u
                                         else (if (bid <= (this -> highestBid)) then u
                                          else ((this -> pendingReturns = ((this -> pendingReturns)[(msg -> sender) -> bid])) ((this -> highestBidder = (msg -> sender)) (this -> highestBid = bid)))))))))})
                                  (unit withdraw () {
                                      return (if ((msg -> sender) == (this -> owner) ) then u
                                       else (if ((this -> highestBidder) == (msg -> sender)) then u
                                        else (if (((this -> pendingReturns)[(msg -> sender)]) == 0) then u
                                         else (this -> pendingReturns = ((this -> pendingReturns)[(msg -> sender) -> 0])))))})
                                  (unit win () {
                                       return (if ((msg -> sender) == (this -> owner) ) then u
                                        else (if ((this -> auctionEnded) == false) then u
                                         else (if (((this -> pendingReturns)[(msg -> sender)]) == 0) then u
                                          else (if ((this -> highestBidder) == (msg -> sender)) then
                                                   (((Client ((msg -> sender))) -> withdraw -> value(0) -> sender((msg -> sender)) ((amount : ((this -> pendingReturns)[(msg -> sender)])))) (this -> pendingReturns = ((this -> pendingReturns)[(msg -> sender) -> 0])) )
                                                   else u))))
                                       })
                                  
                                  })
               (contract Owner {(uint a) (Owner () {})})
               (contract Client {
                                 (uint balance)
                                 (Client ((uint balance)) {(this -> balance = balance)})
                                 (uint getBalance () {return (this -> balance)})
                                 (unit withdraw ((uint amount)) {return (this -> balance = ((this -> balance) - amount))})})
              ) (()) (()) ((cOwner : Owner) (aOwner : address) (cAuction : Auction) (aAuction : address) (cC1 : Client) (aC1 : address) (cC2 : Client) (aC2 : address)) ((Owner o = (new Owner -> value (0) () (cOwner aOwner))) ((Auction x = (new Auction -> value (0) ((pendingReturns : ()) (auctionEnded : false) (highestBid : 0) (highestBidder : a) (owner : aOwner))  (cAuction aAuction)) ) ((x -> init -> value (0) -> sender(aOwner) ()) ((Client c1 = (new Client -> value (500) ((balance : 500)) (cC1 aC1))) ((x -> bid -> value (3) -> sender((address(c1))) ((bid : 9))) ((Client c2 = (new Client -> value (560) ((balance : 800)) (cC2 aC2))) ((x -> bid -> value (0) -> sender ((address(c2))) ((bid : 19))) ((x -> withdraw -> value (0) -> sender ((address(c1))) ()) ((x -> end -> value (0) -> sender(aOwner) ()) (x -> win -> value (0) -> sender(aC2) ())))) ))) )) ) _ ))






(judgment-holds (⊢wf ((contract EOC {(uint a) (EOC () {}) (unit fb () {return u})})
               (contract Bank {
                               ((mapping (address => unit)) balances)
                               (Bank (((mapping (address => unit)) balances)) {(this -> balances = balances)})
                               (unit deposit () {return (this -> balances = ((this -> balances)[(msg -> sender) -> (((this -> balances)[(msg -> sender)]) + (msg -> value))]))})
                               (unit withdraw ((uint amount)) {return (if (((this -> balances)[(msg -> sender)]) >= amount) then ((this -> balances = ((this -> balances)[(msg -> sender) -> (((this -> balances)[(msg -> sender)]) - amount)])) ((msg -> sender) -> transfer (amount))) else u)})
                               (uint getBalance() {return ((this -> balances)[(msg -> sender)])})
                                                           (unit transfer ((address to) (uint amount)) {return (if (((this -> balances)[(msg -> sender)]) >= amount) then ((this -> balances = ((this -> balances)[(msg -> sender) -> (((this -> balances)[(msg -> sender)]) - amount)])) (this -> balances = ((this -> balances)[to -> (((this -> balances)[to]) + amount)]))) else u)})})
               
              ) (()) (()) ((cEOC : EOC) (aEOC : address) (cBank : Bank) (aBank : address)) ((EOC xEOC = (new EOC -> value (1000) () (cEOC aEOC))) ((Bank yBank = (new Bank -> value (0) ((balances : ())) (cBank aBank))) ((yBank -> deposit -> value (500) -> sender ((address (xEOC))) ()) (yBank -> transfer -> value (0) -> sender ((address (xEOC))) ((to : (address (yBank))) (amount : 87)))))) unit ))

|#