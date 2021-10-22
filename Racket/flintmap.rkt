 #lang racket
(require redex)

;;;;;Language;;;;
(define-language Flint
  ;Main language specification
  ;Contract declaration
  (CD ::= (contract C (tss ...) {vars ...} K PB ...))

  ;Variable declaration
  (vars ::= (var x : t)
        (var x : t = v)
        (let x : t)
        (let x : t = v)
        )

  ;Constructor
  (K ::= (C :: (cl cl ...) {(public init (params ...) {e ...}) F ...}))
  
  ;Protection Blocks
  (PB ::= (C @ (tss tss ...) :: (cl ...) {F ...}))

  ;Function declaration
  (F ::= (public func f (params ...) -> t {e ... return e}))

  ;Parameters
  (params ::= (x : t))

  ;Types
  (t ::= Int Address Bool Void C (t ...) (t : t))
  
  ;Type state
  (ts ::= (a -> tss ...))
  (tss ::= variable-not-otherwise-mentioned)

  ;Caller of contract
  (cl ::= variable-not-otherwise-mentioned
      anycaller)

  ;Expressions
  (e ::= 
       x
       v
       self
       ;if condition
       (if (e) {e} else {e})
       ;varibable assignment and declaration
       (var x : t = e)
       (var x : t)
       (let x : t = e)
       (let x : t)
       ;function call
       (C -> init ((x : e) ...) -> a)
       (C -> init ((x : e) ...) -> n -> a)
       (e -> f ((x : e) ... ))
       (f ((x : e) ...))
       (e -> f ((x : e) ...) -> sender (a))
       ;(call C -> f ((x : e) ...))
       (try ? (e -> f ((x : e) ...))) ;for dynamic checking (later)
       ;read var
       (e -> x)
       (e -> x = e)
       (x = e)
       ;return
       (return e)
       ;(x -> transfer from x amount v)
       ;sequential composition
       (e e ...)
       ;become statement
       (become tss)
       b
       (e a-op e)
       (x : v)
       (e [e ::])
       (e [e :: e])
       revert
       )

  ;Values
  (v ::= n bool a unit M )

  (a ::= (variable-prefix a))
  (f ::= variable-not-otherwise-mentioned)
  (C ::= variable-not-otherwise-mentioned)
  (x ::= variable-not-otherwise-mentioned)
  (n ::= integer)
  (bool ::= true false)
  (b ::= (e b-op1 e)
     (e b-op2 e))
  (b-op1 ::= < <= == >= > !=)
  (b-op2 ::= && )
  (a-op ::= + - * / % **)
  (M ::= ((v : v) ...))

  ;Context Evaluation
  (E ::= hole
     (if (E) {e} else {e})
     (var x : t = E)
     (let x : t = E)
     (C -> init ((x : v) ... (x : E) (x : e) ...) -> a)
     (C -> init ((x : v) ... (x : E) (x : e) ...) -> n -> a)
     (E -> f ((x : e) ...))
     (a -> f ((x : v) ... (x : E) (x : e) ...))
     (f ((x : v) ... (x : E) (x : e) ...))
     (E -> f ((x : e) ...) -> sender (a))
     (a -> f ((x : v) ... (x : E) (x : e) ...) -> sender (a))
     (try ? (E -> f ((x : e) ...)))
     (try ? (a -> f ((x : v) ... (x : E) (x : e) ...)))
     (E -> x)
     (E -> x = e)
     (a -> x = E)
     (x = E)
     (E e ...)
     (return E)
     
     (E a-op e)
     (v a-op E)
     (E b-op1 e)
     (v b-op1 E)
     (E b-op2 e)
     (bool b-op2 E)
     (x : E)
     (E [e ::])
     (M [E ::])
     (E [e :: e])
     (M [E :: e])
     (M [v :: E])
     )

  ;Environments
  ;Programs classes
  (classes ::= (CD ...))
  ;Blockchain envioromnent
  (env-ß ::= (ß-v ...))
  (ß-v ::= contracts varmap)
  (contracts ::= (a -> (C varmap ... n) -> varmap ... -> varmap ...))
  (varmap ::= (x : v)
          (x : ))
  ;Stack environment
  
  (env-s ::= (ß-v ... a ...))
  ;Stack Type States
  (CTS ::= (ts ...))
 )

;;Reduction Relations;;
(define s->ßs
  (reduction-relation
  Flint
  #:domain (e env-ß env-s CTS classes)
   ;Arithmetic Expressions
   (--> [(in-hole E (n_1 + n_2)) env-ß env-s CTS classes]
        [(in-hole E ,(+ (term n_1)(term n_2))) env-ß env-s CTS classes]
        "ADD")
   (--> [(in-hole E (n_1 - n_2)) env-ß env-s CTS classes]
        [(in-hole E ,(- (term n_1)(term n_2))) env-ß env-s CTS classes]
        "SUB")
   (--> [(in-hole E (n_1 * n_2)) env-ß env-s CTS classes]
        [(in-hole E ,(* (term n_1)(term n_2))) env-ß env-s CTS classes]
        "MULT")
   (--> [(in-hole E (n_1 / n_2)) env-ß env-s CTS classes]
        [(in-hole E ,(/ (term n_1)(term n_2))) env-ß env-s CTS classes]
        "DIV")
   (--> [(in-hole E (n_1 % n_2)) env-ß env-s CTS classes]
        [(in-hole E ,(modulo (term n_1)(term n_2))) env-ß env-s CTS classes]
        "MOD")
   (--> [(in-hole E (n_1 ** n_2)) env-ß env-s CTS classes]
        [(in-hole E ,(expt (term n_1)(term n_2))) env-ß env-s CTS classes]
        "EXP")
   ;Boolean Expression
   (--> [(in-hole E (v_1 == v_2)) env-ß env-s CTS classes]
        [(in-hole E ,(if (equal? (term v_1) (term v_2)) (term true) (term false))) env-ß env-s CTS classes]
        "EQUAL")
   (--> [(in-hole E (v_1 != v_2)) env-ß env-s CTS classes]
        [(in-hole E ,(if (equal? (term v_1) (term v_2)) (term false) (term true))) env-ß env-s CTS classes]
        "NOT-EQUAL")
   (--> [(in-hole E (n_1 <= n_2)) env-ß env-s CTS classes]
        [(in-hole E ,(if (<= (term n_1) (term n_2)) (term true) (term false))) env-ß env-s CTS classes]
        "LESS-EQ")
   (--> [(in-hole E (n_1 < n_2)) env-ß env-s CTS classes]
        [(in-hole E ,(if (< (term n_1) (term n_2)) (term true) (term false))) env-ß env-s CTS classes]
        "LESS")
   (--> [(in-hole E (n_1 >= n_2)) env-ß env-s CTS classes]
        [(in-hole E ,(if (>= (term n_1) (term n_2)) (term true) (term false))) env-ß env-s CTS classes]
        "GREATER-EQ")
   (--> [(in-hole E (n_1 > n_2)) env-ß env-s CTS classes]
        [(in-hole E ,(if (> (term n_1) (term n_2)) (term true) (term false))) env-ß env-s CTS classes]
        "GREATER")
   (--> [(in-hole E (bool_1 && bool_2)) env-ß env-s CTS classes]
        [(in-hole E ,(if (equal? (term bool_1) (term bool_2)) (term true) (term false))) env-ß env-s CTS classes]
        "AND")
   
   ;Conditional clauses
   (--> [(in-hole E (if (true) {e_1} else {e_2})) env-ß env-s CTS classes]
       [(in-hole E e_1) env-ß env-s CTS classes]
        "IF-TRUE")
   (--> [(in-hole E (if (false) {e_1} else {e_2})) env-ß env-s CTS classes]
        [(in-hole E e_2) env-ß env-s CTS classes]
        "IF_FALSE")
   ; Mapping
   (--> [(in-hole E (M [v ::])) env-ß env-s CTS classes]
        [(in-hole E (mappsel M v)) env-ß env-s CTS classes]
        "MAP-SEL")
   (--> [(in-hole E (M [v_k :: v_v])) env-ß env-s CTS classes]
        [(in-hole E (mappass M v_k v_v)) env-ß env-s CTS classes]
        "MAP-ASS ")
   ;Sequential Composition
   (--> [(in-hole E (v e e_1 ...)) env-ß (ß-v ...) CTS classes]
        [(in-hole E (e e_1 ...)) env-ß env-ß CTS classes]
        "SEQ-C")
   (--> [(in-hole E (v e e_1 ...)) env-ß (ß-v ... a_0 a ...) CTS classes]
        [(in-hole E (e e_1 ...)) env-ß (ß-v ... a_0 a ...) CTS classes]
        "SEQ")
   (--> [(in-hole E (v)) env-ß env-s CTS classes]
        [(in-hole E v) env-ß env-s CTS classes]
        "REM-PAR")
   
   ;Variable and Constant Declaration
   (--> [(in-hole E (var x : t = v)) env-ß env-s CTS classes]
        [(in-hole E v) (decl env-ß (top-s env-s) x v 1) env-s CTS classes]
        "DECL-VAR")
   (--> [(in-hole E (var x : Int)) env-ß env-s CTS classes]
        [(in-hole E 0) (decl env-ß (top-s env-s) x 0 1) env-s CTS classes]
        "DECL-VAR-INT")
   (--> [(in-hole E (var x : Bool)) env-ß env-s CTS classes]
        [(in-hole E false) (decl env-ß (top-s env-s) x false 1) env-s CTS classes]
        "DECL-VAR-BOOL")
   (--> [(in-hole E (var x : Address)) env-ß env-s CTS classes]
        [(in-hole E aNULL) (decl env-ß (top-s env-s) x aNULL 1) env-s CTS classes]
        "DECL-VAR-ADDRESS")
   (--> [(in-hole E (let x : t = v)) env-ß env-s CTS classes]
        [(in-hole E v) (decl env-ß (top-s env-s) x v 2) env-s CTS classes]
        "DECL-CONS")
   (--> [(in-hole E (let x : Int)) env-ß env-s CTS classes]
        [(in-hole E 0) (decl env-ß (top-s env-s) x 0 2) env-s CTS classes] 
        "DECL-CONS-INT")
   (--> [(in-hole E (let x : Bool)) env-ß env-s CTS classes]
        [(in-hole E false) (decl env-ß (top-s env-s) x false 2) env-s CTS classes] 
        "DECL-CONS-BOOL")
   (--> [(in-hole E (let x : Address)) env-ß env-s CTS classes]
        [(in-hole E aNULL) (decl env-ß (top-s env-s) x aNULL 2) env-s CTS classes] 
        "DECL-CONS-ADDRESS")
   ;Read variable
   (--> [(in-hole E x) env-ß env-s CTS classes]
        [(in-hole E (find env-ß (top-s env-s) x)) env-ß env-s CTS classes]
        "VAR")
   (--> [(in-hole E (a -> x)) env-ß env-s CTS classes]
        [(in-hole E (find env-ß a x)) env-ß env-s CTS classes]
        "STATE_VAR")
   
   ;Assign variables
   (--> [(in-hole E (x = v)) env-ß env-s CTS classes]
        [(in-hole E v) (assign env-ß (top-s env-s) x v) env-s CTS classes]
        "ASS")
   (--> [(in-hole E (a -> x = v)) env-ß env-s CTS classes]
        [(in-hole E v) (assign env-ß a x v) env-s CTS classes]
        "STATE-ASS")
   ;Call function
   (--> [(in-hole E (a -> f ((x : v) ...)))
         (ß-v_1 ... (a -> (C (x_1 : v_1)... n_1) -> (x_2 : v_2) ... -> (x_3 : v_3) ...) ß-v_2 ...)
         (ß-v_s ... a_1 ... a_s) (ts_1 ... (a -> tss_0 ... tss_x)  ts_0 ...)
         (CD_1 ... (contract C (tss ...) {vars ...} K PB_1 ... (C @ (tss_pb ...) :: (cl ...) {F_1 ... (public func f ((x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...)]
        [(in-hole E (call (ß-v_1 ... (a -> (C (x_1 : v_1)... n_1) -> (x_2 : v_2) ... -> (x_3 : v_3) ...) ß-v_2 ...) (CD_1 ... (contract C (tss ...) {vars ...} K PB_1 ... (C @ (tss_pb ...) :: (cl ...) {F_1 ... (public func f ((x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...) f a a_s ((x : v) ...)));(subst-x ((x : v)...) (subst-e a (e_1 ... (return e)))))
         (declcall (uptbal (uptbal (ß-v_1 ... (a -> (C (x_1 : v_1)... n_1) -> (x_2 : v_2) ... -> (x_3 : v_3) ...) ß-v_2 ...) a 1) a_s ,(- (term 0)(term 1))) a ((x : v)...))
         (call-s (ß-v_s ... a_1 ... a_s)) (ts_1 ... (a -> tss_0 ... tss_x)  ts_0 ...)
         (CD_1 ... (contract C (tss ...) {vars ...} K PB_1 ... (C @ (tss_pb ...) :: (cl ...) {F_1 ... (public func f ((x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...)] ;repete address no env-s para quando fizer return bater certo
        "CALL"
                (judgment-holds (subsequence (tss_x) (tss_pb ...)))
                (judgment-holds (subsequence (tss_pb ...) (tss ...)))
                (side-condition (<= (term 1) (term n_1))))
   (--> [(in-hole E (try ? (a -> f ((x : v) ...))))
         (ß-v_1 ... (a -> (C (x_1 : v_1)... n_1) -> (x_2 : v_2) ... -> (x_3 : v_3) ...) ß-v_2 ...)
         (ß-v_s ... a_1 ... a_s) (ts_1 ... (a -> tss_0 ... tss_x)  ts_0 ...)
         (CD_1 ... (contract C (tss ...) {vars ...} K PB_1 ... (C @ (tss_pb ...) :: (cl ...) {F_1 ... (public func f ((x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...)]
        [(in-hole E (call (ß-v_1 ... (a -> (C (x_1 : v_1)... n_1) -> (x_2 : v_2) ... -> (x_3 : v_3) ...) ß-v_2 ...) (CD_1 ... (contract C (tss ...) {vars ...} K PB_1 ... (C @ (tss_pb ...) :: (cl ...) {F_1 ... (public func f ((x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...) f a a_s ((x : v) ...)));(subst-x ((x : v)...) (subst-e a (e_1 ... (return e)))))
         (declcall (uptbal (uptbal (ß-v_1 ... (a -> (C (x_1 : v_1)... n_1) -> (x_2 : v_2) ... -> (x_3 : v_3) ...) ß-v_2 ...) a 1) a_s ,(- (term 0)(term 1))) a ((x : v)...))
         (call-s (ß-v_s ... a_1 ... a_s)) (ts_1 ... (a -> tss_0 ... tss_x)  ts_0 ...)
         (CD_1 ... (contract C (tss ...) {vars ...} K PB_1 ... (C @ (tss_pb ...) :: (cl ...) {F_1 ... (public func f ((x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...)] ;repete address no env-s para quando fizer return bater certo
        "CALL-TRY"
                (judgment-holds (subsequence (tss_x) (tss_pb ...)))
                (judgment-holds (subsequence (tss_pb ...) (tss ...)))
                (side-condition (<= (term 1) (term n_1))))
   (--> [(in-hole E (a -> f ((x : v) ...))) (ß-v_1 ... (a -> (C (x_1 : v_1)... n_1) -> (x_2 : v_2) ... -> (x_3 : v_3) ...) ß-v_2 ...) (ß-v_s ... a_1 ... a_s) CTS (CD_1 ... (contract C (tss ...) {vars ...} PB_1 ... (C :: (cl ... anycaller cl_1 ...) {( public init (params ...) { e_i ...}) F_1 ... (public func f ((x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...)]
        [(in-hole E (subst-x ((x : v)...) (subst-e a (e_1 ... (return e)))))
         (declcall (uptbal (uptbal (ß-v_1 ... (a -> (C (x_1 : v_1)... n_1) -> (x_2 : v_2) ... -> (x_3 : v_3) ...) ß-v_2 ...) a 1) a_s ,(- (term 0)(term 1))) a ((x : v) ...))
         (call-s (a_1 ... a_s)) CTS
         (CD_1 ... (contract C (tss ...) {vars ...} PB_1 ... (C :: (cl ... anycaller cl_1 ...) {( public init (params ...) { e_i ...}) F_1 ... (public func f ((x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...)]
        "CALL-2"
                (side-condition (<= (term 1) (term n_1))));quando a funcao esta dentro do block init
   (--> [(in-hole E (a -> f ((x : v) ...))) (ß-v_1 ... (a -> (C (x_1 : v_1)... n_1) -> (x_2 : v_2) ... -> (x_3 : v_3) ...) ß-v_2 ...) (ß-v_s ... a_1 ... a_s) CTS (CD_1 ... (contract C (tss ...) {vars ...} PB_1 ... (C :: (cl ... anycaller cl_1 ...) {( public init (params ...) { e_i ...}) F_1 ... (public func f ((x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...)]
        [(in-hole E (subst-x ((x : v)...) (subst-e a (e_1 ... (return e)))))
         (declcall (uptbal (uptbal (ß-v_1 ... (a -> (C (x_1 : v_1)... n_1) -> (x_2 : v_2) ... -> (x_3 : v_3) ...) ß-v_2 ...) a 1) a_s ,(- (term 0)(term 1))) a ((x : v) ...))
         (call-s (a_1 ... a_s)) CTS
         (CD_1 ... (contract C (tss ...) {vars ...} PB_1 ... (C :: (cl ... anycaller cl_1 ...) {( public init (params ...) { e_i ...}) F_1 ... (public func f ((x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...)]
        "CALL-TRY-2"
                (side-condition (<= (term 1) (term n_1))))
   (--> [(in-hole E (a -> f ((x : v) ...))) (ß-v_1 ... (a -> (C (x_1 : v_1)... n_1) -> (x_2 : v_2) ... -> (x_3 : v_3) ...) ß-v_2 ...) (ß-v_s ... a_1 ... a_s) CTS (CD_1 ... (contract C (tss ...) {vars ...} K PB_1 ... (C @ (anystate) :: (cl ...) {F_1 ... (public func f ((x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...)]
        [(in-hole E (call (ß-v_1 ... (a -> (C (x_1 : v_1)... n_1) -> (x_2 : v_2) ... -> (x_3 : v_3) ...) ß-v_2 ...) (CD_1 ... (contract C (tss ...) {vars ...} K PB_1 ... (C @ (anystate) :: (cl ...) {F_1 ... (public func f ((x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...) f a a_s ((x : v)...)))
         (declcall (uptbal (uptbal (ß-v_1 ... (a -> (C (x_1 : v_1)... n_1) -> (x_2 : v_2) ... -> (x_3 : v_3) ...) ß-v_2 ...) a 1) a_s ,(- (term 0)(term 1))) a ((x : v) ...))
         (call-s (a_1 ... a_s)) CTS
         (CD_1 ... (contract C (tss ...) {vars ...} K PB_1 ... (C @ (anystate) :: (cl ...) {F_1 ... (public func f ((x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...)] ;any nao precisa de verificaçao, any é palavra reservada
        "CALL-ANY"
                 (side-condition (<= (term 1) (term n_1))))
   (--> [(in-hole E (a -> f ((x : v) ...))) (ß-v_1 ... (a -> (C (x_1 : v_1)... n_1) -> (x_2 : v_2) ... -> (x_3 : v_3) ...) ß-v_2 ...) (ß-v_s ... a_1 ... a_s) CTS (CD_1 ... (contract C (tss ...) {vars ...} K PB_1 ... (C @ (anystate) :: (cl ...) {F_1 ... (public func f ((x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...)]
        [(in-hole E (call (ß-v_1 ... (a -> (C (x_1 : v_1)... n_1) -> (x_2 : v_2) ... -> (x_3 : v_3) ...) ß-v_2 ...) (CD_1 ... (contract C (tss ...) {vars ...} K PB_1 ... (C @ (anystate) :: (cl ...) {F_1 ... (public func f ((x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...) f a a_s ((x : v)...)))
         (declcall (uptbal (uptbal (ß-v_1 ... (a -> (C (x_1 : v_1)... n_1) -> (x_2 : v_2) ... -> (x_3 : v_3) ...) ß-v_2 ...) a 1) a_s ,(- (term 0)(term 1))) a ((x : v) ...))
         (call-s (a_1 ... a_s)) CTS
         (CD_1 ... (contract C (tss ...) {vars ...} K PB_1 ... (C @ (anystate) :: (cl ...) {F_1 ... (public func f ((x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...)] ;any nao precisa de verificaçao, any é palavra reservada
        "CALL-TRY-ANY"
                 (side-condition (<= (term 1) (term n_1))))
   (--> [(in-hole E (a -> f ((x : v) ...))) (ß-v_1 ... (a -> (C (x_1 : v_1)... n_1) -> (x_2 : v_2) ... -> (x_3 : v_3) ...) ß-v_2 ...) env-s CTS classes]
        [(in-hole E revert) (ß-v_1 ... (a -> (C (x_1 : v_1)... n_1) -> (x_2 : v_2) ... -> (x_3 : v_3) ...) ß-v_2 ...) env-s CTS classes]
        "CALL-REVERT"
        (side-condition (> (term 1) (term n_1))))
   (--> [(in-hole E (a -> f ((x : v) ...) -> sender (a_s))) (ß-v_1 ... (a -> (C (x_1 : v_1)... n_1) -> (x_2 : v_2) ... -> (x_3 : v_3) ...) ß-v_2 ...) env-s (ts_1 ... (a -> tss_1 ... tss_0) ts_0 ...) (CD_1 ... (contract C (tss ...) {vars ...} K PB_1 ... (C @ (tss_pb ...) :: (cl ...) {F_1 ... (public func f ((x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...)]
        [(in-hole E (call (ß-v_1 ... (a -> (C (x_1 : v_1)... n_1) -> (x_2 : v_2) ... -> (x_3 : v_3) ...) ß-v_2 ...) (CD_1 ... (contract C (tss ...) {vars ...} K PB_1 ... (C @ (tss_pb ...) :: (cl ...) {F_1 ... (public func f ((x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...) f a a_s ((x : v) ...)))
         (declcall (uptbal (uptbal (ß-v_1 ... (a -> (C (x_1 : v_1)... n_1) -> (x_2 : v_2) ... -> (x_3 : v_3) ...) ß-v_2 ...) a 1) a_s ,(- (term 0)(term 1))) a ((x : v)...))
         (add-s env-s a) (ts_1 ... (a -> tss_1 ... tss_0) ts_0 ...)
         (CD_1 ... (contract C (tss ...) {vars ...} K PB_1 ...
                             (C @ (tss_pb ...) :: (cl ...) {F_1 ... (public func f ((x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...)] 
        "CALL-SENDER"
        	(judgment-holds (subsequence (tss_0) (tss_pb ...)))
                (judgment-holds (subsequence (tss_pb ...) (tss ...)))
                (side-condition (<= (term 1) (term n_1))))
   (--> [(in-hole E (a -> f ((x : v) ...) -> sender (a_s))) (ß-v_1 ... (a -> (C (x_1 : v_1)... n_1) -> (x_2 : v_2) ... -> (x_3 : v_3) ...) ß-v_2 ...) env-s CTS (CD_1 ... (contract C (tss ...) {vars ...} PB_1 ... (C :: (cl ... anycaller cl_1 ...) {( public init (params ...) { e_i ...}) F_1 ... (public func f ((x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...)]
        [(in-hole E (subst-x ((x : v)...) (subst-e a (e_1 ... (return e)))))
         (declcall (uptbal (uptbal (ß-v_1 ... (a -> (C (x_1 : v_1)... n_1) -> (x_2 : v_2) ... -> (x_3 : v_3) ...) ß-v_2 ...) a 1) a_s ,(- (term 0)(term 1))) a ((x : v) ...))
         (add-s env-s a) CTS
         (CD_1 ... (contract C (tss ...) {vars ...} PB_1 ... (C :: (cl ... anycaller cl_1 ...) {( public init (params ...) { e_i ...}) F_1 ... (public func f ((x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...)]
        "CALL-SENDER-2"
        (side-condition (<= (term 1) (term n_1)))) ;quando a funcao esta dentro do block init, deve ser any_caller, nao precisa de verificaçao
   (--> [(in-hole E (a -> f ((x : v) ...) -> sender (a_s))) (ß-v_1 ... (a -> (C (x_1 : v_1)... n_1) -> (x_2 : v_2) ... -> (x_3 : v_3) ...) ß-v_2 ...) env-s CTS (CD_1 ... (contract C (tss ...) {vars ...} K PB_1 ... (C @ (anystate) :: (cl ...) {F_1 ... (public func f ((x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...)]
        [(in-hole E (call (ß-v_1 ... (a -> (C (x_1 : v_1)... n_1) -> (x_2 : v_2) ... -> (x_3 : v_3) ...) ß-v_2 ...) (CD_1 ... (contract C (tss ...) {vars ...} K PB_1 ... (C @ (anystate) :: (cl ...) {F_1 ... (public func f ((x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...) f a a_s ((x : v) ...)))
         (declcall (uptbal (uptbal (ß-v_1 ... (a -> (C (x_1 : v_1)... n_1) -> (x_2 : v_2) ... -> (x_3 : v_3) ...) ß-v_2 ...) a 1) a_s ,(- (term 0) (term 1))) a ((x : v) ...))
         (add-s env-s a) CTS
         (CD_1 ... (contract C (tss ...) {vars ...} K PB_1 ... (C @ (anystate) :: (cl ...) {F_1 ... (public func f ((x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...)] ;any nao precisa de verificaçao, any é palavra reservada
        "CALL-SENDER-ANY"
        (side-condition (<= (term 1) (term n_1))))
   (--> [(in-hole E (a -> f ((x : v)...) -> sender (a_s))) (ß-v_1 ... (a -> (C (x_1 : v_1)... n_1) -> (x_2 : v_2) ... -> (x_3 : v_3) ...) ß-v_2 ...) env-s CTS classes]
        [(in-hole E revert) (ß-v_1 ... (a -> (C (x_1 : v_1)... n_1) -> (x_2 : v_2) ... -> (x_3 : v_3) ...) ß-v_2 ...) env-s CTS classes]
        "CALL-SENDER-R"
        (side-condition (> (term 1) (term n_1))))
   ;Init
   #|(--> [(in-hole E (C -> init ((x : v) ...) -> a)) env-ß env-s CTS (CD_1 ... (contract C (tss ...) { (var x_1 : t_1) ... (var x_2 : t_2 = v_2) ... (let x_3 : t_3) ... (let x_4 : t_4 = v_4) ...} (C :: (cl ...) { ( public init ((x : t) ...) { e ...}) F ...}) PB ...) CD_2 ...)]
        [(in-hole E (subst-x ((x : v) ...) (subst-e a ( e ... (return unit))))) (initc env-ß a 0 C ((var x_1 : t_1) ... (var x_2 : t_2 = v_2) ... (let x_3 : t_3) ... (let x_4 : t_4 = v_4) ...)) (add-s env-s a) CTS (CD_1 ... (contract C (tss ...) { (var x_1 : t_1) ... (var x_2 : t_2 = v_2) ... (let x_3 : t_3) ... (let x_4 : t_4 = v_4) ...} (C :: (cl ...) { ( public init ((x : t) ...) { e ...}) F ...}) PB ...) CD_2 ...)]
        "INIT")|#
   (--> [(in-hole E (C -> init ((x : v) ...) -> n -> a)) env-ß env-s CTS (CD_1 ... (contract C (tss ...) { (var x_1 : t_1) ... (var x_2 : t_2 = v_2) ... (let x_3 : t_3) ... (let x_4 : t_4 = v_4) ...} (C :: (cl ...) { ( public init ((x : t) ...) { e ...}) F ...}) PB ...) CD_2 ...)]
        [(in-hole E (subst-x ((x : v) ...) (subst-e a ( e ... (return unit))))) (initc env-ß a n C ((var x_1 : t_1) ... (var x_2 : t_2 = v_2) ... (let x_3 : t_3) ... (let x_4 : t_4 = v_4) ...)) (add-s env-s a) CTS (CD_1 ... (contract C (tss ...) { (var x_1 : t_1) ... (var x_2 : t_2 = v_2) ... (let x_3 : t_3) ... (let x_4 : t_4 = v_4) ...} (C :: (cl ...) { ( public init ((x : t) ...) { e ...}) F ...}) PB ...) CD_2 ...)]
        "INIT")
   ;Return
   (--> [(in-hole E (return v)) env-ß env-s CTS classes]
        [(in-hole E v) env-ß (pop-s env-s) CTS classes]
        "RETURN")
   (--> [(in-hole E (become tss)) env-ß (ß-v ... a_1 ... a) CTS classes]
        [(in-hole E unit) env-ß (ß-v ... a_1 ... a) (add-cts CTS a tss) classes]
        "BECOME")
   (--> [(in-hole E (return revert)) env-ß env-s CTS classes]
        [(in-hole E revert) env-ß (pop-s env-s) CTS classes]
        "RETURN-R")
   (--> [(in-hole E (revert e ...)) env-ß env-s CTS classes]
        [(in-hole E revert) (rev env-s) env-s CTS classes]
        "SEQ-R")
   ))

(define-metafunction Flint
  initc : env-ß a n C (vars ...) ->  env-ß
  [(initc (ß-v ...) a n C  ((var x_1 : t_1) ... (var x_2 : t_2 = v_2) ... (let x_3 : t_3) ... (let x_4 : t_4 = v_4) ...)) (ß-v ... (a -> (C (x_1 : ) ... (x_2 : v_2) ... n) -> (x_3 : ) ... (x_4 : v_4) ...  -> )) (side-condition (not (judgment-holds (ain (ß-v ...) a))))]
  )

(define-metafunction Flint
  decl : env-ß a x v n -> env-ß
  [(decl (ß-v_1 ... (a -> (C (x_1 : v_1)... n_1) -> (x_2 : v_2) ... -> (x_3 : v_3) ...) ß-v_2 ...) a x v 1) (ß-v_1 ... (a -> (C (x_1 : v_1)...  n_1) -> (x_2 : v_2) ... -> (x_3 : v_3) ... (x : v)) ß-v_2 ...) (side-condition (not (member (term (x : _)) (term ((x_1 : _) ...)))))
                               (side-condition (not (member (term (x : _)) (term ((x_3 : _) ...)))))
                               (side-condition (not (member (term (x : _)) (term ((x_2 : _) ...)))))]
  [(decl (ß-v_1 ... (a -> (C (x_1 : v_1)... n_1) -> (x_2 : v_2) ... -> (x_3 : v_3) ...(x : v_old) (x_4 : v_4) ...) ß-v_2 ...) a x v 1) (ß-v_1 ... (a -> (C (x_1 : v_1)...  n_1) -> (x_2 : v_2) ... -> (x_3 : v_3) ... (x : v) (x_4 : v_4) ...) (x : v_old) ß-v_2 ...) 
                               ]
  [(decl (ß-v_1 ... (a -> (C (x_1 : v_1)... n_1) -> (x_2 : v_2) ... -> (x_3 : v_3) ...) ß-v_2 ...) a x v 2) (ß-v_1 ... (a -> (C (x_1 : v_1)... n_1) -> (x_2 : v_2) ... (x : v) -> (x_3 : v_3) ...) ß-v_2 ...) (side-condition (not (member (term (x : _)) (term ((x_1 : _) ...)))))
                               (side-condition (not (member (term (x : _)) (term ((x_2 : _) ...)))))]) 

(define-metafunction Flint
  declcall : env-ß a any -> env-ß
  [(declcall (ß-v_1 ... (a -> (C (x_1 : v_1)... n_1) -> (x_2 : v_2) ... -> (x_4 : v_4) ... (x : v_3) ... (x_5 : v_5) ...) ß-v_2 ...) a ((x : v) ...))
   (ß-v_1 ... (a -> (C (x_1 : v_1)... n_1) -> (x_2 : v_2) ... -> (x_4 : v_4) ... (x : v) ...(x_5 : v_5) ...) (x : v_3) ... ß-v_2 ...)]
  [(declcall (ß-v_1 ... (a -> (C (x_1 : v_1)... n_1) -> (x_2 : v_2) ... -> (x_3 : v_3) ...) ß-v_2 ...) a ((x : v) ...))
   (ß-v_1 ... (a -> (C (x_1 : v_1)... n_1) -> (x_2 : v_2) ... -> (x_3 : v_3) ... (x : v) ...) ß-v_2 ...)])

(define-metafunction Flint
  find : env-ß any x -> any
  [(find (ß-v_1 ... (a -> (C (x_1 : v_1) ... (x : v) (x_2 : v_2) ... n_1) -> (x_3 : v_3) ... -> (x_4 : v_4) ...) ß-v_2 ...) a x)
   v]
  [(find (ß-v_1 ... (a -> (C (x_1 : v_1) ... n_1) -> (x_2 : v_2) ... (x : v) (x_3 : v_3) ... -> (x_4 : v_4) ...) ß-v_2 ...) a x)
   v]
  [(find (ß-v_1 ... (a -> (C (x_1 : v_1) ... n_1) -> (x_2 : v_2) ... -> (x_3 : v_3) ... (x : v) (x_4 : v_4) ...) ß-v_2 ...) a x)
   v] ; talvez deva desaparecer porque sao parametros  no self
  [(find env-ß _ x) x]
  )

#|(define-metafunction Flint
  assign : env-ß a x v -> env-ß
  [(assign (ß-v_1 ... (a -> (C (x_1 : v_1) ... (x : v_old) (x_2 : v_2) ... n_1) -> (x_3 : v_3) ... -> (x_4 : v_4) ...) ß-v_2 ...) a x v)
   (ß-v_1 ... (a -> (C (x_1 : v_1) ... (x : v) (x_2 : v_2) ... n_1) -> (x_3 : v_3) ... -> (x_4 : v_4) ...) ß-v_2 ...)]
  [(assign (ß-v_1 ... (a -> (C (x_1 : v_1) ... (x : ) (x_2 : v_2) ... n_1) -> (x_3 : v_3) ... -> (x_4 : v_4) ...) ß-v_2 ...) a x v)
   (ß-v_1 ... (a -> (C (x_1 : v_1) ... (x : v) (x_2 : v_2) ... n_1) -> (x_3 : v_3) ... -> (x_4 : v_4) ...) ß-v_2 ...)]
  [(assign (ß-v_1 ... (a -> (C (x_1 : v_1) ... n_1) -> (x_2 : v_2) ... -> (x_3 : v_3) ... (x : v_old) (x_4 : v_4) ...) ß-v_2 ...) a x v)
   (ß-v_1 ... (a -> (C (x_1 : v_1) ... n_1) -> (x_2 : v_2) ... -> (x_3 : v_3) ... (x : v) (x_4 : v_4) ...) ß-v_2 ...) ]
  [(assign (ß-v_1 ... (a -> (C (x_1 : v_1) ... n_1) -> (x_2 : v_2) ... -> (x_3 : v_3) ... (x : ) (x_4 : v_4) ...) ß-v_2 ...) a x v)
   (ß-v_1 ... (a -> (C (x_1 : v_1) ... n_1) -> (x_2 : v_2) ... -> (x_3 : v_3) ... (x : v) (x_4 : v_4) ...) ß-v_2 ...) ]
  )|#
(define-metafunction Flint
  assign : env-ß a x v -> env-ß
  [(assign (ß-v_1 ... (a -> (C varmap_1 ... (x : v_old) varmap_2 ... n_1) -> varmap_3 ... -> varmap_4 ...) ß-v_2 ...) a x v)
   (ß-v_1 ... (a -> (C varmap_1 ... (x : v) varmap_2 ... n_1) -> varmap_3 ... -> varmap_4 ...) ß-v_2 ...)]
  [(assign (ß-v_1 ... (a -> (C varmap_1 ... (x : ) varmap_2 ... n_1) -> varmap_3 ... -> varmap_4 ...) ß-v_2 ...) a x v)
   (ß-v_1 ... (a -> (C varmap_1 ... (x : v) varmap_2 ... n_1) -> varmap_3 ... -> varmap_4 ...) ß-v_2 ...)]
  [(assign (ß-v_1 ... (a -> (C varmap_1 ...  n_1) -> varmap_2 ... -> varmap_3 ... (x : v_old) varmap_4 ...) ß-v_2 ...) a x v)
   (ß-v_1 ... (a -> (C varmap_1  ... n_1) -> varmap_2 ... -> varmap_3 ... (x : v) varmap_4 ...) ß-v_2 ...) ]
  [(assign (ß-v_1 ... (a -> (C varmap_1 ... n_1) -> varmap_2 ... -> varmap_3 ... (x : ) varmap_4 ...) ß-v_2 ...) a x v)
   (ß-v_1 ... (a -> (C varmap_1 ... n_1) -> varmap_2 ... -> varmap_3 ... (x : v) varmap_4 ...) ß-v_2 ...) ]
  )

(define-metafunction Flint
  call : env-ß classes f a a ((x : v) ...) -> any
  [(call (ß-v_1 ... (a -> (C varmap_0 ... (x_c : a_s) varmap_1 ... n_1) -> varmap_2 ... -> varmap_3 ...) ß-v_2 ...) (CD_1 ... (contract C (tss_all1 ... tss tss_all2 ...) {vars ...} K PB_1 ... (C @ (tss_01 ...) :: (cl_1 ... x_c cl_2 ...) {F_1 ... (public func f ((x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...) f a a_s ((x : v) ...))
   (subst-x ((x : v)...) (subst-e a (e_1 ... (return e))))]
  [(call (ß-v_1 ... (a -> (C varmap_1 ... n_1) -> varmap_0 ... (x_c : a_s) varmap_2 ... -> varmap_3 ...) ß-v_2 ...) (CD_1 ... (contract C (tss_all1 ... tss tss_all2 ...) {vars ...} K PB_1 ... (C @ (tss_01 ... tss t_02 ...) :: (cl_1 ... x_c cl_2 ...) {F_1 ... (public func f ((x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...) f a a_s ((x : v) ...))
   (subst-x ((x : v)...) (subst-e a (e_1 ... (return e))))]
  [;(call (ß-v_1 ... (a -> (C varmap_0 ... n_1) -> varmap_2 ... -> varmap_3 ...) ß-v_2 ...) (CD_1 ... (contract C (tss_all1 ... tss tss_all2 ...) {vars ...} K PB_1 ... (C @ (tss_01 ...) :: (any_caller) {F_1 ... (public func f ((x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...) f a a_s ((x : v) ...))
   (call (ß-v_1 ... (a -> (C varmap_1 ... n_1) -> varmap_2 ... -> varmap_3 ...) ß-v_2 ...) (CD_1 ... (contract C (tss_all1 ... tss tss_all2 ...) {vars ...} K PB_1 ... (C @ (tss_01 ... tss t_02 ...) :: (cl_1 ... anycaller cl_2 ...) {F_1 ... (public func f_0 ((x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...) f_0 a a_s ((x : v) ...))
   (subst-x ((x : v)...) (subst-e a (e_1 ... (return e))))]
  
  )

(define-metafunction Flint
  mappsel : M v -> v
  [(mappsel (M_1 ... (v_01 : v_001)... (v : v_1) (v_02 : v_002)... M_2 ...) v) v_1]
  [(mappsel M v) 0])

(define-metafunction Flint
  mappass : M v_1 v_2 -> M
  [(mappass (M_1 ...  (v_01 : v_001)... (v_1 : v_old) (v_02 : v_002)... M_2 ...) v_1 v)
   (M_1 ... (v_01 : v_001)... (v_1 : v) (v_02 : v_002)... M_2 ...) ]
 
  [(mappass ((v_01 : v_02) ...) v_1 v_2)
   ((v_01 : v_02) ... (v_1 : v_2)) (side-condition (not (member (term v_1) (term ((v_01 : v_02)...)))))])

(define-metafunction Flint
  add-s : env-s a -> env-s
  [(add-s (ß-v ... a_1 ...) a) (ß-v ... a_1 ... a)]
  )

(define-metafunction Flint
  call-s : env-s -> env-s
  [(call-s (ß-v ... a_1 ... a)) (ß-v ... a_1 ... a a)])

(define-metafunction Flint
  top-s : env-s -> any
  [(top-s (ß-v ... a_1 ... a)) a]
  [(top-s (ß-v ...)) (ß-v ...)])

(define-metafunction Flint
  rev : env-s -> env-s
  [(rev (ß-v ... a ... )) (ß-v ...)])

(define-metafunction Flint
  add-cts : CTS a tss -> CTS
  [(add-cts (ts_1 ... (a -> tss_1 ... ) ts_0 ...) a tss)
   (ts_1 ... (a -> tss_1 ... tss ) ts_0 ...)]
  [(add-cts (ts_1 ...) a tss)
   (ts_1 ... (a -> tss))])

(define-metafunction Flint
  pop-s : env-s -> env-s
  [(pop-s (ß-v ... a_1 ... a)) (ß-v ... a_1 ...)]
  [(pop-s (ß-v ...)) (ß-v ...)])

(define-metafunction Flint
  top-cts : CTS a -> tss
  [(top-cts (ts_1 ... (a -> tss_1 ... tss_0) ts_0 ...)) tss_0])

(define-metafunction Flint
  uptbal : env-ß a n -> env-ß
  [(uptbal (ß-v_1 ... (a -> (C (x_1 : v_1) ... n_old) -> (x_2 : v_2) ... -> (x_3 : v_3) ...) ß-v_2 ...) a n)
   (ß-v_1 ... (a -> (C (x_1 : v_1) ... ,(+ (term n_old)(term n))) -> (x_2 : v_2) ... -> (x_3 : v_3) ...) ß-v_2 ...)]
  )

(define-metafunction Flint
  subst-x : ((x : v) ...) any -> e
  [(subst-x () e)
   e]
  [(subst-x ((x : v) ...) (e))
   (subst-x ((x : v) ...) e)]
  [(subst-x ((x : v) ...) (if (e_1) {e_2} else {e_3}))
   (if ((subst-x ((x : v) ...) e_1))  {(subst-x ((x : v) ...) e_2)} else {(subst-x ((x : v) ...) e_3)})]
  [(subst-x ((x : v) ...) (var x_0 : t = e))
   (var x_0 : t = (subst-x ((x : v) ...) e))]
  [(subst-x ((x : v) ...) (let x_0 : t = e))
   (let x_0 : t = (subst-x ((x : v) ...) e))]
  [(subst-x ((x : v) ...) (e_0 [e_1 :: e_2]))
   ((subst-x ((x : v) ...) e_0) [(subst-x ((x : v) ...) e_1) :: (subst-x ((x : v) ...) e_2)])]
  [(subst-x ((x : v) ...) (e_0 [e_1 ::]))
   ((subst-x ((x : v) ...) e_0) [(subst-x ((x : v) ...) e_1) ::])]
  [(subst-x ((x : v) ...) (e_1 -> f ((x_1 : v_1) (x_2 : v_2) ...) ))
   ((subst-x ((x : v) ...) e_1) -> f (subst-x ((x : v) ...) ((x_1 : v_1) (x_2 : v_2) ...)))]
  [(subst-x ((x : v) ...) (e_1 -> f () ))
   ((subst-x ((x : v) ...) e_1) -> f ())]
  [(subst-x ((x : v) ...) ((e_1) -> f ((x_1 : v_1) ...) ))
   ((subst-x ((x : v) ...) e_1) -> f (subst-x ((x : v) ...) ((x_1 : v_1) ...)))]
  [(subst-x ((x : v) ...) (try ? ((e_1) -> f ((x_1 : v_1) ...) )))
   (try ? ((subst-x ((x : v) ...) e_1) -> f (subst-x ((x : v) ...) ((x_1 : v_1) ...))))]
  ;[(subst-x ((x : v) ...) (C -> init (() ...)))])
  [(subst-x ((x : v) ...) (e -> x_0))
   ((subst-x ((x : v) ...) e) -> x_0)]
  [(subst-x ((x : v) ...) (e -> x_0 = e_1))
   ((subst-x ((x : v) ...) e) -> x_0 = (subst-x ((x : v) ...) e_1))]
  [(subst-x ((x : v) ...) (return e))
   (return ((subst-x ((x : v) ...) e)))]
  [(subst-x ((x : v) ...) (e e_0 e_1 ...))
   ((subst-x ((x : v) ...) e) (subst-x ((x : v) ...) (e_0 e_1 ...)))]
  [(subst-x ((x : v) ...) (e e_0))
   ((subst-x ((x : v) ...) e) (subst-x ((x : v) ...) e_0))]
  [(subst-x ((x : v) ...) (e_1 a-op e_2))
   ((subst-x ((x : v) ...) e_1) a-op (subst-x ((x : v) ...) e_2))]
  [(subst-x ((x : v) ...) (e_1 b-op1 e_2))
   ((subst-x ((x : v) ...) e_1) b-op1 (subst-x ((x : v) ...) e_2))]
  [(subst-x ((x : v) ...) (e_1 b-op2 e_2))
   ((subst-x ((x : v) ...) e_1) b-op2 (subst-x ((x : v) ...) e_2))]
  [(subst-x ((x_1 : v_1) ... (x : v) (x_2 : v_2) ...) x)
   v]
  [(subst-x ((x : v) (x_1 : v_1) ...) x_2)
   (subst-x ((x_1 : v_1) ...) x_2)]
  [(subst-x ((x : v)) x_2)
   x_2]
  
  ;[(subst-x ((x : v) ... ((x_0 : v_0))...) e)
   ;(subst-x ((x : v) ... (x_0 : v_0)...) e)]
  [(subst-x ((x : v) ...) x_1) x_1]
  [(subst-x ((x : v) ...) v_1) v_1]
  [(subst-x ((x : v) ...) (e)) e]
  [(subst-x ((x : v) ...) e) e]
  
  )

(define-metafunction Flint
  subst-e : a any -> any
  [(subst-e a self) a]
  [(subst-e a (self -> x)) (a -> x)]
  [(subst-e a (if (e_1) {e_2} else {e_3}))
   (if ((subst-e a e_1)) {(subst-e a e_2)} else {(subst-e a e_3)})]
  [(subst-e a (var x : t = e))
   (var x : t = (subst-e a e))]
  [(subst-e a (let x : t = e))
   (let x : t = (subst-e a e))]
  [(subst-e a (e_0 [e_1 :: e_2]))
   ((subst-e a e_0) [(subst-e a e_1) :: (subst-e a e_2)])]
  [(subst-e a (e_0 [e_1 ::]))
   ((subst-e a e_0) [(subst-e a e_1) ::])]
  [(subst-e a (C -> init ((x : e) ...) -> a))
   (C -> init (subst-e a ((x : e) ...)) -> a)]
  [(subst-e a (f ((x : e_2)...)))
   (a -> f (subst-e a ((x : e_2) ...)))]
  [(subst-e a (e_1 -> f ((x : e_2)...)))
   ((subst-e a e_1) -> f (subst-e a ((x : e_2) ...)))]
  [(subst-e a (try ? (e_1 -> f ((x : e_2)...))))
   (try ? ((subst-e a e_1) -> f (subst-e a ((x : e_2) ...))))]
  [(subst-e a (a -> f ((x : e_2)...) -> sender (a_1)))
   (a -> f (subst-e a ((x : e_2) ...)) -> sender (a_1))]
  [(subst-e a (call C -> f ((x : e)...)))
   (call C -> f (subst-e a ((x : e) ...)))]
  [(subst-e a (e -> x))
   ((subst-e a e) -> x)]
  [(subst-e a (e_1 -> x = e_2))
   ((subst-e a e_1) -> x = (subst-e a e_2))]
  [(subst-e a (x = e))
   (x = (subst-e a e))]
  [(subst-e a (return e))
   (return (subst-e a e))]
  [(subst-e a (e e_0 e_1 ...))
   ((subst-e a e) (subst-e a (e_0 e_1 ...)))]
  [(subst-e a (e_0 a-op e_1))
   ((subst-e a e_0) a-op (subst-e a e_1))]
  [(subst-e a (e_0 b-op1 e_1))
   ((subst-e a e_0) b-op1 (subst-e a e_1))]
  [(subst-e a (e_0 b-op2 e_1))
   ((subst-e a e_0) b-op2 (subst-e a e_1))]
  [(subst-e a ((x : v)))
   (subst-e a (x : v))]
  [(subst-e a ((x : e) ...))
   ((x : (subst-e a e)) ...)]
  [(subst-e a x) x]
  [(subst-e a v) v]
 
  [(subst-e a (e)) (subst-e a e)]
  [(subst-e a e) e]
  
  )

(define-judgment-form Flint
  #:mode (subsequence I I)
  #:contract (subsequence (tss ...) (tss ...))

  [----------------------------------------------
   (subsequence (tss_1 )
                (tss_2 ... tss_1  tss_3 ...))]
  

  [(subsequence (tss_1 ...)
                (tss_2 ... tss_0 tss_3 ...))
   
   ----------------------------------------------
   (subsequence (tss_0 tss_1 ...)
                (tss_2 ... tss_0 tss_3 ...))])

(define-judgment-form Flint
  #:mode (ain I I)
  #:contract (ain env-ß a)
  [------------------
   (ain ((a -> (C varmap_1 ... n_1) -> varmap_2 ... -> varmap_3 ...)) a)]
  [------------------
   (ain (ß-v ... (a -> (C varmap_1 ... n_1) -> varmap_2 ... -> varmap_3 ...)) a)]
  [(ain (ß-v ... ) a)
   ------------------
   (ain (ß-v ... (a_0 -> (C varmap_1 ... n_1) -> varmap_2 ... -> varmap_3 ...)) a)])

(define-judgment-form Flint
  #:mode (anotin I I O)
  #:contract (anotin env-ß a boolean)

  [-------------------------
   (anotin () a #f)]
  [-------------------------
   (anotin (ß-v_0 ... (a -> (C varmap_1 ... n_1) -> varmap_2 ... -> varmap_3 ...) ) a #t)]
  [-------------------------
   (anotin ((a_0 -> (C varmap_1 ... n_1) -> varmap_2 ... -> varmap_3 ...)) a #f)]
  [(anotin (ß-v ß-v_0 ...) a boolean)
   -------------------------
   (anotin (ß-v ß-v_0 ... (a_0 -> (C varmap_1 ... n_1) -> varmap_2 ... -> varmap_3 ...) ) a boolean)]



 #| [-------------------------
   (anotin ((a -> (C varmap_1 ... n_1) -> varmap_2 ... -> varmap_3 ...)) a #t)]
  
  [-------------------------
   (anotin ((a_0 -> (C varmap_1 ... n_1) -> varmap_2 ... -> varmap_3 ...)) a #f)]

  [-------------------------
   (anotin (ß-v_0 ß-v... (a -> (C varmap_1 ... n_1) -> varmap_2 ... -> varmap_3 ...)) a #t)]

  [(anotin (ß-v ß-v_0 ...) a boolean)
   -------------------------
   (anotin (ß-v ß-v_0 ... (a_0 -> (C varmap_1 ... n_1) -> varmap_2 ... -> varmap_3 ...) ) a boolean)]
  |#
  )

;(traces s->ßs (term ( (if (true) {1} else {2}) () () () ())))
;(traces s->ßs (term ( (if (false) {1} else {2}) () () () ())))
;(traces s->ßs (term ( (if (true) {(1 + 2)} else {2}) () () () ())))
;(traces s->ßs (term ( (if (true) {(let x : Bool = true)} else {2}) () () () ((contract EOA () {} (EOA @ () :: () {(public func f () -> Bool {return true})}))))))

;(traces s->ßs (term ( (EOA -> init () -> aEOA) () () () ((contract EOA () {} (EOA @ () :: () {(public func f () -> Bool {return true})}))))))
;(traces s->ßs (term ( (EOA -> init () -> aEOA) () () () ((contract EOA () {} (EOA :: () {(public init () {3})}) (EOA @ () :: () {(public func f () -> Bool {return true})}))))))

;(traces s->ßs (term ( (EOA -> init () -> aEOA) () () () ((contract EOA () {(var x : Bool = 5)} (EOA :: () {(public init () {5})}) (EOA @ () :: () {(public func f () -> Bool {return true})}))))))
;(traces s->ßs (term ( (Counter -> init () -> aCounter) () () () ((contract Counter () {(let x : Bool = 5)} (Counter :: () {(public init () {5})}) (EOA @ () :: () {(public func f () -> Bool {return true})}))))))
;(traces s->ßs (term ( ((Counter -> init () -> aCounter) (Counter -> g ())) () () (a) ((contract Counter (a b) {(var value : Int = 0)} (Counter :: () {(public init () {}) (public func f () -> Bool {return true})}) (Counter @ (a) :: () {(public func g () -> Bool {return true})} ) )))))(traces s->ßs (term ( ((Counter -> init () -> aCounter) (Counter -> g ())) () () (a) ((contract Counter (a b) {(var value : Int = 0)} (Counter :: () {(public init () {}) (public func f () -> Bool {return true})}) (Counter @ (a) :: () {(public func g () -> Bool {return true})} ) )))))

;call e protection blocks
;(traces s->ßs (term ( ((Counter -> init () -> aCounter) (Counter -> g ())) () () () ((contract Counter (a b) {(var value : Int = 0)} (Counter :: () {(public init () {}) (public func f () -> Bool {return true})}) (Counter @ (a) :: () {(public func g () -> Bool {return value})} ) )))))
;(traces s->ßs (term ( ((Counter -> init () -> aCounter) (Counter -> f ((x : 5)))) () () (a) ((contract Counter (a b) {(var value : Int = 0)} (Counter :: () {(public init () {}) (public func f ((x : Int)) -> Bool {return true})}) (Counter @ (a) :: () {(public func g () -> Bool {return value})} ) )))))
;(traces s->ßs (term ( ((Counter -> init () -> aCounter) (Counter -> g ())) () () (a) ((contract Counter (a b) {(var value : Int = 0)} (Counter :: () {(public init () {}) (public func f () -> Bool {return true})}) (Counter @ (anystate) :: () {(public func g () -> Bool {return value})} ) )))))
;(traces s->ßs (term ( ((Counter -> init () -> aCounter) (Counter -> g () -> sender (aCounter))) () () (a) ((contract Counter (a b) {(var value : Int = 0)} (Counter :: () {(public init () {}) (public func f () -> Bool {return true})}) (Counter @ (a) :: () {(public func g () -> Bool {return value})} ) )))))
;(traces s->ßs (term ( ((Counter -> init () -> aCounter) (Counter -> g () -> sender (hjfshs))) () () (a) ((contract Counter (a b) {(var value : Int = 0)} (Counter :: () {(public init () {}) (public func f () -> Bool {return true})}) (Counter @ (anystate) :: () {(public func g () -> Bool {return value})} ) )))))
;(traces s->ßs (term ( ((Counter -> init () -> aCounter) (Counter -> f ((x : 5)) -> sender (dfhjbd))) () () (a) ((contract Counter (a b) {(var value : Int = 0)} (Counter :: () {(public init () {}) (public func f ((x : Int)) -> Bool {return true})}) (Counter @ (a) :: () {(public func g () -> Bool {return value})} ) )))))

;self
;(traces s->ßs (term ( ((Counter -> init () -> aCounter) (Counter -> g ())) () () (a) ((contract Counter (a b) {(var value : Int = 0)} (Counter :: () {(public init () {}) (public func f () -> Bool {return true})}) (Counter @ (a) :: () {(public func g () -> Bool {return (self -> value)})} ) )))))

;assign
;(traces s->ßs (term ( ((Counter -> init () -> aCounter) (Counter -> g () -> sender (aCounter))) () () (a) ((contract Counter (a b) {(var value : Int = 0)} (Counter :: () {(public init () {}) (public func f () -> Bool {return true})}) (Counter @ (a) :: () {(public func g () -> Bool {return (self -> value = 7)})} ) )))))
;(traces s->ßs (term ( ((Counter -> init () -> aCounter) (Counter -> g () -> sender (aCounter))) () () (a) ((contract Counter (a b) {(var value : Int = 0)} (Counter :: () {(public init () {}) (public func f () -> Bool {return true})}) (Counter @ (a) :: () {(public func g () -> Bool {return (value = 7)})} ) )))))

;change func syntax (remove C ->)
;(traces s->ßs (term ( ((Counter -> init () -> aCounter) (g () -> sender (aCounter))) () () (a) ((contract Counter (a b) {(var value : Int = 0)} (Counter :: () {(public init () {}) (public func f () -> Bool {return true})}) (Counter @ (a) :: () {(public func g () -> Bool {return (self -> value = 7)})} ) )))))
;(traces s->ßs (term ( ((Counter -> init () -> aCounter) (g () -> sender (aCounter))) () () (a) ((contract Counter (a b) {(let value : Int = 0)} (Counter :: () {(public init () {}) (public func f () -> Bool {return true})}) (Counter @ (a) :: () {(public func g () -> Bool {return (value = 7)})} ) )))))
;(traces s->ßs (term ( ((Counter -> init () -> aCounter) (g () -> sender (aCounter))) () () (a) ((contract Counter (a b) {(var value : Int = 0)} (Counter :: () {(public init () {}) (public func f () -> Bool {return true})}) (Counter @ (a) :: () {(public func g () -> Bool {return (value = 7)})} ) )))))

;caller groups
;(traces s->ßs (term ( ((Counter -> init () -> aCounter) (g ())) () (aCounter) (a) ((contract Counter (a b) {(var value : Int = 0) (var manager : Address = aCounter)} (Counter :: () {(public init () {}) (public func f () -> Bool {return true})}) (Counter @ (a) :: (manager) {(public func g () -> Bool {return (value = 7)})} ) )))))
;(traces s->ßs (term ( ((Counter -> init () -> aCounter) (g ())) () (aCounter) (a) ((contract Counter (a b) {(var value : Int = 0) (let manager : Address = aCounter)} (Counter :: () {(public init () {}) (public func f () -> Bool {return true})}) (Counter @ (a) :: (manager) {(public func g () -> Bool {return (value = 7)})} ) )))))
;(traces s->ßs (term ( ((Counter -> init () -> aCounter) (g ())) () (aCounter) (a) ((contract Counter (a b) {(var value : Int = 0) (let manager : Address = aCounter)} (Counter :: () {(public init () {}) (public func f () -> Bool {return true})}) (Counter @ (a) :: (gsds any_caller) {(public func g () -> Bool {return (value = 7)})} ) )))))

;added a->f ...
;(traces s->ßs (term ( ((Counter -> init () -> aCounter) (aCounter -> g ())) () (am) (a) ((contract Counter (a b) {(var value : Int = 0) (let manager : Address = am)} (Counter :: (any_caller) {(public init () {}) (public func f () -> Bool {return true})}) (Counter @ (a) :: (manager) {(public func g () -> Bool {return (value = 7)})} ) )))))
;(traces s->ßs (term ( ((Counter -> init () -> aCounter) (aCounter -> g ())) () (aCounter) (a) ((contract Counter (a b) {(var value : Int = 0) (let manager : Address = aCounter)} (Counter :: (any_caller) {(public init () {}) (public func f () -> Bool {return true})}) (Counter @ (a) :: (manager) {(public func g () -> Bool {return (value = 7)})} ) )))))
;(traces s->ßs (term ( ((Counter -> init () -> aCounter) (aCounter -> g () -> sender (am))) () () (a) ((contract Counter (a b) {(var value : Int = 0) (let manager : Address = am)} (Counter :: (any_caller) {(public init () {}) (public func f () -> Bool {return true})}) (Counter @ (a) :: (manager) {(public func g () -> Bool {return (value = 7)})} ) )))))
;(traces s->ßs (term ( ((Counter -> init () -> aCounter) (aCounter -> g () -> sender (am))) () () (a) ((contract Counter (a b) {(var value : Int = 0) (let manager : Address = am)} (Counter :: (any_caller) {(public init () {}) (public func f () -> Bool {return true})}) (Counter @ (a) :: (manager) {(public func g () -> Bool { (f ()) return (value = 7)})} ) )))))

#|(traces s->ßs (term ( ((TrafficLights -> init () -> aTL) (aTL -> moveToAmber () -> sender (aTL)) (aTL -> moveToGreen () -> sender (aTL)) (aTL -> moveToAmber () -> sender (aTL))) () () () (
       (contract TrafficLights (Red Amber Green) {
          (var signal : Int = 0)}
          (TrafficLights :: (any_caller) {
            (public init () {(become Red)})
            (public func getSignal () -> Int {return signal})})
          (TrafficLights @ (Red Green) :: (any_caller) {
             (public func moveToAmber () -> Void {(signal = 1) (become Amber) return unit })})
          (TrafficLights @ (Amber) :: (any_caller) {
             (public func moveToGreen () -> Void {(signal = 2) (become Green) return unit})
             (public func moveToRed () -> Void {(signal = 0) (become Red) return unit})}))))))|#

#|(traces s->ßs (term ( ((RockPaperScissors -> init () -> aRPS) (aRPS -> leftWins ((left : 0) (right : 2)) -> sender (aRPS)) (aRPS -> leftWins ((left : 2) (right : 1)) -> sender (aRPS))) () () () (
       (contract RockPaperScissors () {
          (var winner : Bool)}
          (RockPaperScissors :: (any_caller) {
            (public init () {(winner = false)})
            (public func leftWins ((left : Int) (right : Int)) -> Int {(var outcome : Int = ((3 + left) - right)) (winner = ((outcome % 3) == 1)) return winner})})
          )))))|#

#|(traces s->ßs (term ( ((Rectangle -> init ((width : 9) (height : 5)) -> aR) (aR -> changeArea ((width : 4) (height : 9)) -> sender (aR) )) () () () (
       (contract Rectangle () {
          (var width : Int)
          (var height : Int)}
          (Rectangle :: (any_caller) {
            (public init ((width : Int) (height : Int)) {(self -> width =  width) (self -> height = height)})
            (public func changeWidth ((width : Int)) -> Void {(self -> width = width) return unit})
            (public func changeHeight ((height : Int)) -> Void {(self -> height = height) return unit})
            (public func changeArea ((width : Int) (height : Int)) -> Int {(self -> width = width) (self -> height = height) return ((self -> width) * (self -> height))} )})
          
          )))))|#


;(traces s->ßs (term ( ((Auction -> init ((owner : aOwner)) -> aAuction) (aAuction -> endAuction () -> sender (aOwner))) () () () ((contract Auction (auctionEnded auctionRunning) { (var owner : Address) (var ended : Bool) (var highestBid : Int) (var highestBidder : Address)} (Auction :: (any_caller) {(public init ((owner : Address)) {(self -> owner = owner) (self -> ended = false) (self -> highestBid = 0) (self -> highestBidder = aNull) (become auctionRunning)}) }) (Auction @ (auctionRunning) :: (owner) {(public func endAuction () -> Void { (self -> ended = true) (become auctionEnded) return unit})} ) )))))

;(traces s->ßs (term ( ((Auction -> init ((owner : aOwner)) -> aAuction) (aAuction -> bid ((bid : 9) (bidder : aC1)) -> sender (aOwner)) (aAuction -> getHBid () -> sender (aOwner))) () () () ((contract Auction (auctionEnded auctionRunning) { (var owner : Address) (var ended : Bool) (var highestBid : Int) (var highestBidder : Address)} (Auction :: (any_caller) {(public init ((owner : Address)) {(self -> owner = owner) (self -> ended = false) (self -> highestBid = 0) (self -> highestBidder = aNull) (become auctionRunning)}) (public func getHBidder () -> Address {return (self -> highestBidder)}) (public func getHBid () -> Int {return (self -> highestBid)})}) (Auction @ (auctionRunning) :: (owner) {(public func endAuction () -> Void { (self -> ended = true) (become auctionEnded) return unit})} ) (Auction @ (auctionRunning) :: (any_caller) {(public func bid ((bid : Int) (bidder : Address)) -> Int {(if ((bid > (self -> highestBid))) {(if ((bidder != (self -> highestBidder))) {((self -> highestBid = bid) (self -> highestBidder = bidder))} else {unit})} else {unit}) return bid})}) )))))


#|(traces s->ßs (term ( ((Auction -> init ((owner : aOwner)) -> aAuction) (Client -> init ((auction : aAuction)) -> aC1) (aC1 -> bid ((bid : 8)) -> sender (aC1)) ) () () () (
           (contract Auction (auctionEnded auctionRunning)
                     { (var owner : Address) (var ended : Bool) (var highestBid : Int) (var highestBidder : Address)}
                     (Auction :: (any_caller) {
                        (public init ((owner : Address)) {(self -> owner = owner) (self -> ended = false) (self -> highestBid = 0) (self -> highestBidder = aNull) })
                        (public func getHBidder () -> Address {return (self -> highestBidder)})
                        (public func getHBid () -> Int {return (self -> highestBid)})
                        (public func hasEnded () -> Bool {return (self -> ended)})})
                     (Auction @ (auctionRunning) :: (owner) {(public func endAuction () -> Void { (self -> ended = true)  return unit})} )
                     (Auction @ (anystate) :: (any_caller) {(public func bid ((bid : Int) (bidder : Address)) -> Address {(if ((bid > (self -> highestBid))) {(if ((bidder != (self -> highestBidder))) {((self -> highestBid = bid) (self -> highestBidder = bidder))} else {unit})} else {unit}) return (self -> highestBidder)})}) )           
           (contract Client (canBid canWithdraw won isHB) {
          (var auction : Address) (var bid : Int = 0)}
          (Client :: (any_caller) {
            (public init ((auction : Address)) {(self -> auction = auction) (become canBid)})
            (public func hasEnded () -> Bool {return ((self -> auction) -> ended)})})
          (Client @ (canBid) :: (any_caller) {
            (public func bid ((bid : Int)) -> Int {((self -> auction) -> bid ((bid : bid) (bidder : (self -> auction)))) return bid})})
          )))))|#

#|(traces s->ßs (term ( ((Auction -> init ((owner : aOwner)) -> aAuction) (Client -> init ((auction : aAuction)) -> aC1) (aC1 -> bid ((bid : 8)) -> sender (aC1)) ) () () () (
           (contract Auction (anystate auctionEnded auctionRunning)
                     { (var owner : Address) (var ended : Bool) (var highestBid : Int) (var highestBidder : Address)}
                     (Auction :: (any_caller) {
                        (public init ((owner : Address)) {(self -> owner = owner) (self -> ended = false) (self -> highestBid = 0) (self -> highestBidder = aNull) (become auctionRunning)})
                        (public func getHBidder () -> Address {return (self -> highestBidder)})
                        (public func getHBid () -> Int {return (self -> highestBid)})
                        (public func hasEnded () -> Bool {return (self -> ended)})})
                     (Auction @ (auctionRunning) :: (owner) {(public func endAuction () -> Void { (self -> ended = true)  return unit})} )
                     (Auction @ (auctionRunning) :: (any_caller) {(public func bid ((bid : Int) (bidder : Address)) -> Address {(if ((bid > (self -> highestBid))) {(if ((bidder != (self -> highestBidder))) {((self -> highestBid = bid) (self -> highestBidder = bidder))} else {unit})} else {unit}) return (self -> highestBidder)}) (public func bid2 () -> Void {return unit})}) )           
           (contract Client (canBid canWithdraw won isHB) {
          (var auction : Address) (var bid : Int = 0)}
          (Client :: (any_caller) {
            (public init ((auction : Address)) {(self -> auction = auction) (become canBid)})
            (public func hasEnded () -> Bool {return ((self -> auction) -> ended)})})
          (Client @ (canBid) :: (any_caller) {
            (public func bid ((bid : Int)) -> Int {(self -> bid = bid) ((self -> auction) -> bid ((bid : bid) (bidder : self))) (become isHB) return bid})})
          )))))|#


#|(traces s->ßs (term ( ((Auction -> init ((owner : aOwner)) -> aAuction) (Client -> init ((auction : aAuction)) -> aC1) (Client -> init ((auction : aAuction)) -> aC2) (aC1 -> bid ((bid : 8)) -> sender (aC1)) (aC2 -> bid ((bid : 8)) -> sender (aC2)) (aC2 -> withdraw () -> sender (aC2)) (aC2 -> bid ((bid : 10)) -> sender (aC2)) (aAuction -> endAuction () -> sender (aOwner)) (aC1 -> isHB () -> sender (aC1)) (aC1 -> withdraw () -> sender (aC1)) (aC2 -> isHB () -> sender (aC2)) (aC2 -> won () -> sender (aC2)) ) () () () (
           (contract Auction (anystate auctionEnded auctionRunning)
                     { (var owner : Address) (var ended : Bool) (var highestBid : Int) (var highestBidder : Address)}
                     (Auction :: (any_caller) {
                        (public init ((owner : Address)) {(self -> owner = owner) (self -> ended = false) (self -> highestBid = 0) (self -> highestBidder = aNull) (become auctionRunning)})
                        (public func getHBidder () -> Address {return (self -> highestBidder)})
                        (public func getHBid () -> Int {return (self -> highestBid)})
                        (public func hasEnded () -> Bool {return (self -> ended)})
                        (public func withdraw ((bidder : Address)) -> Bool {return (if ((bidder != (self -> highestBidder))) {true} else {false})})
                        })
                     (Auction @ (auctionRunning) :: (owner) {
                        (public func endAuction () -> Void { (self -> ended = true) (become auctionEnded)  return unit})} )
                     (Auction @ (auctionRunning) :: (any_caller) {
                        (public func bid ((bid : Int) (bidder : Address)) -> Address {
                           (if ((bid > (self -> highestBid))) {(if ((bidder != (self -> highestBidder))) {((self -> highestBid = bid) (self -> highestBidder = bidder))} else {unit})} else {unit})
                           return (self -> highestBidder)}) })
                     (Auction @ (auctionEnded) :: (any_caller) {
                        (public func win ((bidder : Address)) -> Bool {return (if ((bidder == (self -> highestBidder))) {true} else {false})})})
                     )           
           (contract Client (canBid canWithdraw won lost isHB ended) {
          (var auction : Address) (var bid : Int = 0)}
          (Client :: (any_caller) {
            (public init ((auction : Address)) {(self -> auction = auction) (become canBid)})
            (public func hasEnded () -> Bool {return ((self -> auction) -> ended)})
            })
          (Client @ (canBid) :: (any_caller) {
            (public func bid ((bid : Int)) -> Int {(self -> bid = bid) (if ((((self -> auction) -> bid ((bid : bid) (bidder : self))) == self)) {(become isHB)} else {(become canWithdraw)})  return bid})})
          (Client @ (canWithdraw) :: (any_caller) {
            (public func withdraw () -> Void { ((self -> auction) -> withdraw ((bidder : self))) (if (((self -> auction) -> hasEnded ())) {(become lost)} else {(become canBid)}) return unit})})
          (Client @ (isHB) :: (any_caller) {
            (public func isHB () -> Bool {return (if ((((self -> auction) -> getHBidder ()) == self)) {(if (((self -> auction) -> hasEnded ())) {((become won) (true))} else {true})} else {((become canWithdraw) (false))})})})
          (Client @ (won) :: (any_caller) {
            (public func won () -> Bool {return (if (((self -> auction) -> win ((bidder : self)))) {(become ended)} else {false})})})
          )))))



(traces s->ßs (term ( ((BlockKing -> init ((warrior : aBK) (warriorGold : 3)) -> aBK) (EOC -> init () -> aC) (aBK -> enter ((warrior : aC) (warriorGold : 3)) -> sender (aC)) (aBK -> process_payment () -> sender (aC))) () () () (
           (contract BlockKing (waiting canEnter)
                     { (var warrior : Address) (var warriorGold : Int) (var king : Address)}
                     (BlockKing :: (any_caller) {
                        (public init ((warrior : Address) (warriorGold : Int)) {(self -> warrior = warrior) (self -> warriorGold = warriorGold) (self -> king = warrior) (become canEnter)})
                        
                        })
                     (BlockKing @ (canEnter) :: (any_caller) {
                        (public func enter ((warrior : Address) (warriorGold : Int)) -> Void { (self -> warrior = warrior) (self -> warriorGold = warriorGold) (become waiting)  return unit})} )
                     (BlockKing @ (waiting) :: (any_caller) {
                        (public func process_payment () -> Void {
                           (self -> king = (self -> warrior)) (become canEnter)
                           return unit}) })
                     
                     )
           (contract EOC () {} (EOC :: (any_caller) {(public init () {})}))
           ))))

;; 2 enters
(traces s->ßs (term ( ((BlockKing -> init ((warrior : aBK) (warriorGold : 3)) -> aBK) (EOC -> init () -> aC) (aBK -> enter ((warrior : aC) (warriorGold : 3)) -> sender (aC)) (aBK -> enter ((warrior : aB) (warriorGold : 5)) -> sender (aC)) (aBK -> process_payment () -> sender (aC))) () () () (
           (contract BlockKing (waiting canEnter)
                     { (var warrior : Address) (var warriorGold : Int) (var king : Address)}
                     (BlockKing :: (any_caller) {
                        (public init ((warrior : Address) (warriorGold : Int)) {(self -> warrior = warrior) (self -> warriorGold = warriorGold) (self -> king = warrior) (become canEnter)})
                        
                        })
                     (BlockKing @ (canEnter) :: (any_caller) {
                        (public func enter ((warrior : Address) (warriorGold : Int)) -> Void { (self -> warrior = warrior) (self -> warriorGold = warriorGold) (become waiting)  return unit})} )
                     (BlockKing @ (waiting) :: (any_caller) {
                        (public func process_payment () -> Void {
                           (self -> king = (self -> warrior)) (become canEnter)
                           return unit}) })
                     
                     )
           (contract EOC () {} (EOC :: (any_caller) {(public init () {})}))
           ))))


(traces s->ßs (term ( ((EtherStore -> init ((Owner : aOwner) (Creator : aOwner) (price : 8)) -> aES) (aES -> foo ((newOwner : aAlice)) -> sender (aES))) () () () (
           (contract EtherStore (anystate)
                     { (var Owner : Address) (var Creator : Address) (var price : Int)}
                     (EtherStore :: (any_caller) {
                        (public init ((Owner : Address) (Creator : Address) (price : Int)) {(self -> Owner = Owner) (self -> Creator = Creator) (self -> price = price) })
                        (public func foo ((newOwner : Address)) -> Address {return (self -> Owner = newOwner)})
                        (public func bar ((price : Int)) -> Int {return (this -> price = price)})
                        })
                     )
           (contract EOC () {} (EOC :: (any_caller) {(public init () {})}))
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

(traces s->ßs (term ( ((EtherStore -> init ((balances : ()) (Owner : aOwner) (Creator : aOwner) (price : 8)) -> aES) (aES -> foo ((newOwner : aAlice)) -> sender (aES)) (aES -> bar ((price : 5) (caller : aAlice)) -> sender (aES))) () () () (
           (contract EtherStore (anystate)
                     {(var balances : (Address : Int)) (var Owner : Address) (var Creator : Address) (var price : Int)}
                     (EtherStore :: (any_caller) {
                        (public init ((balances : (Address : Int)) (Owner : Address) (Creator : Address) (price : Int)) {(self -> balances = balances) (self -> Owner = Owner) (self -> Creator = Creator) (self -> price = price) })
                        (public func foo ((newOwner : Address)) -> Address {return (self -> Owner = newOwner)})
                        (public func bar ((price : Int) (caller : Address)) -> Int {(self -> price = price) return (self -> balances = ((self -> balances) [caller : (((self -> balances)[caller :]) + price)]))})
                        })
                     )
           (contract EOC () {} (EOC :: (any_caller) {(public init () {})}))
           ))))

(traces s->ßs (term ( ((Counter -> init () -> aCounter) (aCounter -> set ((value : 3)) -> sender (aCounter)) (aCounter -> get () -> sender (aCounter)) ) () () () (
           (contract Counter (canSet cannotSet)
                     { (var balance : Int = 0) }
                     (Counter :: (any_caller) {
                        (public init () {(become canSet)})
                        (public func get () -> Int {return (self -> balance)})
                        })
                     (Counter @ (canSet) :: (any_caller) {
                        (public func set ((value : Int)) -> Int {(become cannotSet) (var t : Int = (self -> balance)) (self -> balance = value) (become canSet) return t})
                        })
                     )
           (contract EOC () {} (EOC :: (any_caller) {(public init () {})}))
           ))))

(traces s->ßs (term ( ((BlockKing -> init ((warrior : aBK) (warriorGold : 3)) -> aBK) (EOC -> init () -> aC) (aBK -> enter ((warrior : aC) (warriorGold : 3)) -> sender (aC)) (aBK -> __callback () -> sender (aO))) () () () (
           (contract BlockKing (waiting canEnter processing)
                     { (var warrior : Address) (var warriorGold : Int) (var king : Address) (var Oraclize : Address = aO)}
                     (BlockKing :: (anycaller) {
                        (public init ((warrior : Address) (warriorGold : Int)) {(self -> warrior = warrior) (self -> warriorGold = warriorGold) (self -> king = warrior) (become canEnter)})
                        
                        })
                     (BlockKing @ (canEnter) :: (anycaller) {
                        (public func enter ((warrior : Address) (warriorGold : Int)) -> Void { (self -> warrior = warrior) (self -> warriorGold = warriorGold) (become waiting)  return unit})} )
                     (BlockKing @ (waiting) :: (Oraclize) {
                        (public func __callback () -> Void {
                            (become processing) (process_payment ()) return unit})
                        })
                     (BlockKing @ (processing) :: (anycaller) {
                        (public func process_payment () -> Void {
                           (self -> king = (self -> warrior)) (become canEnter)
                           return unit}) 
                                                                })
                     )
           (contract EOC () {} (EOC :: (any_caller) {(public init () {})}))
           ))))




;latex
(traces s->ßs (term ( (
                         (BlockKing -> init ((warrior : aBK) (warriorGold : 3)) -> aBK)
                         (aBK -> enter ((warrior : aC) (warriorGold : 3)) -> sender (aC))
                         (aBK -> __callback () -> sender (aO))) () () () (
           (contract BlockKing (waiting canEnter processing)
                     { (var warrior : Address)
                       (var warriorGold : Int)
                       (var king : Address)
                       (var Oraclize : Address = aO)}
                     (BlockKing :: (anycaller) {
                        (public init ((warrior : Address) (warriorGold : Int)) {
                            (self -> warrior = warrior)
                            (self -> warriorGold = warriorGold)
                            (self -> king = warrior)
                            (become canEnter)})
                        })
                     (BlockKing @ (canEnter) :: (anycaller) {
                        (public func enter ((warrior : Address) (warriorGold : Int)) -> Void {
                            (self -> warrior = warrior)
                            (self -> warriorGold = warriorGold)
                            (become waiting)
                            return unit})} )
                     (BlockKing @ (waiting) :: (Oraclize) {
                        (public func __callback () -> Void {
                            (become processing)
                            (process_payment ())
                            return unit})
                        })
                     (BlockKing @ (processing) :: (anycaller) {
                        (public func process_payment () -> Void {
                           (self -> king = (self -> warrior))
                           (become canEnter)
                           return unit}) 
                      })
                     )
           ))))


(traces s->ßs (term ( ((Counter -> init () -> aCounter)
                         (aCounter -> set ((value : 3)) -> sender (aCounter))
                         (aCounter -> get () -> sender (aCounter)) )
           ()
           ()
           () (
           (contract Counter (canSet cannotSet)
                     { (var balance : Int = 0) }
                     (Counter :: (anycaller) {
                        (public init () {
                          (become canSet)})
                        (public func get () -> Int {
                          return (self -> balance)})
                        })
                     (Counter @ (canSet) :: (anycaller) {
                        (public func set ((value : Int)) -> Int {
                          (become cannotSet)
                          (var t : Int = (self -> balance))
                          (self -> balance = value)
                          (become canSet)
                          return t})
                        })
                     )
           ))))

(traces s->ßs (term ( ((Auction -> init ((owner : aOwner)) -> aAuction) (Client -> init ((auction : aAuction)) -> aC1) (Client -> init ((auction : aAuction)) -> aC2) (aC1 -> bid ((bid : 8)) -> sender (aC1)) (aC2 -> bid ((bid : 8)) -> sender (aC2)) (aC2 -> withdraw () -> sender (aC2)) (aC2 -> bid ((bid : 10)) -> sender (aC2)) (aAuction -> endAuction () -> sender (aOwner)) (aC1 -> isHB () -> sender (aC1)) (aC1 -> withdraw () -> sender (aC1)) (aC2 -> isHB () -> sender (aC2)) (aC2 -> won () -> sender (aC2)) ) () () () (
           (contract Auction (anystate auctionEnded auctionRunning)
                     {(var store : (Address : Int)) (var owner : Address) (var ended : Bool) (var highestBid : Int) (var highestBidder : Address)}
                     (Auction :: (anycaller) {
                        (public init ((owner : Address)) {(self -> owner = owner) (self -> ended = false) (self -> highestBid = 0) (self -> highestBidder = aNull) (self -> store = ())(become auctionRunning)})
                        (public func getHBidder () -> Address {return (self -> highestBidder)})
                        (public func getHBid () -> Int {return (self -> highestBid)})
                        (public func hasEnded () -> Bool {return (self -> ended)})
                        (public func withdraw ((bidder : Address)) -> Bool {return (if ((bidder != (self -> highestBidder))) {((self -> store = ((self -> store)[bidder :: 0])) (true))} else {false})})
                        })
                     (Auction @ (auctionRunning) :: (owner) {
                        (public func endAuction () -> Void { (self -> ended = true) (become auctionEnded)  return unit})} )
                     (Auction @ (auctionRunning) :: (anycaller) {
                        (public func bid ((bid : Int) (bidder : Address)) -> Address {
                           (if ((bid > (self -> highestBid))) {(if ((bidder != (self -> highestBidder))) {((self -> highestBid = bid) (self -> highestBidder = bidder) (self -> store = ((self -> store)[bidder :: bid])))} else {unit})} else {unit})
                           return (self -> highestBidder)}) })
                     (Auction @ (auctionEnded) :: (anycaller) {
                        (public func win ((bidder : Address)) -> Bool {return (if ((bidder == (self -> highestBidder))) {((self -> store = ((self -> store)[bidder :: 0])) (true))} else {false})})})
                     )           
           (contract Client (canBid canWithdraw won lost isHB ended) {
          (var auction : Address) (var bid : Int = 0)}
          (Client :: (anycaller) {
            (public init ((auction : Address)) {(self -> auction = auction) (become canBid)})
            (public func hasEnded () -> Bool {return ((self -> auction) -> ended)})
            })
          (Client @ (canBid) :: (anycaller) {
            (public func bid ((bid : Int)) -> Int {(self -> bid = bid) (if ((((self -> auction) -> bid ((bid : bid) (bidder : self))) == self)) {(become isHB)} else {(become canWithdraw)})  return bid})})
          (Client @ (canWithdraw) :: (anycaller) {
            (public func withdraw () -> Void { ((self -> auction) -> withdraw ((bidder : self))) (if (((self -> auction) -> hasEnded ())) {(become lost)} else {(become canBid)}) return unit})})
          (Client @ (isHB) :: (anycaller) {
            (public func isHB () -> Bool {return (if ((((self -> auction) -> getHBidder ()) == self)) {(if (((self -> auction) -> hasEnded ())) {((become won) (true))} else {true})} else {((become canWithdraw) (false))})})})
          (Client @ (won) :: (anycaller) {
            (public func won () -> Bool {return (if (((self -> auction) -> win ((bidder : self)))) {(become ended)} else {false})})})
          )))))
(traces s->ßs (term ( ((Auction -> init ((owner : aOwner)) -> aAuction) (Client -> init ((auction : aAuction)) -> aC1) (Client -> init ((auction : aAuction)) -> aC2) (aC1 -> bid ((bid : 8)) -> sender (aC1)) (aC2 -> bid ((bid : 8)) -> sender (aC2)) (aC2 -> withdraw () -> sender (aC2)) (aC2 -> bid ((bid : 10)) -> sender (aC2)) (aAuction -> endAuction () -> sender (aOwner)) (aC1 -> isHB () -> sender (aC1)) (aC1 -> withdraw () -> sender (aC1)) (aC2 -> isHB () -> sender (aC2)) (aC2 -> won () -> sender (aC2)) ) () () () (
           (contract Auction (anystate auctionEnded auctionRunning)
                     {(var store : (Address : Int)) (var owner : Address) (var ended : Bool) (var highestBid : Int) (var highestBidder : Address)}
                     (Auction :: (anycaller) {
                        (public init ((owner : Address)) {(self -> owner = owner) (self -> ended = false) (self -> highestBid = 0) (self -> highestBidder = aNull) (self -> store = ())(become auctionRunning)})
                        (public func getHBidder () -> Address {return (self -> highestBidder)})
                        (public func getHBid () -> Int {return (self -> highestBid)})
                        (public func hasEnded () -> Bool {return (self -> ended)})
                        (public func withdraw ((bidder : Address)) -> Bool {return (if (((bidder != (self -> highestBidder)) && (((self -> store)[bidder ::]) != 0))) {((self -> store = ((self -> store)[bidder :: 0])) (true))} else {false})})
                        })
                     (Auction @ (auctionRunning) :: (owner) {
                        (public func endAuction () -> Void { (self -> ended = true) (become auctionEnded)  return unit})} )
                     (Auction @ (auctionRunning) :: (anycaller) {
                        (public func bid ((bid : Int) (bidder : Address)) -> Address {
                           (if ((((self -> store)[bidder ::]) == 0)) {((self -> store = ((self -> store)[bidder :: bid])) (if ((bid > (self -> highestBid))) {((self -> highestBid = bid) (self -> highestBidder = bidder))} else {unit}))} else {unit})
                           return (self -> highestBidder)}) })
                     (Auction @ (auctionEnded) :: (anycaller) {
                        (public func win ((bidder : Address)) -> Bool {return (if (((bidder == (self -> highestBidder)) && (((self -> store)[bidder ::]) != 0))) {((self -> store = ((self -> store)[bidder :: 0])) (true))} else {false})})})
                     )           
           (contract Client (canBid canWithdraw won lost hasBid ended) {
          (var auction : Address) (var bid : Int = 0)}
          (Client :: (anycaller) {
            (public init ((auction : Address)) {(self -> auction = auction) (become canBid)})
            (public func hasEnded () -> Bool {return ((self -> auction) -> ended)})
            })
          (Client @ (canBid) :: (anycaller) {
            (public func bid ((bid : Int)) -> Int {(self -> bid = bid) (if ((((self -> auction) -> bid ((bid : bid) (bidder : self))) == self)) {(become hasBid)} else {(become canWithdraw)})  return bid})})
          (Client @ (canWithdraw) :: (anycaller) {
            (public func withdraw () -> Void { ((self -> auction) -> withdraw ((bidder : self))) (if (((self -> auction) -> hasEnded ())) {(become lost)} else {(become canBid)}) return unit})})
          (Client @ (hasBid) :: (anycaller) {
            (public func isHB () -> Bool {return (if ((((self -> auction) -> getHBidder ()) == self)) {(if (((self -> auction) -> hasEnded ())) {((become won) (true))} else {true})} else {((become canWithdraw) (false))})})})
          (Client @ (won) :: (anycaller) {
            (public func won () -> Bool {return (if (((self -> auction) -> win ((bidder : self)))) {(become ended)} else {false})})})
          )))))|#

#|(traces s->ßs (term ( ((Counter -> init () -> 0 -> aCounter)
                         (aCounter -> set ((value : 3)) -> sender (aCounter))
                         (aCounter -> get () -> sender (aCounter)) )
           ()
           ()
           () (
           (contract Counter (canSet cannotSet)
                     { (var balance : Int = 0) }
                     (Counter :: (anycaller) {
                        (public init () {
                          (become canSet)})
                        (public func get () -> Int {
                          return (self -> balance)})
                        })
                     (Counter @ (canSet) :: (anycaller) {
                        (public func set ((value : Int)) -> Int {
                          (become cannotSet)
                          (var t : Int = (self -> balance))
                          (self -> balance = value)
                          (become canSet)
                          return t})
                        })
                     )
           ))))

(traces s->ßs (term ( ((EOC -> init () -> 10 -> aC)
                         (EOC -> init () -> 10 -> aO)
                         (BlockKing -> init ((warrior : aBK) (warriorGold : 3)) -> 9 -> aBK)
                         (aBK -> enter ((warrior : aC) (warriorGold : 3)) -> sender (aC))
                         (aBK -> __callback () -> sender (aO))) () () () (
           (contract BlockKing (waiting canEnter processing)
                     { (var warrior : Address)
                       (var warriorGold : Int)
                       (var king : Address)
                       (var Oraclize : Address = aO)}
                     (BlockKing :: (anycaller) {
                        (public init ((warrior : Address) (warriorGold : Int)) {
                            (self -> warrior = warrior)
                            (self -> warriorGold = warriorGold)
                            (self -> king = warrior)
                            (become canEnter)})
                        })
                     (BlockKing @ (canEnter) :: (anycaller) {
                        (public func enter ((warrior : Address) (warriorGold : Int)) -> Void {
                            (self -> warrior = warrior)
                            (self -> warriorGold = warriorGold)
                            (become waiting)
                            return unit})} )
                     (BlockKing @ (waiting) :: (Oraclize) {
                        (public func __callback () -> Void {
                            (become processing)
                            (try ? (aBK -> process_payment ()))
                            return unit})
                        })
                     (BlockKing @ (processing) :: (anycaller) {
                        (public func process_payment () -> Void {
                           (self -> king = (self -> warrior))
                           (become canEnter)
                           return unit}) 
                      })
                     )
            (contract EOC () {} (EOC :: (any_caller) {(public init () {})}))
           ))))


(contract BlockKing (waiting canEnter processing)
                     { (var warrior : Address)
                       (var warriorGold : Int)
                       (var king : Address)
                       (var Oraclize : Address = aO)}
                     (BlockKing :: (anycaller) {
                        (public init ((warrior : Address) (warriorGold : Int)) {
                            (self -> warrior = warrior)
                            (self -> warriorGold = warriorGold)
                            (self -> king = warrior)
                            (become canEnter)})
                        })
                     (BlockKing @ (canEnter) :: (anycaller) {
                        (public func enter ((warrior : Address) (warriorGold : Int)) -> Void {
                            (self -> warrior = warrior)
                            (self -> warriorGold = warriorGold)
                            (become waiting)
                            return unit})} )
                     (BlockKing @ (waiting) :: (Oraclize) {
                        (public func __callback () -> Void {
                            (become processing)
                            (try ? (aBK -> process_payment ()))
                            return unit})
                        })
                     (BlockKing @ (processing) :: (anycaller) {
                        (public func process_payment () -> Void {
                           (self -> king = (self -> warrior))
                           (become canEnter)
                           return unit}) 
                      })
                     )|#

;;;;;;Typechecker;;;;;;

(define-extended-language Flint-t Flint
  (Γ-v ::= (x : t)
     )
  (Γ ::= (Γ-v ...)))
  ;(p ::= (params ...))
  ;(e-t ::= e 
   ;  p))


;Typing rules
(define-judgment-form
  Flint-t
  #:mode (⊢ I I I O O)
  #:contract (⊢ classes Γ e Γ t)
  ;Axioms
  ;T-TRUE
  [------------------
   (⊢ classes Γ true Γ Bool)]
  ;T-FALSE
  [------------------
   (⊢ classes Γ false Γ Bool)]
  ;T-UNIT
  [--------------
   (⊢ classes Γ unit Γ Void)]
  ;T-NAT
  [--------------
   (⊢ classes Γ n Γ Int)]
  ;T-ADDRESS VAR
  [--------------
   (⊢ classes Γ x Γ (find-type Γ x))]
  ;T-SELF
  [--------------
   (⊢ classes Γ self Γ Address)]
  ;T-IF
  [(⊢ classes Γ e_1 Γ_1 bool)
   (⊢ classes Γ e_2 Γ_2 t)
   (⊢ classes Γ e_3 Γ_3 t)
   --------------
   (⊢ classes Γ (if e_1 then e_2 else e_3) (union Γ_2 Γ_3) t)]
  ;T-DECL-VAR
  [(⊢ classes Γ e Γ_1 t)
   --------------
   (⊢ classes Γ (var x : t = e) (assign-type Γ x t) t)]
  ;T-DECL-VAR-2
  [--------------
   (⊢ classes Γ (var x : t) (assign-type Γ x t) t)]
  ;T-DECL-CONS
  [(⊢ classes Γ e Γ_1 t)
   --------------
   (⊢ classes Γ (let x : t = e) (assign-type Γ x t) t)]
  ;T-DECL-CONS-2
  [--------------
   (⊢ classes Γ (let x : t) (assign-type Γ x t) t)]
  ;T-INIT
  [(⊢ (CD_1 ... (contract C (ts ...) {vars ...} (C :: (cl ...) {(public init ((x_00 : t_00) (x : t) ...) {e ...}) F ...}) PB ...) CD_2 ...) (assign-type (assign-type Γ a Address) a C) a Γ_1 Address)
   (⊢ (CD_1 ... (contract C (ts ...) {vars ...} (C :: (cl ...) {(public init ((x_00 : t_00) (x : t) ...) {e ...}) F ...}) PB ...) CD_2 ...) Γ_1 (vars ... e ...) Γ_2 _)
   (⊢ (CD_1 ... (contract C (ts ...) {vars ...} (C :: (cl ...) {(public init ((x_00 : t_00) (x : t) ...) {e ...}) F ...}) PB ...) CD_2 ...) Γ_2 ((x_00 : e_00) (x : e_0) ...) Γ_3 (t_00 t ...))
   ;avaliar e
   --------------
   (⊢ (CD_1 ... (contract C (ts ...) {vars ...} (C :: (cl ...) {(public init ((x_00 : t_00) (x : t) ...) {e ...}) F ...}) PB ...) CD_2 ...) Γ (C -> init ((x_00 : e_00) (x : e_0) ...) -> a) Γ_2 Void)]
  ;T-INIT-2 for when init has no input arguments
  [(⊢ (CD_1 ... (contract C (ts ...) {vars ...} (C :: (cl ...) {(public init () {e ...}) F ...}) PB ...) CD_2 ...) (assign-type (assign-type Γ a Address) a C) a Γ_1 Address)
   ;(⊢ (CD_1 ... (contract C (ts ...) {vars ...} (C :: (cl ...) {(public init () {e ...}) F ...}) PB ...) CD_2 ...) Γ_1 (vars ... e ...) Γ_2 _)
   --------------
   (⊢ (CD_1 ... (contract C (ts ...) {vars ...} (C :: (cl ...) {(public init () {e ...}) F ...}) PB ...) CD_2 ...) Γ (C -> init () -> a) Γ_1 Void)]
  
  ;T-CALL-SENDER
  [(⊢ (CD_1 ... (contract C (ts ...) {vars ...} K PB_1 ... (C @ (ts_pb ...) :: (cl ...) {F_1 ... (public func f ((x_00 : t_00) (x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...) Γ e_0 Γ Address)
   (⊢ (CD_1 ... (contract C (ts ...) {vars ...} K PB_1 ... (C @ (ts_pb ...) :: (cl ...) {F_1 ... (public func f ((x_00 : t_00) (x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...) Γ a Γ Address)
   (⊢ (CD_1 ... (contract C (ts ...) {vars ...} K PB_1 ... (C @ (ts_pb ...) :: (cl ...) {F_1 ... (public func f ((x_00 : t_00) (x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...) Γ e Γ_2 t)
   (⊢ (CD_1 ... (contract C (ts ...) {vars ...} K PB_1 ... (C @ (ts_pb ...) :: (cl ...) {F_1 ... (public func f ((x_00 : t_00) (x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...) Γ_2 ((x_00 : e_00) (x : e_x) ...) Γ_3 (t_00 t_x ...))
   --------------
   (⊢ (CD_1 ... (contract C (ts ...) {vars ...} K PB_1 ... (C @ (ts_pb ...) :: (cl ...) {F_1 ... (public func f ((x_00 : t_00)(x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...) Γ (e_0 -> f ((x_00 : e_00) (x : e_x) ...) -> sender (a)) Γ_3 t)]
  ;T-CALL-SENDER
  [(⊢ (CD_1 ... (contract C (ts ...) {vars ...} K PB_1 ... (C @ (ts_pb ...) :: (cl ...) {F_1 ... (public func f () -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...) Γ e_0 Γ Address)
   (⊢ (CD_1 ... (contract C (ts ...) {vars ...} K PB_1 ... (C @ (ts_pb ...) :: (cl ...) {F_1 ... (public func f () -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...) Γ a Γ Address)
   (⊢ (CD_1 ... (contract C (ts ...) {vars ...} K PB_1 ... (C @ (ts_pb ...) :: (cl ...) {F_1 ... (public func f () -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...) Γ e Γ_2 t)
   --------------
   (⊢ (CD_1 ... (contract C (ts ...) {vars ...} K PB_1 ... (C @ (ts_pb ...) :: (cl ...) {F_1 ... (public func f () -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...) Γ (e_0 -> f () -> sender (a)) Γ_2 t)]
  
  ;T-CALL-SENDER-2 
  [(⊢ (CD_1 ... (contract C (ts ...) {vars ...} PB_1 ... (C :: (cl ...) {( public init (params ...) { e_i ...}) F_1 ... (public func f ((x_00 : t_00) (x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...) Γ e_0 Γ Address)
   (⊢ (CD_1 ... (contract C (ts ...) {vars ...} PB_1 ... (C :: (cl ...) {( public init (params ...) { e_i ...}) F_1 ... (public func f ((x_00 : t_00) (x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...) Γ a Γ Address)
   (⊢ (CD_1 ... (contract C (ts ...) {vars ...} PB_1 ... (C :: (cl ...) {( public init (params ...) { e_i ...}) F_1 ... (public func f ((x_00 : t_00) (x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...) Γ e Γ_2 t)
   (⊢ (CD_1 ... (contract C (ts ...) {vars ...} PB_1 ... (C :: (cl ...) {( public init (params ...) { e_i ...}) F_1 ... (public func f ((x_00 : t_00) (x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...) Γ_2 ((x_00 : e_00) (x : e_x) ...) Γ_3 (t_00 t_x ...))
   --------------
   (⊢ (CD_1 ... (contract C (ts ...) {vars ...} PB_1 ... (C :: (cl ...) {( public init (params ...) { e_i ...}) F_1 ... (public func f ((x_00 : t_00) (x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...) Γ (e_0 -> f ((x_00 : e_00) (x : e_x) ...) -> sender (a)) Γ_3 t)] ; return statement
    ;T-CALL-SENDER-2 
  [(⊢ (CD_1 ... (contract C (ts ...) {vars ...} PB_1 ... (C :: (cl ...) {( public init (params ...) { e_i ...}) F_1 ... (public func f () -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...) Γ e_0 Γ Address)
   (⊢ (CD_1 ... (contract C (ts ...) {vars ...} PB_1 ... (C :: (cl ...) {( public init (params ...) { e_i ...}) F_1 ... (public func f () -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...) Γ a Γ Address)
   (⊢ (CD_1 ... (contract C (ts ...) {vars ...} PB_1 ... (C :: (cl ...) {( public init (params ...) { e_i ...}) F_1 ... (public func f () -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...) Γ e Γ_2 t)
   --------------
   (⊢ (CD_1 ... (contract C (ts ...) {vars ...} PB_1 ... (C :: (cl ...) {( public init (params ...) { e_i ...}) F_1 ... (public func f () -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...) Γ (e_0 -> f () -> sender (a)) Γ_2 t)] ; return statement
  ;T-CALL
  [(⊢ (CD_1 ... (contract C (ts ...) {vars ...} K PB_1 ... (C @ (ts_pb ...) :: (cl ...) {F_1 ... (public func f ((x_00 : t_00) (x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...) Γ e_0 Γ Address)
   (⊢ (CD_1 ... (contract C (ts ...) {vars ...} K PB_1 ... (C @ (ts_pb ...) :: (cl ...) {F_1 ... (public func f ((x_00 : t_00) (x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...) Γ e Γ_2 t)
   (⊢ (CD_1 ... (contract C (ts ...) {vars ...} K PB_1 ... (C @ (ts_pb ...) :: (cl ...) {F_1 ... (public func f ((x_00 : t_00) (x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...) Γ_2 ((x_00 : e_00) (x : e_x) ...) Γ_3 (t_00 t_x ...))
   --------------
   (⊢ (CD_1 ... (contract C (ts ...) {vars ...} K PB_1 ... (C @ (ts_pb ...) :: (cl ...) {F_1 ... (public func f ((x_00 : t_00) (x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...) Γ (e_0 -> f ((x_00 : e_00) (x : e_x) ...)) Γ_3 t)]
  [(⊢ (CD_1 ... (contract C (ts ...) {vars ...} K PB_1 ... (C @ (ts_pb ...) :: (cl ...) {F_1 ... (public func f () -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...) Γ e_0 Γ Address)
   (⊢ (CD_1 ... (contract C (ts ...) {vars ...} K PB_1 ... (C @ (ts_pb ...) :: (cl ...) {F_1 ... (public func f () -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...) Γ e Γ_2 t)
   --------------
   (⊢ (CD_1 ... (contract C (ts ...) {vars ...} K PB_1 ... (C @ (ts_pb ...) :: (cl ...) {F_1 ... (public func f () -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...) Γ (e_0 -> f ()) Γ_2 t)]
  ;T-CALL-2 
  [(⊢ (CD_1 ... (contract C (ts ...) {vars ...} PB_1 ... (C :: (cl ...) {( public init (params ...) { e_i ...}) F_1 ... (public func f ((x_00 : t_00) (x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...) Γ e_0 Γ Address)
   (⊢ (CD_1 ... (contract C (ts ...) {vars ...} PB_1 ... (C :: (cl ...) {( public init (params ...) { e_i ...}) F_1 ... (public func f ((x_00 : t_00) (x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...) Γ e Γ_2 t)
   (⊢ (CD_1 ... (contract C (ts ...) {vars ...} PB_1 ... (C :: (cl ...) {( public init (params ...) { e_i ...}) F_1 ... (public func f ((x_00 : t_00) (x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...) Γ_2 ((x_00 : e_00) (x : e_x) ...) Γ_3 (t_00 t_x ...))
   --------------
   (⊢ (CD_1 ... (contract C (ts ...) {vars ...} PB_1 ... (C :: (cl ...) {( public init (params ...) { e_i ...}) F_1 ... (public func f ((x_00 : t_00) (x : t_x) ...) -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...) Γ (e_0 -> f ((x_00 : e_00) (x : e_x) ...)) Γ_3 t)] ; return statement
  
  [(⊢ (CD_1 ... (contract C (ts ...) {vars ...} PB_1 ... (C :: (cl ...) {( public init (params ...) { e_i ...}) F_1 ... (public func f () -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...) Γ e_0 Γ Address)
   (⊢ (CD_1 ... (contract C (ts ...) {vars ...} PB_1 ... (C :: (cl ...) {( public init (params ...) { e_i ...}) F_1 ... (public func f () -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...) Γ e Γ_2 t)
   --------------
   (⊢ (CD_1 ... (contract C (ts ...) {vars ...} PB_1 ... (C :: (cl ...) {( public init (params ...) { e_i ...}) F_1 ... (public func f () -> t {e_1 ... return e}) F_2 ...} ) PB_2 ...) CD_2 ...) Γ (e_0 -> f ()) Γ_2 t)]
  ;T-SEQ
  [(⊢ classes Γ e_1 Γ_1 t_1)
   (⊢ classes Γ_1 (e_2 e ...) Γ_2 t_2)
   --------------
   (⊢ classes Γ (e_1 e_2 e ...) Γ_2 t_2)]
  [(⊢ classes Γ e_1 Γ_1 t_1)
   (⊢ classes Γ_1 e_2 Γ_2 t_2)
   --------------
   (⊢ classes Γ (e_1 e_2) Γ_2 t_2)]
  
  ;T-PARAMS
  [(⊢ classes Γ (x_1 : e_1) Γ t)
   (⊢ classes Γ ((x_2 : e_2) (x : e) ...) Γ (t_1 ...) )
   --------------
   (⊢ classes Γ ((x_1 : e_1) (x_2 : e_2) (x : e) ...) Γ (t t_1 ...))]
  [(⊢ classes Γ (x_1 : e_1) Γ t)
   (⊢ classes Γ (x_2 : e_2) Γ t_1)
   --------------
   (⊢ classes Γ ((x_1 : e_1) (x_2 : e_2)) Γ (t t_1))]
  [(⊢ classes Γ e Γ t)
   --------------
   (⊢ classes Γ (x : e) Γ t)]
  ;T-MAPPING
  [(⊢ classes Γ v_k Γ_1 t_k)
   (⊢ classes Γ_1 v_v Γ_2 t_v)
   (⊢ classes Γ_2 ((v_k1 : v_v1) ...) Γ_3 (t_k : t_v))
   --------------
   (⊢ classes Γ ((v_k1 : v_v1) ... (v_k : v_v)) Γ_3 (t_k : t_v))]
  [(⊢ classes Γ v_k Γ_1 t_k)
   (⊢ classes Γ_1 v_v Γ_2 t_v)
   --------------
   (⊢ classes Γ ((v_k : v_v)) Γ_2 (t_k : t_v))]
  ;T-MAPASS
  [(⊢ classes Γ v_k Γ_1 t_k)
   (⊢ classes Γ_1 v_v Γ_2 t_v)
   (⊢ classes Γ_2 M Γ_3 (t_k : t_v))
   --------------
   (⊢ classes Γ (M [v_k : v_v]) Γ_3 (t_k : t_v))]
  ;T-MAPSEL
  [(⊢ classes Γ v_k Γ_1 t_k)
   (⊢ classes Γ_1 M Γ_2 (t_k : t_v))
   --------------
   (⊢ classes Γ (M [v_k :]) Γ_2 (t_k : t_v))]
  ;T-RETURN
  [(⊢ classes Γ e Γ t)
   --------------
   (⊢ classes Γ (return e) Γ t)]
  ;T-STATE-SEL
  [(⊢ (CD_1 ... (contract C (ts ...) {vars_1 ... (var x : t) vars_2 ...}  K) CD_2 ...) ((x_0 : t_0) ... (a : C) (x_1 : t_1) ...) e_s Γ_1 Address)
   --------------
   (⊢ (CD_1 ... (contract C (ts ...) {vars_1 ... (var x : t) vars_2 ...}  K) CD_2 ...) ((x_0 : t_0) ... (a : C) (x_1 : t_1) ...) (e_s -> x) Γ_1 t)]
  [(⊢ (CD_1 ... (contract C (ts ...) {vars_1 ... (var x : t = e_x) vars_2 ...}  K) CD_2 ...) ((x_0 : t_0) ... (a : C) (x_1 : t_1) ...) e_s Γ_1 Address)
   --------------
   (⊢ (CD_1 ... (contract C (ts ...) {vars_1 ... (var x : t = e_x) vars_2 ...}  K) CD_2 ...) ((x_0 : t_0) ... (a : C) (x_1 : t_1) ...) (e_s -> x) Γ_1 t)]
  ;T-STATE-ASS
  [(⊢ classes Γ (e_0 -> x) Γ t)
   (⊢ classes Γ e_1 Γ t)
   --------------
   (⊢ classes Γ (e_0 -> x = e_1) Γ t)]
  ;T-ASS
  [(⊢ classes Γ x Γ t)
   (⊢ classes Γ e_0 Γ t)
   --------------
   (⊢ classes Γ (x = e_0) Γ t)]
  ;T-ARITH
  [(⊢ classes Γ e_0 Γ Int)
   (⊢ classes Γ e_1 Γ Int)
   --------------
   (⊢ classes Γ (e_0 a-op e_1) Γ Int)]
  ;T-BOOL-1
  [(⊢ classes Γ e_0 Γ Int)
   (⊢ classes Γ e_1 Γ Int)
   --------------
   (⊢ classes Γ (e_0 b-op1 e_1) Γ Bool)]
  ;T-BOOL-2
  [(⊢ classes Γ e_0 Γ Bool)
   (⊢ classes Γ e_1 Γ Bool)
   --------------
   (⊢ classes Γ (e_0 b-op2 e_1) Γ Bool)]
  ;T-BECOME
  [--------------
   (⊢ classes Γ (become ts) Γ Void)]
  )

(define-metafunction Flint-t
  find-type : Γ x -> t
  [(find-type ((x : t) (x_2 : t_2) ...) x)
   t]
  [(find-type ((x_1 : t_1) (x_2 : t_2) ...) x)
   (find-type ((x_2 : t_2) ...) x)]
  ;[(find-type ((x_1 : t_1) ... (x : t) (x_2 : t_2) ...) x)
   ;t])
  )


(define-metafunction Flint-t
  assign-type : Γ any t -> Γ
  [(assign-type (Γ-v ...) x t) (Γ-v ... (x : t))])

(define-metafunction Flint-t
  union : Γ Γ -> Γ
  [(union ((x_1 : t_1) ...) ((x_2 : t_2) ...))
   ((x_1 : t_1) ... (x_2 : t_2) ...)])

;(judgment-holds (⊢ () () true _ _))
;(judgment-holds (⊢ () ((x : Address)) x _ Address))

#|(judgment-holds (⊢ ((contract Rectangle () {
          (var width : Int)
          (var height : Int)}
          (Rectangle :: (any_caller) {
            (public init ((width : Int) (height : Int)) {(self -> width =  width) (self -> height = height)})
            (public func changeWidth ((width : Int)) -> Void {(self -> width = width) return unit})
            (public func changeHeight ((height : Int)) -> Void {(self -> height = height) return unit})
            (public func changeArea ((width : Int) (height : Int)) -> Int {(self -> width = width) (self -> height = height) return ((self -> width) * (self -> height))} )})
          
          )) ((aR : Address)) ((Rectangle -> init ((width : 9) (height : 5)) -> aR) (aR -> changeArea ((width : 4) (height : 9)) -> sender (aR) )) _ _))|#

#|(judgment-holds (⊢ ((contract Rectangle () {
          (var width : Int)
          (var height : Int)}
          (Rectangle :: (any_caller) {
            (public init ((width : Int) (height : Int)) {(self -> width =  width) (self -> height = height)})
            (public func changeWidth ((width : Int)) -> Void {(self -> width = width) return unit})
            (public func changeHeight ((height : Int)) -> Void {(self -> height = height) return unit})
            (public func changeArea ((width : Int) (height : Int)) -> Int {(self -> width = width) (self -> height = height) return ((self -> width) * (self -> height))} )})
          
          )) () ((Rectangle -> init ((width : 9) (height : 5)) -> aR) (width = 0)) ((aR : Address) (aR : Rectangle) (width : Int) (height : Int)) _))|#

#|(judgment-holds (⊢ ((contract Rectangle () {
          (var width : Int)
          (var height : Int)}
          (Rectangle :: (any_caller) {
            (public init ((width : Int) (height : Int)) {(self -> width =  width) (self -> height = height)})
            (public func changeWidth ((width : Int)) -> Void {(self -> width = width) return unit})
            (public func changeHeight ((height : Int)) -> Void {(self -> height = height) return unit})
            (public func changeArea ((width : Int) (height : Int)) -> Int {(self -> width = width) (self -> height = height) return ((self -> width) * (self -> height))} )})
          
          )) () ((Rectangle -> init ((width : 9) (height : 5)) -> aR) (aR -> changeArea ((width : 4) (height : 9)) -> sender (aR) )) ((aR : Address) (aR : Rectangle) (width : Int) (height : Int)) _))|#


#|(judgment-holds (⊢ ((contract Rectangle () {
          (var width : Int)
          (var height : Int)}
          (Rectangle :: (any_caller) {
            (public init ((width : Int) (height : Int)) {(self -> width =  width) (self -> height = height)})
            (public func changeWidth ((width : Int)) -> Void {(self -> width = width) return unit})
            (public func changeHeight ((height : Int)) -> Void {(self -> height = height) return unit})
            (public func changeArea ((width : Int) (height : Int)) -> Int {(self -> width = width) (self -> height = height) return ((self -> width) * (self -> height))} )})
          
          )) ((aR : Address) (aR : Rectangle) (width : Int) (height : Int))  (aR -> changeArea ((width : 4) (height : 9)) -> sender (aR) ) ((aR : Address) (aR : Rectangle) (width : Int) (height : Int)) Int))|#

#|(judgment-holds (⊢ (
       (contract RockPaperScissors () {
          (var winner : Int)}
          (RockPaperScissors :: (any_caller) {
            (public init () {(winner = 0)})
            (public func leftWins ((left : Int) (right : Int)) -> Int {(var outcome : Int = ((3 + left) - right)) (winner = ((outcome % 3) == 1)) return winner})})
          )) () ((RockPaperScissors -> init () -> aRPS) (aRPS -> leftWins ((left : 0) (right : 2)) -> sender (aRPS)) (aRPS -> leftWins ((left : 2) (right : 1)) -> sender (aRPS))) _ _))|#


#|(judgment-holds (⊢ (
       (contract TrafficLights (Red Amber Green) {
          (var signal : Int = 0)}
          (TrafficLights :: (any_caller) {
            (public init () {(become Red)})
            (public func getSignal () -> Int {return signal})})
          (TrafficLights @ (Red Green) :: (any_caller) {
             (public func moveToAmber () -> Void {(signal = 1) (become Amber) return unit })})
          (TrafficLights @ (Amber) :: (any_caller) {
             (public func moveToGreen () -> Void {(signal = 2) (become Green) return unit})
             (public func moveToRed () -> Void {(signal = 0) (become Red) return unit})}))) () ((TrafficLights -> init () -> aTL) (aTL -> moveToAmber () -> sender (aTL)) (aTL -> moveToGreen () -> sender (aTL)) (aTL -> moveToAmber () -> sender (aTL))) _ _))|#

#|(judgment-holds (⊢ (
           (contract Owner (anystate) {} (Owner :: (any_caller) {(public init () {})}))
           (contract Auction (anystate auctionEnded auctionRunning)
                     { (var owner : Address) (var ended : Bool) (var highestBid : Int) (var highestBidder : Address)}
                     (Auction :: (any_caller) {
                        (public init ((owner : Address)) {(self -> owner = owner) (self -> ended = false) (self -> highestBid = 0) (self -> highestBidder = aNull) (become auctionRunning)})
                        (public func getHBidder () -> Address {return (self -> highestBidder)})
                        (public func getHBid () -> Int {return (self -> highestBid)})
                        (public func hasEnded () -> Bool {return (self -> ended)})
                        (public func withdraw ((bidder : Address)) -> Bool {return (if ((bidder != (self -> highestBidder))) {true} else {false})})
                        })
                     (Auction @ (auctionRunning) :: (owner) {
                        (public func endAuction () -> Void { (self -> ended = true) (become auctionEnded)  return unit})} )
                     (Auction @ (auctionRunning) :: (any_caller) {
                        (public func bid ((bid : Int) (bidder : Address)) -> Address {
                           (if ((bid > (self -> highestBid))) {(if ((bidder != (self -> highestBidder))) {((self -> highestBid = bid) (self -> highestBidder = bidder))} else {unit})} else {unit})
                           return (self -> highestBidder)}) })
                     (Auction @ (auctionEnded) :: (any_caller) {
                        (public func win ((bidder : Address)) -> Bool {return (if ((bidder == (self -> highestBidder))) {true} else {false})})})
                     )           
           (contract Client (canBid canWithdraw won lost isHB ended) {
          (var auction : Address) (var bid : Int = 0)}
          (Client :: (any_caller) {
            (public init ((auction : Address)) {(self -> auction = auction) (become canBid)})
            (public func hasEnded () -> Bool {return ((self -> auction) -> ended)})
            })
          (Client @ (canBid) :: (any_caller) {
            (public func bid ((bid : Int)) -> Int {(self -> bid = bid) (if ((((self -> auction) -> bid ((bid : bid) (bidder : self))) == self)) {(become isHB)} else {(become canWithdraw)})  return bid})})
          (Client @ (canWithdraw) :: (any_caller) {
            (public func withdraw () -> Void { ((self -> auction) -> withdraw ((bidder : self))) (if (((self -> auction) -> hasEnded ())) {(become lost)} else {(become canBid)}) return unit})})
          (Client @ (isHB) :: (any_caller) {
            (public func isHB () -> Bool {return (if ((((self -> auction) -> getHBidder ()) == self)) {(if (((self -> auction) -> hasEnded ())) {((become won) (true))} else {true})} else {((become canWithdraw) (false))})})})
          (Client @ (won) :: (any_caller) {
            (public func won () -> Bool {return (if (((self -> auction) -> win ((bidder : self)))) {(become ended)} else {false})})})
          )) () ((Owner -> init () -> aOwner)  ) _ _))|#