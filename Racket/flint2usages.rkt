#lang racket
(require redex)

;;;;;Language;;;;
(define-language Flint
  ;Main language specification
  ;Contract declaration
  (CD ::= (contract C (u) {vd ...} PB ...)) ; falta tss 
  
  ;Variable declaration
  (vd ::= (var f : t))
  (F ::= (f t))

  ;Protection Blocks
  (PB ::= (C @ (tss tss ...) :: (cl ...) {M M ...})) 

  ;Function declaration
  (M ::= (public func m (params ...) -> t {return e}))

  ;Parameters
  (params ::= (x : t))

  ;Types
  (t ::= Int Address Bool Void C (C[u]) (C[u ... F ...]))
  
  ;Paths
  (r ::= self x)

  ;Class Session Types
  (u ::=
     ( q{m : u} )
     ( q{(m : u) ...} )
     ( un{} )
     (< u + u >)
     X
     ( μ X -> u )
     (! X))

  ;Usage qualifiers
  (q ::= lin un)

  ;Type state
  (tss ::= variable-not-otherwise-mentioned
       anystate)

  ;Caller of contract
  (cl ::= variable-not-otherwise-mentioned
      anycaller)

  ;Expressions
  (e ::= x v b self
       ;if condition
       (if (e) {e} else {e})
       (e a-op e)
       ;varibable assignment and declaration
       (var x : t = e)
       (r = e)
       ;contract creation
       (C -> init (n))
       ;function call
       (e -> m((x : e) ...))
       (e -> m((x : e) ...) -> sender (e))
       ;read var
       (r -> f)
       (r -> f = e)
       ;return
       (return e)
       ;sequential composition
       (e e)
       ;become statement
       (become tss)
       revert
       )

  ;Values
  (v ::= n bb a unit)

  (a ::= number) 
  (f ::= variable-not-otherwise-mentioned)
  (m ::= variable-not-otherwise-mentioned)
  (C ::= variable-not-otherwise-mentioned)
  (x ::= variable-not-otherwise-mentioned)
  (X ::= variable-not-otherwise-mentioned)
  (n ::= integer)
  
  (bb ::= true false)
  (b ::= (e b-op1 e)
     (e b-op2 e))
  (b-op1 ::= < <= == >= > !=)
  (b-op2 ::= && )
  (a-op ::= + - * / % **)
  

  ;Context Evaluation
  (E ::= hole
     (if (E) {e} else {e})
     (var x : t = E)
     (r = E)
     (E -> m((x : e) ...))
     (r -> m((x : v) ... (x : E) (x : e) ...))
     (r -> f -> m((x : v) ... (x : E) (x : e) ...))
     (E -> m((x : e) ...) -> sender (e))
     (r -> m((x : v) ... (x : E) (x : e) ...) -> sender (e))
     (r -> m((x : v) ...) -> sender (E))
     (r -> f = E)
     (return E)
     (E e)
     
     (E a-op e)
     (v a-op E)
     (E b-op1 e)
     (v b-op1 E)
     (E b-op2 e)
     (bool b-op2 E)
     )

  (vars ::= (f : v))

 )

;Runtime Syntax
(define-extended-language Flint-r Flint
  (v ::= .... null a)
  (r ::= .... a)
  (t ::= .... (C[u F ...]))
  (u ::= .... ())
  (e ::= .... getref)

  ;Environments
  ;Programs classes
  (classes ::= (CD ...))
  ;Blockchain envioromnent
  (env-ß ::= (ß-v ...))
  (ß-v ::= contracts vars)
  (contracts ::= (a R))
  (R ::= ((C u vars ... n) vars ... -> vars ...))

  ;Stack environment
  (env-s ::= (ß-v ... a ...))

  ;Type state stack
  (ts ::= (a -> tss ...))
  (CTS ::= (ts ...))
  
  
)

;;Reduction Relations;;
(define s->ßs
  (reduction-relation
  Flint-r
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
   (--> [(in-hole E (bb_1 && bb_2)) env-ß env-s CTS classes]
        [(in-hole E ,(if (equal? (term bb_1) (term bb_2)) (term true) (term false))) env-ß env-s CTS classes]
        "AND")
   
   ;Conditional clauses
   (--> [(in-hole E (if (true) {e_1} else {e_2})) env-ß env-s CTS classes]
       [(in-hole E e_1) env-ß env-s CTS classes]
        "IF-TRUE")
   (--> [(in-hole E (if (false) {e_1} else {e_2})) env-ß env-s CTS classes]
        [(in-hole E e_2) env-ß env-s CTS classes]
        "IF_FALSE")
   ;Sequential Composition
   (--> [(in-hole E (v e)) env-ß (ß-v ...) CTS classes]
        [(in-hole E e) env-ß env-ß CTS classes]
        "SEQ-C")
   (--> [(in-hole E (v e)) env-ß (ß-v ... a_0 a ...) CTS classes]
        [(in-hole E e) env-ß (ß-v ... a_0 a ...) CTS classes]
        "SEQ")
   (--> [(in-hole E (v)) env-ß env-s CTS classes]
        [(in-hole E v) env-ß env-s CTS classes]
        "REM-PAR")
   (--> [(in-hole E (C -> init (n))) env-ß env-s CTS (CD_1 ... (contract C (u ...) {(var f : t) ...} PB ...) CD_2 ...)]
        [(in-hole E getref) (fresh-1 env-ß C (get-class-usage (contract C (u ...) {(var f : t) ...} PB ...)) f ... n) env-s CTS (CD_1 ... (contract C (u ...) {(var f : t) ...} PB ...) CD_2 ...)]
        "NEW")
   (--> [(in-hole E getref) (ß-v ... (a R)) (ß-v_0 ... a_0 ...) CTS classes]
        [(in-hole E a) (ß-v ... (a R)) (ß-v_0 ... a_0 ...) CTS classes]
        "GETREF")
   (--> [(in-hole E (var x : t = v)) env-ß (ß-v ... a_1 ... a) CTS classes]
        [(in-hole E v) (decl env-ß a x v) (ß-v ... a_1 ... a) CTS classes]
        "DECL-VAR-1")
   (--> [(in-hole E (var x : t = v)) env-ß (ß-v ...) CTS classes]
        [(in-hole E v) (decl2 env-ß x v) (ß-v ...) CTS classes]
        "DECL-VAR-2")
   ;Read variables
   (--> [(in-hole E x) env-ß (ß-v ... a_1 ... a) CTS classes]
        [(in-hole E (get-field-var env-ß a x)) env-ß (ß-v ... a_1 ... a) CTS classes]
        "VAR-1")
   (--> [(in-hole E x) (ß-v_1 ... (x : v) ß-v_2 ...) (ß-v ...) CTS classes]
        [(in-hole E v) (ß-v_1 ... (x : v) ß-v_2 ...) (ß-v ...) CTS classes]
        "VAR-2")
   (--> [(in-hole E (a -> f)) env-ß env-s CTS classes]
        [(in-hole E (get-field-var env-ß a f)) (field-un-lin env-ß a f) env-s CTS classes]
        "STATEVAR")
   (--> [(in-hole E (a -> f = v)) (ß-v_1 ... (a ((C u (f_0 : v_0) ... (f : v_old) (f_1 : v_1) ... n) vars_0 ... -> vars_pv ...)) ß-v_2 ...) env-s CTS classes]
        [(in-hole E v) (ß-v_1 ... (a ((C u (f_0 : v_0) ... (f : v) (f_1 : v_1) ... n) vars_0 ... -> vars_pv ...)) ß-v_2 ...) env-s CTS classes]
        "STATEASS")
   (--> [(in-hole E (x = v)) (ß-v_1 ... (a ((C u vars_0 ... n) (f_0 : v_0) ... (x : v_old) (f_1 : v_1) ... -> vars_pv ...)) ß-v_2 ...) (ß-v ... a_0 ... a) CTS classes]
        [(in-hole E v) (ß-v_1 ... (a ((C u vars_0 ... n) (f_0 : v_0) ... (x : v) (f_1 : v_1) ... -> vars_pv ...)) ß-v_2 ...) (ß-v ... a_0 ... a) CTS classes]
        "ASS-1")
   (--> [(in-hole E (x = v)) (ß-v_1 ... (x : v_old) ß-v_2 ...) (ß-v ...) CTS classes]
        [(in-hole E v) (ß-v_1 ... (x : v) ß-v_2 ...) (ß-v ...) CTS classes]
        "ASS-2")
   (--> [(in-hole E (a -> f -> m ((x : v) ...)))
         (ß-v_0 ...
          (a ((C u (f_0 : v_0) ... (f : a_0) (f_1 : v_1) ... n) vars ... -> vars_pv ...))
          ß-v_1 ...
          (a_0 ((C_0 u_0 vars_0 ... n) vars_00 ... -> vars_pv ...)) ß-v_2 ...)
         (ß-v ... a_s ...)
         CTS
         (CD_1 ... (contract C_0 (u_00 ...) {vd ...} PB_1 ... (C_0 @ (tss_pb ...) :: (cl_pb ...) {M_1 ... (public func m ((x : t) ...) -> t_t {return e}) M_2 ...}) PB_2 ...) CD_2 ...)]
        [(in-hole E (subst-x ((x : v)...) (subst-e a (return e))))
         (ß-v_0 ...
          (a ((C u (f_0 : v_0) ... (f : a_0) (f_1 : v_1) ... n) vars ... -> vars_pv ...))
          ß-v_1 ...
          (a_0 ((C_0 u_0 vars_0 ... n) vars_00 ... -> vars_pv ...)) ß-v_2 ...)
         (ß-v ... a_s ... a)
         CTS
         (CD_1 ... (contract C_0 (u_00 ...) {vd ...} PB_1 ... (C_0 @ (tss_pb ...) :: (cl_pb ...) {M_1 ... (public func m ((x : t) ...) -> t_t {return e}) M_2 ...}) PB_2 ...) CD_2 ...)]
        "FIELDCALL")

   (--> [(in-hole E (a -> m ((x : v) ...)))
         (ß-v_1 ... (a ((C u vars_f ... n) vars ... -> vars_pv ...)) ß-v_2 ...)
         (ß-v ... a_ss ... a_s)
         (ts_1 ... (a -> tss_1 ... tss_0) ts_0 ...)
         (CD_1 ... (contract C_0 (u_00 ...) {vd ...} PB_1 ... (C_0 @ (tss_pb ...) :: (cl_pb ...) {M_1 ... (public func m ((x : t) ...) -> t_t {return e}) M_2 ...}) PB_2 ...) CD_2 ...)]
        [(in-hole E (call (ß-v_1 ... (a ((C u vars_f ... n) vars ... -> vars_pv ...)) ß-v_2 ...) (CD_1 ... (contract C_0 (u_00 ...) {vd ...} PB_1 ... (C_0 @ (tss_pb ...) :: (cl_pb ...) {M_1 ... (public func m ((x : t) ...) -> t_t {return e}) M_2 ...}) PB_2 ...) CD_2 ...) m a a_s ((x : v) ...)))
         (declcall (uptbal (uptbal (ß-v_1 ... (a ((C u vars_f ... n) vars ... -> vars_pv ...)) ß-v_2 ...) a 1) a_s ,(- (term 0) (term 1))) a ((x : v) ...))
         (ß-v ... a_ss ... a_s a)
         (ts_1 ... (a -> tss_1 ... tss_0) ts_0 ...)
         (CD_1 ... (contract C_0 (u_00 ...) {vd ...} PB_1 ... (C_0 @ (tss_pb ...) :: (cl_pb ...) {M_1 ... (public func m ((x : t) ...) -> t_t {return e}) M_2 ...}) PB_2 ...) CD_2 ...)]
        "CALL"
                (judgment-holds (tsinpb (tss_0) (tss_pb ...))))
   (--> [(in-hole E (a -> m ((x : v) ...)))
         (ß-v_1 ... (a ((C u vars_f ... n) vars ... -> vars_pv ...)) ß-v_2 ...)
         (ß-v ... a_ss ... a_s)
         CTS
         (CD_1 ... (contract C_0 (u_00 ...) {vd ...} PB_1 ... (C_0 @ (anystate) :: (cl_pb ...) {M_1 ... (public func m ((x : t) ...) -> t_t {return e}) M_2 ...}) PB_2 ...) CD_2 ...)]
        [(in-hole E (call (ß-v_1 ... (a ((C u vars_f ... n) vars ... -> vars_pv ...)) ß-v_2 ...) (CD_1 ... (contract C_0 (u_00 ...) {vd ...} PB_1 ... (C_0 @ (anystate) :: (cl_pb ...) {M_1 ... (public func m ((x : t) ...) -> t_t {return e}) M_2 ...}) PB_2 ...) CD_2 ...) m a a_s ((x : v) ...)))
         (declcall (uptbal (uptbal (ß-v_1 ... (a ((C u vars_f ... n) vars ... -> vars_pv ...)) ß-v_2 ...) a 1) a_s ,(- (term 0) (term 1))) a ((x : v) ...))
         (ß-v ... a_ss ... a_s a)
         CTS
         (CD_1 ... (contract C_0 (u_00 ...) {vd ...} PB_1 ... (C_0 @ (anystate) :: (cl_pb ...) {M_1 ... (public func m ((x : t) ...) -> t_t {return e}) M_2 ...}) PB_2 ...) CD_2 ...)]
        "CALL-ANY"
                )
   (--> [(in-hole E (a -> m ((x : v) ...) -> sender (a_s)))
         (ß-v_1 ... (a ((C u vars_f ... n) vars ... -> vars_pv ...)) ß-v_2 ...)
         (ß-v ...)
         (ts_1 ... (a -> tss_1 ... tss_0) ts_0 ...)
         (CD_1 ... (contract C_0 (u_00 ...) {vd ...} PB_1 ... (C_0 @ (tss_pb ...) :: (cl_pb ...) {M_1 ... (public func m ((x : t) ...) -> t_t {return e}) M_2 ...}) PB_2 ...) CD_2 ...)]
        [(in-hole E (return (subst-x ((x : v)...) (subst-e a e))))
         (declcall (uptbal (uptbal (ß-v_1 ... (a ((C u vars_f ... n) vars ... -> vars_pv ...)) ß-v_2 ...) a 1) a_s ,(- (term 0) (term 1))) a ((x : v) ...))
         (ß-v ... a_s )
         (ts_1 ... (a -> tss_1 ... tss_0) ts_0 ...)
         (CD_1 ... (contract C_0 (u_00 ...) {vd ...} PB_1 ... (C_0 @ (tss_pb ...) :: (cl_pb ...) {M_1 ... (public func m ((x : t) ...) -> t_t {return e}) M_2 ...}) PB_2 ...) CD_2 ...)]
        "CALLTOPLEVEL"
                (judgment-holds (tsinpb (tss_0) (tss_pb ...))))
   (--> [(in-hole E (a -> m ((x : v) ...) -> sender (a_s)))
         (ß-v_1 ... (a ((C u vars_f ... n) vars ... -> vars_pv ...)) ß-v_2 ...)
         (ß-v ...)
         CTS
         (CD_1 ... (contract C_0 (u_00 ...) {vd ...} PB_1 ... (C_0 @ (anystate) :: (cl_pb ...) {M_1 ... (public func m ((x : t) ...) -> t_t {return e}) M_2 ...}) PB_2 ...) CD_2 ...)]
        [(in-hole E (return (subst-x ((x : v)...) (subst-e a e))))
         (declcall (uptbal (uptbal (ß-v_1 ... (a ((C u vars_f ... n) vars ... -> vars_pv ...)) ß-v_2 ...) a 1) a_s ,(- (term 0) (term 1))) a ((x : v) ...))
         (ß-v ... a_s )
         CTS
         (CD_1 ... (contract C_0 (u_00 ...) {vd ...} PB_1 ... (C_0 @ (anystate) :: (cl_pb ...) {M_1 ... (public func m ((x : t) ...) -> t_t {return e}) M_2 ...}) PB_2 ...) CD_2 ...)]
        "CALLTOPLEVEL-ANY"
                )
   (--> [(in-hole E (return v)) env-ß (ß-v ... a_0 ... a) CTS classes]
        [(in-hole E v) env-ß (ß-v ... a_0 ...) CTS classes]
        "RETURN")
   (--> [(in-hole E (become tss)) env-ß (ß-v ... a_0 ... a) CTS classes]
        [(in-hole E unit) env-ß (ß-v ... a_0 ... a) (add-cts CTS a tss) classes]
        "BECOME")

   
   
   ))

;Generates nsw object identifier
(define-metafunction Flint-r
  fresh-1 : env-ß C u f ... n -> env-ß
  [(fresh-1 env-ß C u f ... n)
   (fresh-2 env-ß C u f ... n ,(random 99))])

(define-metafunction Flint-r
  fresh-2 : env-ß C u f ... n a -> env-ß
  [(fresh-2 ( ß-v_1 ... (a R) ß-v_2 ...) C u f ... n a)
   (fresh-1 (ß-v_1 ... (a R) ß-v_2 ...) C u f ... n)]
  [(fresh-2 (ß-v_1 ...) C u f ... n a_new)
   (ß-v_1 ... ( a_new ((C u (f : null) ... n) -> ) ))])

(define-metafunction Flint-r
  get-class-usage : CD -> u
  [(get-class-usage (contract C (u) {(var f : t) ...} PB ...))
   u]
  [(get-class-usage (contract C () {(var f : t) ...} PB ...))
   ()])

(define-metafunction Flint-r
  call : env-ß classes m a a ((x : v) ...) -> env-ß
  [(call (ß-v_1 ... (a ((C u vars_0 ... (x_c : a_s) vars_1 ... n) vars_2 ... -> vars_pv ...)) ß-v_2 ...)
         (CD_1 ... (contract C_0 (u_00 ...) {vd ...} PB_1 ... (C_0 @ (tss ...) :: (cl_1 ... x_c cl_2 ...) {M_1 ... (public func m ((x : t) ...) -> t_t {return e}) M_2 ...}) PB_2 ...) CD_2 ...)
         m a a_s ((x : v) ...))
   (return (subst-x ((x : v)...) (subst-e a e)))]
  [(call (ß-v_1 ... (a ((C u vars_0 ...  n) vars_1 ... (x_c : a_s) vars_2 ... -> vars_pv ...)) ß-v_2 ...)
         (CD_1 ... (contract C_0 (u_00 ...) {vd ...} PB_1 ... (C_0 @ (tss ...) :: (cl_1 ... x_c cl_2 ...) {M_1 ... (public func m ((x : t) ...) -> t_t {return e}) M_2 ...}) PB_2 ...) CD_2 ...)
         m a a_s ((x : v) ...))
   (return (subst-x ((x : v)...) (subst-e a e)))]
  [(call (ß-v_1 ... (a ((C u vars_0 ... n) vars_2 ... -> vars_pv ...)) ß-v_2 ...)
         (CD_1 ... (contract C_0 (u_00 ...) {vd ...} PB_1 ... (C_0 @ (tss ...) :: (cl_1 ... anycaller cl_2 ...) {M_1 ... (public func m ((x : t) ...) -> t_t {return e}) M_2 ...}) PB_2 ...) CD_2 ...)
         m a a_s ((x : v) ...))
   (return (subst-x ((x : v)...) (subst-e a e)))])

(define-metafunction Flint-r
  decl : env-ß a x v -> env-ß
  [(decl (ß-v_1 ... (a ((C u vars ... n) vars_0 ... (x : v_old) vars_1 ... -> vars_pv ...)) ß-v_2 ...) a x v)
   (ß-v_1 ... (a ((C u vars ... n) vars_0 ... (x : v) vars_1 ... -> vars_pv ... (x : v_old))) ß-v_2 ...)]
  [(decl (ß-v_1 ... (a ((C u vars ... n) (x_0 : v_0) ... -> vars_pv ...)) ß-v_2 ...) a x v)
   (ß-v_1 ... (a ((C u vars ... n) (x_0 : v_0) ... (x : v) -> vars_pv ...)) ß-v_2 ...)]
  )

(define-metafunction Flint-r
  decl2 : env-ß x v -> env-ß
  [(decl2 (ß-v_1 ... (x : v_old) ß-v_2 ...) x v)
   (ß-v_1 ... (x : v) ß-v_2 ...)]
  [(decl2 (ß-v_1 ...) x v)
   (ß-v_1 ... (x : v))])

(define-metafunction Flint-r
  declcall : env-ß a any -> env-ß
  [(declcall (ß-v_1 ... (a ((C u vars ... n) (x_1 : v_1) ... (x : v_old) ...  (x_2 : v_2) ... -> vars_pv ...)) ß-v_2 ...) a ((x : v) ...))
   (ß-v_1 ... (a ((C u vars ... n) (x_1 : v_1) ... (x : v) ...  (x_2 : v_2) ... -> vars_pv ... (x : v_old) ...)) ß-v_2 ...)]
  [(declcall (ß-v_1 ... (a ((C u vars ... n) (x_1 : v_1) ... -> vars_pv ...)) ß-v_2 ...) a ((x : v) ...))
   (ß-v_1 ... (a ((C u vars ... n) (x_1 : v_1) ... (x : v) ... -> vars_pv ...)) ß-v_2 ...)])

(define-metafunction Flint-r
  field-un-lin : env-ß a f -> env-ß
  ;null
  [(field-un-lin (ß-v_1 ... (a ((C u (f_0 : v_0) ... (f : unit) (f_1 : v_1) ... n) vars_0 ... -> vars_pv ...)) ß-v_2 ...) a f)
   (ß-v_1 ... (a ((C u (f_0 : v_0) ... (f : unit) (f_1 : v_1) ... n) vars_0 ... -> vars_pv ...)) ß-v_2 ...)]
  ;[(field-un-lin (ß-v_1 ... (a ((C u vars_0 ... n) (f_0 : v_0) ... (f : unit) (f_1 : v_1) ... -> vars_pv ...)) ß-v_2 ...) a f 1)
   ;(ß-v_1 ... (a ((C u vars_0 ... n) (f_0 : v_0) ... (f : unit) (f_1 : v_1) ... -> vars_pv ...)) ß-v_2 ...)]
  ;boolean
  [(field-un-lin (ß-v_1 ... (a ((C u (f_0 : v_0) ... (f : bb) (f_1 : v_1) ... n) vars_0 ... -> vars_pv ...)) ß-v_2 ...) a f)
   (ß-v_1 ... (a ((C u (f_0 : v_0) ... (f : bb) (f_1 : v_1) ... n) vars_0 ... -> vars_pv ...)) ß-v_2 ...)]
  ;[(field-un-lin (ß-v_1 ... (a ((C u vars_0 ... n) (f_0 : v_0) ... (f : bb) (f_1 : v_1) ... -> vars_pv ...)) ß-v_2 ...) a f 1)
   ;(ß-v_1 ... (a ((C u vars_0 ... n) (f_0 : v_0) ... (f : bb) (f_1 : v_1) ... -> vars_pv ...)) ß-v_2 ...)]
  ;int
  [(field-un-lin (ß-v_1 ... (a ((C u (f_0 : v_0) ... (f : n_0) (f_1 : v_1) ... n) vars_0 ... -> vars_pv ...)) ß-v_2 ...) a f)
   (ß-v_1 ... (a ((C u (f_0 : v_0) ... (f : n_0) (f_1 : v_1) ... n) vars_0 ... -> vars_pv ...)) ß-v_2 ...)]
  ;[(field-un-lin (ß-v_1 ... (a ((C u vars_0 ... n) (f_0 : v_0) ... (f : n_0) (f_1 : v_1) ... -> vars_pv ...)) ß-v_2 ...) a f 1)
   ;(ß-v_1 ... (a ((C u vars_0 ... n) (f_0 : v_0) ... (f : n_0) (f_1 : v_1) ... -> vars_pv ...)) ß-v_2 ...)]
  ;null
  [(field-un-lin (ß-v_1 ... (a ((C u (f_0 : v_0) ... (f : null) (f_1 : v_1) ... n) vars_0 ... -> vars_pv ...)) ß-v_2 ...) a f)
   (ß-v_1 ... (a ((C u (f_0 : v_0) ... (f : null) (f_1 : v_1) ... n) vars_0 ... -> vars_pv ...)) ß-v_2 ...)]
  ;[(field-un-lin (ß-v_1 ... (a ((C u vars_0 ... n) (f_0 : v_0) ... (f : null) (f_1 : v_1) ... -> vars_pv ...)) ß-v_2 ...) a f 1)
   ;(ß-v_1 ... (a ((C u vars_0 ... n) (f_0 : v_0) ... (f : null) (f_1 : v_1) ... -> vars_pv ...)) ß-v_2 ...)]
  ;address
  [(field-un-lin (ß-v_1 ... (a ((C ( μ X -> u ) (f_0 : v_0) ... (f : a_0) (f_1 : v_1) ... n) vars_0 ... -> vars_pv ...)) ß-v_2 ...) a f)
   (ß-v_1 ... (a ((C ( μ X -> u ) (f_0 : v_0) ... (f : a_0) (f_1 : v_1) ... n) vars_0 ... -> vars_pv ...)) ß-v_2 ...)]
  ;[(field-un-lin (ß-v_1 ... (a ((C ( μ X -> u ) vars_0 ... n) (f_0 : v_0) ... (f : a_0) (f_1 : v_1) ... -> vars_pv ...)) ß-v_2 ...) a f 1)
   ;(ß-v_1 ... (a ((C ( μ X -> u ) vars_0 ... n) (f_0 : v_0) ... (f : a_0) (f_1 : v_1) ... -> vars_pv ...)) ß-v_2 ...)]
  
  [(field-un-lin (ß-v_1 ... (a ((C ( un{(m : u) ...} ) (f_0 : v_0) ... (f : a_0) (f_1 : v_1) ... n) vars_0 ... -> vars_pv ...)) ß-v_2 ...) a f)
   (ß-v_1 ... (a ((C ( un{(m : u) ...} ) (f_0 : v_0) ... (f : a_0) (f_1 : v_1) ... n) vars_0 ... -> vars_pv ...)) ß-v_2 ...)]
  ;[(field-un-lin (ß-v_1 ... (a ((C ( un{(m : u) ...} ) vars_0 ... n) (f_0 : v_0) ... (f : a_0) (f_1 : v_1) ... -> vars_pv ...)) ß-v_2 ...) a f 1)
   ;(ß-v_1 ... (a ((C ( un{(m : u) ...} ) vars_0 ... n) (f_0 : v_0) ... (f : a_0) (f_1 : v_1) ... -> vars_pv ...)) ß-v_2 ...)]
  
  [(field-un-lin (ß-v_1 ... (a ((C () (f_0 : v_0) ... (f : a_0) (f_1 : v_1) ... n) vars_0 ... -> vars_pv ...)) ß-v_2 ...) a f)
   (ß-v_1 ... (a ((C () (f_0 : v_0) ... (f : a_0) (f_1 : v_1) ... n) vars_0 ... -> vars_pv ...)) ß-v_2 ...)]
  ;[(field-un-lin (ß-v_1 ... (a ((C () vars_0 ... n) (f_0 : v_0) ... (f : a_0) (f_1 : v_1) ... -> vars_pv ...)) ß-v_2 ...) a f 1)
   ;(ß-v_1 ... (a ((C () vars_0 ... n) (f_0 : v_0) ... (f : a_0) (f_1 : v_1) ... -> vars_pv ...)) ß-v_2 ...)]

  
  [(field-un-lin (ß-v_1 ... (a ((C ( lin{(m : u) ...} ) (f_0 : v_0) ... (f : a_0) (f_1 : v_1) ... n) vars_0 ... -> vars_pv ...)) ß-v_2 ...) a f)
   (ß-v_1 ... (a ((C ( lin{(m : u) ...} ) (f_0 : v_0) ... (f : null) (f_1 : v_1) ... n) vars_0 ... -> vars_pv ... (f : a_0))) ß-v_2 ... )]
  ;[(field-un-lin (ß-v_1 ... (a ((C ( lin{(m : u) ...} ) vars_0 ... n) (f_0 : v_0) ... (f : a_0) (f_1 : v_1) ... -> vars_pv ...)) ß-v_2 ...) a f 1)
   ;(ß-v_1 ... (a ((C ( lin{(m : u) ...} ) vars_0 ... n) (f_0 : v_0) ... (f : null) (f_1 : v_1) ... -> vars_pv ... (f : a_0))) ß-v_2 ... )]
  
  [(field-un-lin (ß-v_1 ... (a ((C (< u_t + u_f >) (f_0 : v_0) ... (f : a_0) (f_1 : v_1) ... n) vars_0 ... -> vars_pv ...)) ß-v_2 ...) a f)
   (ß-v_1 ... (a ((C (< u_t + u_f >) (f_0 : v_0) ... (f : null) (f_1 : v_1) ... n) vars_0 ... -> vars_pv ... (f : a_0))) ß-v_2 ... )]
  ;[(field-un-lin (ß-v_1 ... (a ((C (< u_t + u_f >) vars_0 ... n) (f_0 : v_0) ... (f : a_0) (f_1 : v_1) ... -> vars_pv ...)) ß-v_2 ...) a f 1)
   ;(ß-v_1 ... (a ((C (< u_t + u_f >) vars_0 ... n) (f_0 : v_0) ... (f : null) (f_1 : v_1) ... -> vars_pv ... (f : a_0))) ß-v_2 ... )]
  )

(define-metafunction Flint-r
  get-field-var : env-ß a f -> v
  [(get-field-var (ß-v_1 ... (a ((C u (f_0 : v_0) ... (f : v) (f_1 : v_1) ... n) vars_0 ... -> vars_pv ...)) ß-v_2 ...) a f)
   v]
  [(get-field-var (ß-v_1 ... (a ((C u vars_0 ... n) (f_0 : v_0) ... (f : v) (f_1 : v_1) ... -> vars_pv ...)) ß-v_2 ...) a f)
   v])

(define-metafunction Flint-r
  uptbal : env-ß a n -> env-ß
  [(uptbal (ß-v_1 ... (a ((C u vars_f ... n_old) vars ... -> vars_pv ...)) ß-v_2 ...) a n)
   (ß-v_1 ... (a ((C u vars_f ... ,(+ (term n_old)(term n))) vars ... -> vars_pv ...)) ß-v_2 ...)]
  )

(define-metafunction Flint-r
  add-cts : CTS a tss -> CTS
  [(add-cts (ts_1 ... (a -> tss_1 ... ) ts_0 ...) a tss)
   (ts_1 ... (a -> tss_1 ... tss ) ts_0 ...)]
  [(add-cts (ts_1 ...) a tss)
   (ts_1 ... (a -> tss))])

(define-metafunction Flint-r
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
(define-metafunction Flint-r
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

(define-judgment-form Flint-r
  #:mode (tsinpb I I)
  #:contract (tsinpb (tss ...) (tss ...))

  [----------------------------------------------
   (tsinpb (tss_1 )
                (tss_2 ... tss_1  tss_3 ...))]
  

  [(tsinpb (tss_1 ...)
                (tss_2 ... tss_0 tss_3 ...))
   
   ----------------------------------------------
   (tsinpb (tss_0 tss_1 ...)
                (tss_2 ... tss_0 tss_3 ...))])


;(traces s->ßs (term ( ((var f : (File[(un{})]) = (File -> init (3))) (var x : Int = 9)) () () ((contract File ((lin{( open : (<( μ Read -> (lin {(eof : (< (lin{(close : (un{}))}) + (lin{(read : (! Read))})>))}) ) + (un{}) >))})) {} )))))

#|(traces s->ßs (term ( ((var f : (File[(un{})]) = (File -> init (3))) ((var f : Int = 9) (f -> x))) () ()
                  ((contract File
                       ;usages
                       ((lin{( open : (<( μ Read -> (lin {(eof : (< (lin{(close : (un{}))}) + (lin{(read : (! Read))})>))}) ) + (un{}) >))}))
                       ;fields
                       {(var x : Int)}
                       ;methods
                       )))))|#

#|(traces s->ßs (term ( ((var f : (File[(un{})]) = (File -> init (3))) ((var x : Int = 9) (f -> m ((y : 4))))) () ()
                  ((contract File
                       ;usages
                       ((lin{( open : (<( μ Read -> (lin {(eof : (< (lin{(close : (un{}))}) + (lin{(read : (! Read))})>))}) ) + (un{}) >))}))
                       ;fields
                       {(var x : Int)}
                       ;methods
                       (File @ (open) {(public func m ((y : Int)) -> Int {return (7 + y)})}))))))


(traces s->ßs (term ( ((var m : (Main[(un{})]) = (Main -> init (100))) (m -> main () -> sender (m))) () ()
                  ((contract Semaphore
                       ;usages
                       ((lin{( Init : ( μ Sem -> (lin{( Amber : ( < (lin{( Red : (! Sem) )}) + (lin{( Green : (! Sem) )}) > ))})) )}))
                       ;fields
                       {(var colour : Int) ;red 0, amber 1, green 2
                        (var prevRed : Bool)}
                       ;methods
                       (Semaphore @ (Init) {
                          (public func start () -> Void {return ((self -> prevRed = true) ((self -> colour = 1) true))})})
                       (Semaphore @ (Amber) {
                          (public func goRed () -> Int {return ((self -> prevRed = true) (self -> colour = 0))})
                          (public func goGreen () -> Int {return ((self -> prevRed = false) (self -> colour = 2))})})
                       (Semaphore @ (Red Green){
                          (public func goAmber () -> Int {return (self -> colour = 1)})})
                       )
                   (contract Main
                       ;usages
                       ((un{}))
                       ;fields
                       {(var s : (Semaphore[(lin{( Init : ( μ Sem -> (lin{( Amber : ( < (lin{( Red : (! Sem) )}) + (lin{( Green : (! Sem) )}) > ))})) )})]))
                        (var prevRed : Bool)}
                       ;protection blocks
                       (Main @ () {(public func main () -> Void {
                          return ((self -> s = (Semaphore -> init (100))) ((self -> prevRed = (s -> start ())) (if (((self -> prevRed) == true)) {((self -> prevRed = false) (s -> goGreen ()))} else {((self -> prevRed = false) (s -> goRed ()))})))})})
                   )))))|#

;TRYING BECOMES AND CALLERS
#|(traces s->ßs (term ( ((var m : (Main[(un{})]) = (Main -> init (100))) (m -> main () -> sender (m))) () () ()
                  ((contract Semaphore
                       ;usages
                       ((lin{( start : ( μ Sem -> (lin{( goAmber : ( < (lin{( goRed : (! Sem) )}) + (lin{( goGreen : (! Sem) )}) > ))})) )}))
                       ;fields
                       {(var colour : Int) ;red 0, amber 1, green 2
                        (var prevRed : Bool)}
                       ;methods
                       (Semaphore @ (anystate) :: () {
                          (public func start () -> Void {return ((self -> prevRed = true) ((self -> colour = 1) (become Amber)))})})
                       (Semaphore @ (Amber) :: () {
                          (public func goRed () -> Int {return ((self -> prevRed = true) ((self -> colour = 0) (become Red)))})
                          (public func goGreen () -> Int {return ((self -> prevRed = false) ((self -> colour = 2) (become Green)))})})
                       (Semaphore @ (Red Green) :: () {
                          (public func goAmber () -> Int {return ((self -> colour = 1) (become Amber))})})
                       )
                   (contract Main
                       ;usages
                       ((un{}))
                       ;fields
                       {(var s : (Semaphore[(lin{( Init : ( μ Sem -> (lin{( Amber : ( < (lin{( Red : (! Sem) )}) + (lin{( Green : (! Sem) )}) > ))})) )})]))
                        (var prevRed : Bool)}
                       ;protection blocks
                       (Main @ (anystate) :: () {(public func main () -> Void {
                          return ((self -> s = (Semaphore -> init (100))) ((self -> prevRed = (s -> start ())) ((if (((self -> prevRed) == true)) {((self -> prevRed = false) (s -> goGreen ()))} else {((self -> prevRed = false) (s -> goRed ()))}) (s -> goRed ()))))})})
                   )))))|#




(define-extended-language Flint-t Flint
  (t ::= .... null (t ...))
  (e ::= .... u CD (M ...) ((x : e) ...) w (x ...))
  (w ::= r (r -> f))
  (v :: = .... null)
  (Γ ::= ((r t) ...) (Γ + Γ))
  (θ ::= ( (u Γ) ... ))

  ;Class environment
  (classes ::= (CD ...))
  (usages ::= ((C (X u) ...) ...))

  ;Blockchain envioromnent
  (env-ß ::= (ß-v ...))
  (ß-v ::= contracts vars)
  (contracts ::= (a R))
  (R ::= ((C u vars ... n) vars ... -> vars ...))
  )

(define-judgment-form
  Flint-t
  #:mode (⊢ I I I I I O O O O)
  #:contract (⊢ classes_1 usages_1 θ Γ_1 e t classes_2 usages_2 Γ_2)

  ;Typing rules for values
  ;T-UNIT
  [--------------------
   (⊢ classes usages θ Γ unit Void classes usages Γ)]
  ;T-TRUE
  [--------------------
   (⊢ classes usages θ Γ true Bool classes usages Γ)]
  ;T-FALSE
  [--------------------
   (⊢ classes usages θ Γ false Bool classes usages Γ)]
  ;T-ADDRESS
  [--------------------
   (⊢ classes usages θ Γ a Address classes usages Γ)]
  ;T-INT
  [--------------------
   (⊢ classes usages θ Γ n Int classes usages Γ)]
  [--------------------
   (⊢ classes usages θ Γ null null classes usages Γ)]
  ;T-ARITH
  [(⊢ classes usages θ Γ e_1 Int classes_1 usages_1 Γ_1)
   (⊢ classes_1 usages_1 θ Γ_1 e_2 Int classes_2 usages_2 Γ_2)
   --------------------
   (⊢ classes usages θ Γ (e_1 + e_2) Int classes_2 usages_2 Γ_2)]
   ;T-EQ
  [(⊢ classes usages θ Γ e_1 t_1 classes_1 usages_1 Γ_1)
   (⊢ classes_1 usages_1 θ Γ_1 e_2 t_2 classes_2 usages_2 Γ_2)
   (⊢ classes usages_2 θ (agree t_1 t_2) unit Void _ _ ())
   --------------------
   (⊢ classes usages θ Γ (e_1 == e_2) Bool classes_2 usages_2 Γ_2)]
  ;T-NOT-EQ
  [(⊢ classes usages θ Γ e_1 t_1 classes_1 usages_1 Γ_1)
   (⊢ classes_1 usages_1 θ Γ_1 e_2 t_2 classes_2 usages_2 Γ_2)
   (⊢ classes usages_2 θ (agree t_1 t_2) unit Void _ _ ())
   --------------------
   (⊢ classes usages θ Γ (e_1 != e_2) Bool classes_2 usages_2 Γ_2)]
  ;T-LESS-EQ
  [(⊢ classes usages θ Γ e_1 Int classes_1 usages_1 Γ_1)
   (⊢ classes_1 usages_1 θ Γ_1 e_2 Int classes_2 usages_2 Γ_2)
   --------------------
   (⊢ classes usages θ Γ (e_1 <= e_2) Bool classes_2 usages_2 Γ_2)]
  ;T-LESS
  [(⊢ classes usages θ Γ e_1 Int classes_1 usages_1 Γ_1)
   (⊢ classes_1 usages_1 θ Γ_1 e_2 Int classes_2 usages_2 Γ_2)
   --------------------
   (⊢ classes usages θ Γ (e_1 < e_2) Bool classes_2 usages_2 Γ_2)]
  ;T-GREATER-EQ
  [(⊢ classes usages θ Γ e_1 Int classes_1 usages_1 Γ_1)
   (⊢ classes_1 usages_1 θ Γ_1 e_2 Int classes_2 usages_2 Γ_2)
   --------------------
   (⊢ classes usages θ Γ (e_1 >= e_2) Bool classes_2 usages_2 Γ_2)]
  ;T-GREATER
  [(⊢ classes usages θ Γ e_1 Int classes_1 usages_1 Γ_1)
   (⊢ classes_1 usages_1 θ Γ_1 e_2 Int classes_2 usages_2 Γ_2)
   --------------------
   (⊢ classes usages θ Γ (e_1 > e_2) Bool classes_2 usages_2 Γ_2)]
  ;T-AND
  [(⊢ classes usages θ Γ e_1 Bool classes_1 usages_1 Γ_1)
   (⊢ classes_1 usages_1 θ Γ_1 e_2 Bool classes_2 usages_2 Γ_2)
   --------------------
   (⊢ classes usages θ Γ (e_1 && e_2) Bool classes_2 usages_2 Γ_2)]
  ;T-SEQ
  [(⊢ classes usages θ Γ e_1 t_1 classes_1 usages_1 Γ_1)
   (⊢ classes_1 usages_1 θ Γ_1 e_2 t_2 classes_2 usages_2 Γ_2)
   --------------------
   (⊢ classes usages θ Γ (e_1 e_2) t_2 classes_2 usages_2 Γ_2)]
  ;T-IF
  [(⊢ classes usages θ Γ e_1 Bool classes_1 usages_1 Γ_1)
   (⊢ classes_1 usages_1 θ Γ_1 e_2 t classes_2 usages_2 Γ_2)
   (⊢ classes_2 usages_2 θ Γ_1 e_3 t classes_3 usages_3 Γ_3)
   (⊢ classes_3 usages_3 θ
      (t-test-premise (or (t-env-subtyping Γ_2 Γ_3) (t-env-subtyping Γ_3 Γ_2))) unit Void classes_3 usages_3 ())
   ;subtyping
   --------------------
   (⊢ classes usages θ Γ (if (e_1) {e_2} else {e_3}) t classes_3 usages_3 (Γ_2 + Γ_3))]
  ;T-IFCALL
  [(⊢ (CD_1 ... (contract C (u_00 ...) {vd ...} PB_1 ... (C @ (tss_pb ...) :: (cl_pb ...) {M_1 ... (public func m ((x : t) ...) -> t_t {return e}) M_2 ...}) PB_2 ...)
            CD_2 ...) usages θ Γ (r -> m((x : e_x) ...)) _ classes_1 usages_1 Γ_1)
   (⊢ classes_1 usages_1 θ Γ_1 r (C[(< u_t + u_f >) F_1 ...]) _ usages_2 _)
   (⊢ classes_1 usages_2 θ (t-change-var-usage Γ_1 r (C[(deref-usage usages_1 C u_t) F_1 ...])) e_2 t_e classes_2 usages_3 Γ_2)
   (⊢ classes_2 usages_3 θ (t-change-var-usage Γ_1 r (C[(deref-usage usages_1 C u_f) F_1 ...])) e_3 t_e classes_3 usages_4 Γ_3)
   (⊢ classes_3 usages_4 θ
      (t-test-premise (or (t-env-subtyping Γ_2 Γ_3) (t-env-subtyping Γ_3 Γ_2))) unit Void classes_3 usages_4 ())
       ;TODO params
   --------------------
   (⊢ (CD_1 ... (contract C (u_00 ...) {vd ...} PB_1 ... (C @ (tss_pb ...) :: (cl_pb ...) {M_1 ... (public func m ((x : t) ...) -> t_t {return e}) M_2 ...}) PB_2 ...)
            CD_2 ...)
      usages θ Γ (if (r -> m((x : e_x) ...)) {e_2} else {e_3}) t_e classes_3 usages_3 (merge Γ_2 Γ_3))]
  ;T-IFSTATEVAR
  [(⊢ (CD_1 ... (contract C (u_00 ...) {vd ...} PB_1 ... (C @ (tss_pb ...) :: (cl_pb ...) {M_1 ... (public func m ((x : t) ...) -> t_t {return e}) M_2 ...}) PB_2 ...)
            CD_2 ...) usages θ Γ (r -> f -> m((x : e_x) ...)) _ classes_1 usages_1 Γ_1)
   (⊢ classes_1 usages_1 θ Γ_1 (r -> f) (C[(< u_t + u_f >) F_1 ...]) _ usages_2 _)
   (⊢ classes_1 usages_2 θ (t-change-field-usage Γ_1 r f (C[(deref-usage usages_1 C u_t) F_1 ...])) e_2 t_e classes_2 usages_3 Γ_2)
   (⊢ classes_2 usages_3 θ (t-change-field-usage Γ_1 r f (C[(deref-usage usages_1 C u_f) F_1 ...])) e_3 t_e classes_3 usages_4 Γ_3)
   --------------------
   (⊢ (CD_1 ... (contract C (u_00 ...) {vd ...} PB_1 ... (C @ (tss_pb ...) :: (cl_pb ...) {M_1 ... (public func m ((x : t) ...) -> t_t {return e}) M_2 ...}) PB_2 ...)
            CD_2 ...)
      usages θ Γ (if (r -> f -> m((x : e_x) ...)) {e_2} else {e_3}) t_e classes_3 usages_3 (Γ_2 + Γ_3))]
  ;T-VAR
  [(⊢ classes usages θ (t-test-premise (exists Γ r)) unit Void _ _ ())
   --------------------
   (⊢ classes usages θ Γ r (get-var-type Γ r) classes usages (lin-un-var Γ r))]
  ;T-STATESEL
  [;(⊢ classes usages θ (t-test-premise (exists Γ self)) unit Void _ _ ())
   --------------------
   (⊢ classes usages θ Γ (self -> f) (get-field-type Γ f) classes usages (lin-un-field Γ self f))]
  ;T-DECL
  [(⊢ classes usages θ Γ e t classes usages Γ_1)
   --------------------
   (⊢ classes usages θ Γ (var x : t = e) Void classes usages (t-assign-var Γ_1 x t))]
  ;T-STATEASS
  [(⊢ (CD_1 ... (contract C_0 (u_00 ...) {vd_1 ... (var x : t_2) vd_2 ...} PB ...) CD_2 ...)
      usages θ Γ e t classes usages Γ_1)
   (⊢ classes usages θ Γ_1 self (C[u_00 ... F ...]) _ _ _)
   (⊢ classes usages θ (agree t t_2) unit Void _ _ ())
   --------------------
   (⊢ (CD_1 ... (contract C_0 (u_00 ...) {vd_1 ... (var x : t_2) vd_2 ...} PB ...) CD_2 ...)
      usages θ Γ (self -> x = e) Void classes usages (t-assign-field Γ_1 self x t))]
  ;T-ASS
  [(⊢ classes usages θ Γ x t classes usages _)
   (⊢ classes usages θ Γ e t classes usages Γ_1)
   --------------------
   (⊢ classes usages θ Γ (x = e) Void classes usages Γ_1)]
  ;T-BECOME
  [--------------------
   (⊢ classes usages θ Γ (become tss) Void classes usages Γ)]
  ;T-NEW
  [(⊢ (CD_1 ... (contract C ((lin{(C : u)})) {vd ...} PB ...) CD_2 ...) usages θ Γ n Int
      (CD_1 ... (contract C ((lin{(C : u)})) {vd ...} PB ...) CD_2 ...) usages Γ_1)
   --------------------
   (⊢ (CD_1 ... (contract C ((lin{(C : u)})) {vd ...} PB ...) CD_2 ...) usages θ Γ
      (C -> init (n)) (C[(deref-usage-constructor u)])
      (CD_1 ... (contract C ((lin{(C : u)})) {vd ...} PB ...) CD_2 ...) usages Γ_1)]
  ;T-IF
  [(⊢ classes usages θ Γ e_1 Bool classes_1 usages_1 Γ_1)
   (⊢ classes_1 usages_1 θ Γ_1 e_2 t classes_2 usages_2 Γ_2)
   (⊢ classes_2 usages_2 θ Γ_1 e_3 t classes_3 usages_3 Γ_3)
   (⊢ classes_3 usages_3 θ
      (t-test-premise (or (t-env-subtyping Γ_2 Γ_3) (t-env-subtyping Γ_3 Γ_2))) unit Void classes_3 usages_3 ())
   --------------------
   (⊢ classes usages θ Γ (if (e_1) {e_2} else {e_3}) t classes_3 usages_3 (Γ_2 + Γ_3))]
  ;T-IFCALL
  [(⊢ (CD_1 ... (contract C (u_00 ...) {vd ...} PB_1 ... (C @ (tss_pb ...) :: (cl_pb ...) {M_1 ... (public func m ((x : t) ...) -> t_t {return e}) M_2 ...}) PB_2 ...)
            CD_2 ...) usages θ Γ (r -> m((x : e_x) ...)) _ classes_1 usages_1 Γ_1)
   (⊢ classes_1 usages_1 θ Γ_1 r (C[(< u_t + u_f >) F_1 ...]) _ usages_2 _)
   (⊢ classes_1 usages_2 θ (t-change-var-usage Γ_1 r (C[(deref-usage usages_1 C u_t) F_1 ...])) e_2 t_e classes_2 usages_3 Γ_2)
   (⊢ classes_2 usages_3 θ (t-change-var-usage Γ_1 r (C[(deref-usage usages_1 C u_f) F_1 ...])) e_3 t_e classes_3 usages_4 Γ_3)
   (⊢ classes_3 usages_4 θ
      (t-test-premise (or (t-env-subtyping Γ_2 Γ_3) (t-env-subtyping Γ_3 Γ_2))) unit Void classes_3 usages_4 ())
       ;TODO params
   --------------------
   (⊢ (CD_1 ... (contract C (u_00 ...) {vd ...} PB_1 ... (C @ (tss_pb ...) :: (cl_pb ...) {M_1 ... (public func m ((x : t) ...) -> t_t {return e}) M_2 ...}) PB_2 ...)
            CD_2 ...)
      usages θ Γ (if (r -> m((x : e_x) ...)) {e_2} else {e_3}) t_e classes_3 usages_3 (merge Γ_2 Γ_3))]
  ;T-IFSTATEVAR
  [(⊢ (CD_1 ... (contract C (u_00 ...) {vd ...} PB_1 ... (C @ (tss_pb ...) :: (cl_pb ...) {M_1 ... (public func m ((x : t) ...) -> t_t {return e}) M_2 ...}) PB_2 ...)
            CD_2 ...) usages θ Γ (r -> f -> m((x : e_x) ...)) _ classes_1 usages_1 Γ_1)
   (⊢ classes_1 usages_1 θ Γ_1 (r -> f) (C[(< u_t + u_f >) F_1 ...]) _ usages_2 _)
   (⊢ classes_1 usages_2 θ (t-change-field-usage Γ_1 r f (C[(deref-usage usages_1 C u_t) F_1 ...])) e_2 t_e classes_2 usages_3 Γ_2)
   (⊢ classes_2 usages_3 θ (t-change-field-usage Γ_1 r f (C[(deref-usage usages_1 C u_f) F_1 ...])) e_3 t_e classes_3 usages_4 Γ_3)
   --------------------
   (⊢ (CD_1 ... (contract C (u_00 ...) {vd ...} PB_1 ... (C @ (tss_pb ...) :: (cl_pb ...) {M_1 ... (public func m ((x : t) ...) -> t_t {return e}) M_2 ...}) PB_2 ...)
            CD_2 ...)
      usages θ Γ (if (r -> f -> m((x : e_x) ...)) {e_2} else {e_3}) t_e classes_3 usages_3 (Γ_2 + Γ_3))]
    ;T-VAR
  [(⊢ classes usages θ (t-test-premise (exists Γ r)) unit Void _ _ ())
   --------------------
   (⊢ classes usages θ Γ r (get-var-type Γ r) classes usages (lin-un-var Γ r))]
  ;T-STATESEL
  [(⊢ classes usages θ (t-test-premise (exists Γ self)) unit Void _ _ ())
   --------------------
   (⊢ classes usages θ Γ (self -> f) (get-field-type Γ f) classes usages (lin-un-field Γ self f))]
  ;T-DECL
  [(⊢ classes usages θ Γ e t classes usages Γ_1)
   --------------------
   (⊢ classes usages θ Γ (var x : t = e) Void classes usages (t-assign-var Γ_1 x t))]
  ;T-STATEASS
  [(⊢ (CD_1 ... (contract C_0 (u_00 ...) {vd_1 ... (var x : t_2) vd_2 ...} PB ...) CD_2 ...)
      usages θ Γ e t classes usages Γ_1)
   (⊢ classes usages θ Γ_1 self (C[u_00 ... F ...]) _ _ _)
   (⊢ classes usages θ (agree t t_2) unit Void _ _ ())
   --------------------
   (⊢ (CD_1 ... (contract C_0 (u_00 ...) {vd_1 ... (var x : t_2) vd_2 ...} PB ...) CD_2 ...)
      usages θ Γ (self -> x = e) Void classes usages (t-assign-field Γ_1 self x t))]
  ;T-ASS
  [(⊢ classes usages θ Γ r t classes usages _)
   (⊢ classes usages θ Γ e t classes usages Γ_1)
   --------------------
   (⊢ classes usages θ Γ (r = e) Void classes usages Γ_1)]
  ;T-BECOME
  [--------------------
   (⊢ classes usages θ Γ (become tss) Void classes usages Γ)]
  ;T-NEW
  [(⊢ (CD_1 ... (contract C ((lin{(C : u)})) {vd ...} PB ...) CD_2 ...)
      usages θ Γ n Int (CD_1 ... (contract C ((lin{(C : u)})) {vd ...} PB ...) CD_2 ...)
      usages Γ_1)
   --------------------
   (⊢ (CD_1 ... (contract C ((lin{(C : u)})) {vd ...} PB ...) CD_2 ...) usages θ Γ
      (C -> init (n)) (C[(deref-usage-constructor u)]) (CD_1 ... (contract C ((lin{(C : u)})) {vd ...} PB ...) CD_2 ...)
      usages Γ_1)]
  ;T-CALL-1 (var)
  [;(⊢ (CD_1 ... (contract C (u_00 ...) {vd ...} PB_1 ... (C @ (tss_pb ...) :: (cl_pb ...) {M_1 ... (public func m ((x : t) ...) -> t_t {return e}) M_2 ...}) PB_2 ...)
    ;   CD_2 ...) usages θ Γ ((x : e_x) ...) (t ...) classes usages Γ_1)
   (⊢ (CD_1 ...
       (contract C (u_00 ...) {vd ...} PB_1 ... (C @ (tss_pb ...) :: (cl_pb ...) {M_1 ...
       (public func m ((x : t) ...) -> t_t {return e}) M_2 ...}) PB_2 ...)
       CD_2 ...) usages θ Γ r
       (C[( q{(m_01 : u_01) ... (m : u_0pb) (m_02 : u_02) ...}) F_C ...]) classes usages Γ_2)
   --------------------
   (⊢ (CD_1 ...
       (contract C (u_00 ...) {vd ...} PB_1 ... (C @ (tss_pb ...) :: (cl_pb ...) {M_1 ...
       (public func m ((x : t) ...) -> t_t {return e}) M_2 ...}) PB_2 ...)
       CD_2 ...) usages θ Γ (r -> m((x : e_x) ...)) t_t classes usages
                 (t-change-var-usage Γ r (C[(deref-usage usages C u_0pb) F_C ...])))]
  ;T-CALL-2 (state var)
  [(⊢ (CD_1 ... (contract C (u_00 ...) {vd ...} PB_1 ... (C @ (tss_pb ...) :: (cl_pb ...) {M_1 ... (public func m ((x : t) ...) -> t_t {return e}) M_2 ...}) PB_2 ...)
            CD_2 ...) usages θ Γ (self -> f) (C[( q{(m_01 : u_01) ... (m : u_0pb) (m_02 : u_02) ...}) F_C ...]) classes usages Γ_1)
      ;(⊢ classes env-ß usages θ Γ ((x : e_x) ...) (t ...) classes usages Γ)
   --------------------
   (⊢ (CD_1 ...
       (contract C (u_00 ...) {vd ...} PB_1 ... (C @ (tss_pb ...) :: (cl_pb ...) {M_1 ... (public func m ((x : t) ...) -> t_t {return e}) M_2 ...}) PB_2 ...)
       CD_2 ...) usages θ Γ (self -> f -> m((x : e_x) ...)) t_t classes usages (t-change-field-usage Γ_1 self f (C[(deref-usage usages C u_0pb) F_C ...])))]
  ;T-SELF
  [(⊢ (CD_1 ... (contract C (u_00 ...) {vd ...} PB_1 ... (C @ (tss_pb1 ...) :: (cl_pb ...) {M_1 ... (public func m ((x : t) ...) -> t_t {return e}) M_2 ...}) PB_2 ...)
            CD_2 ...) usages θ Γ e t_t classes usages Γ_1)
   ;(⊢ classes env-ß usages θ Γ ((x : e_x) ...) (t ...) classes usages Γ)
   --------------------
   (⊢ (CD_1 ...
       (contract C (u_00 ...) {vd ...} PB_1 ... (C @ (tss_pb1 ...) :: (cl_pb ...) {M_1 ... (public func m ((x : t) ...) -> t_t {return e}) M_2 ...}) PB_2 ...)
       CD_2 ...) usages θ Γ (self -> m((x : e_x) ...)) t_t classes usages Γ_1)]
  ;T-ARGS
  [--------------------
   (⊢ classes usages θ Γ () () classes usages Γ)
   ]
  [(⊢ classes usages θ Γ e t classes usages Γ)
   --------------------
   (⊢ classes usages θ Γ ((x : e)) t classes usages Γ)
   ]
  [(⊢ classes usages θ Γ ((x : e)) t classes usages Γ)
   (⊢ classes usages θ Γ ((x_1 : e_1) ...) (t_1 ...) classes usages Γ)
   --------------------
   (⊢ classes usages θ Γ ((x : e) (x_1 : e_1) ...) (t t_1 ...) classes usages Γ)
   ]
  [(⊢ classes usages θ Γ x t classes_2 usages_2 Γ_2)
   --------------------
   (⊢ classes usages θ Γ (x) (t) classes_2 usages_2 Γ_2)]
  [(⊢ classes usages θ Γ x t classes_1 usages_1 Γ_1)
   (⊢ classes_1 usages_1 θ Γ_1 (x_1 ...) (t_1 ...) classes_2 usages_2 Γ_2)
   --------------------
   (⊢ classes usages θ Γ (x x_1 ...) (t t_1 ...) classes_2 usages_2 Γ_2)]
  ;T-CLASS
  [
   ;(⊢ () () () () (t-test-premise(t-check-usage () u_a)) unit Void () () ())
   (⊢ (CD ... (contract C (u_a) {vd ...} PB ...)) ( (C_1 (X_1 u_1) ... ) ... (C )) θ
      ((self (C[u_a]))) u_a Void classes_1 usages_1 Γ_1)
   ;(⊢ () () () () (t-test-premise(class-fields-un usages_1 Γ_1)) unit Void () () ())
   --------------------
   (⊢ (CD ...) ( (C_1 (X_1 u_1) ... ) ... ) θ Γ
      (contract C (u_a) {vd ...} PB ...) Void classes_1 usages_1 Γ_1)]
    ;T-BRANCH
  [;TODO assign type params
   (⊢ (CD ... (contract C (u_a) {vd ...} PB_l ... (C @ (tss_pb1 ...) :: (cl_pb ...) {M_1 ... (public func m ((x : t) ...) -> t_t {return e}) M_2 ...}) PB_r ...))
      usages θ (t-assign-params Γ ((x : t) ...)) e t_t classes_1 usages_1 Γ_1)
          ;TODO params
   (⊢ classes_1 usages_1 θ Γ_1
      (x ...) (t ...) classes_2 usages_2 Γ_2)
   (⊢ classes_2 usages_2 θ
      (is-bool-variant  (remove-local-vars Γ_2) t_t u)
      u _ classes_3 usages_3 Γ_3)
   --------------------
   (⊢ (CD ... (contract C (u_a) {vd ...} PB_l ... (C @ (tss_pb1 ...) :: (cl_pb ...) {M_1 ... (public func m ((x : t) ...) -> t_t {return e}) M_2 ...}) PB_r ...))
      usages θ Γ (q{m : u}) Void classes_3 usages_3 Γ_3)]
  ;T-BRANCH-END
  [--------------------
   (⊢ classes usages θ Γ (un{}) Void classes usages Γ)]
  ;T-BRANCH-AUX-SINGLE
  [(⊢ classes usages θ Γ (q{m : u}) Void classes_1 usages_1 Γ_1)
   --------------------
   (⊢ classes usages θ Γ (q{(m : u)}) Void classes_1 usages_1 Γ_1)]
  ;T-BRANCH-AUX-MULT
  [(⊢ classes usages θ Γ (q{m : u}) Void classes_1 usages_1 Γ_1)
   (⊢ classes_1 usages_1 θ Γ (q{(m_0 : u_0) ...}) Void classes_2 usages_2 Γ_2)
   --------------------
   (⊢ classes usages θ Γ (q{(m : u) (m_0 : u_0) ...}) Void classes_2 usages_2 Γ_2)]
  ;T-VARIANT
  [(⊢ classes usages θ Γ_1 u_t Void classes_1 usages_1 Γ_3)
   (⊢ classes_1 usages_1 θ Γ_2 u_f Void classes_2 usages_2 Γ_4)
   --------------------
   (⊢ classes usages θ (Γ_1 + Γ_2) (< u_t + u_f >) Void classes_2 usages_2 (Γ_3 + Γ_4))]
  ;T-USAGEVAR
  [--------------------
   (⊢ classes usages ((X_0 Γ_0) ... (X Γ_x) (X_1 Γ_1) ...) Γ ( ! X ) Void classes usages Γ_x)]
  ;T-REC
  [(⊢ (CD ... (contract C (u_00 ...) {vd ...} PB ...))
        ((C_l (X_l u_l) ...) ... (C (X_C u_C) ... (X u)) (C_r (X_r u_r) ...) ...)
        (t-assign-θ θ X Γ) Γ u Void classes_1 usages_1 Γ_1)
   --------------------
   (⊢ (CD ... (contract C (u_00 ...) {vd ...} PB ...))
        ((C_l (X_l u_l) ...) ... (C (X_C u_C) ...) (C_r (X_r u_r) ...) ...) θ Γ ( μ X -> u ) Void classes_1 usages_1 Γ_1)]

  )



;Tests a premise, return an empty Γ when true
(define-metafunction Flint-t  
  t-test-premise :  boolean -> Γ
  [(t-test-premise #true)
   ()]
  [(t-test-premise #false)
   ((error void))])

(define-metafunction Flint-t  
  and :  boolean boolean -> boolean
  [(and #true #true)
   #true]
  [(and any_1 any_2)
   #false])

(define-metafunction Flint-t 
  or :  boolean boolean -> boolean
  [(or #false #false)
   #false]
  [(or any_1 any_2)
   #true])

;Checks if the usage is valid, i.e., it doesn't go from unrestricted to linear
(define-metafunction Flint-t 
  t-is-equivalent-state : u_1 u_2 -> boolean  
  [(t-is-equivalent-state u u)
   #true]
  [(t-is-equivalent-state u_1 ( μ X -> u_2 ))
   (t-is-equivalent-state u_1 u_2)]
  [(t-is-equivalent-state (un{}) (un{(m : u) ...}))
   #false]
  [(t-is-equivalent-state (un{(m_a : u_a1) ... (m : u_1) (m_b : u_b1) ...}) (un{(m_a : u_a2) ... (m : u_2) (m_b : u_b2) ...}))
   (t-is-equivalent-state (un{(m_a : u_a1) ... (m_b : u_b1) ...}) (un{(m_a : u_a2) ... (m_b : u_b2) ...}))]
  [(t-is-equivalent-state (un{(m_a : u_a) ... }) (un{(m_b : u_b) ...}))
   #false])

(define-metafunction Flint-t 
  t-check-usage : ((X u) ...) u -> boolean  
  [(t-check-usage any (lin{(m : u)}))
   (t-check-usage any u)]
  [(t-check-usage any (lin{(m_a : u_a) (m_b : u_b) ...}))
   (and (t-check-usage any u_a) (t-check-usage any (lin{(m_b : u_b) ...})))]
  [(t-check-usage any (< u_f + u_t >))
   (and (t-check-usage any u_f) (t-check-usage any u_t))]
  [(t-check-usage ((X_t u_t) ...) ( μ X -> u ))
   (t-check-usage ((X u) (X_t u_t) ...) u)]
  [(t-check-usage any (un{(m_a : u_a) ... (m : (< u_t + u_f >)) (m_b : u_b) ...}))
   #false]
  [(t-check-usage ((X_a u_a) ... (X (lin{(m_X : u_X) ...})) (X_b u_b) ...) (un{(m_a : u_a) ... (m : (! X)) (m_b : u_b) ...}))
   #false]
  
  [(t-check-usage ((X_a u_a) ... (X u) (X_b u_b) ...) (un{(m_c : u_c) ... (m : (! X)) (m_d : u_d) ...}))
   (and (t-is-equivalent-state (un{(m_c : u_c) ... (m : (! X)) (m_d : u_d) ...}) u) (t-check-usage ((X_a u_a) ... (X (un{(m_c : u_c) ... (m_d : u_d) ...})) (X_b u_b) ...) (un{(m_c : u_c) ... (m_d : u_d) ...})))]

  [(t-check-usage any (un{(m_a : u_a) ... (m : u) (m_b : u_b) ...}))
   (t-is-equivalent-state (un{(m_a : u_a) ... (m : u) (m_b : u_b) ...}) u)]

  [(t-check-usage any_1 any_2)
   #true])

(define-metafunction Flint-t 
  exists : Γ r -> boolean
  [(exists ((r_1 t_1) ... (r t) (r_2 t_2) ...) r)
   #true]
  [(exists (Γ_1 + Γ_2) r)
   ,(if (eq? (term (exists Γ_1 r)) #true) #true (term (exists Γ_2 r))  )]
  [(exists any_1 any_2)
   #false])

;Returns the type of a variable
(define-metafunction Flint-t 
  get-var-type : Γ r -> t
  [(get-var-type ((r_1 t_1) ... (r t) (r_2 t_2) ...) r)
   t]
  [(get-var-type (Γ_1 + Γ_2) r)
   (get-var-type Γ_1 r)])

;Returns the type of a field
(define-metafunction Flint-t 
  get-field-type : Γ f -> t
  [(get-field-type ((r_1 t_1) ... (self (C[u ... F_1 ... (f t) F_2 ...])) (r_2 t_2) ...) f)
   t]
  [(get-field-type (Γ_1 + Γ_2) r)
   (get-field-type Γ_1 r)]
  [(get-field-type Γ f)
   null])

;Checks if a variable has unrestricted or linear type and returns the appropriate Γ
(define-metafunction Flint-t 
  lin-un-var : Γ r -> Γ
  [(lin-un-var ((r_1 t_1) ... (r (C[(< u_1 + u_2 >) F ...])) (r_2 t_2) ...) r)
   ((r_1 t_1) ... (r_2 t_2) ...)]
  [(lin-un-var ((r_1 t_1) ... (r (C[(lin{(m : u) ...}) F ...])) (r_2 t_2) ...) r)
   ((r_1 t_1) ... (r_2 t_2) ...)]
  [(lin-un-var ((r_1 t_1) ... (r t) (r_2 t_2) ...) r)
   ((r_1 t_1) ... (r t) (r_2 t_2) ...)]
  [(lin-un-var (Γ_1 + Γ_2) r)
   ((lin-un-var Γ_1 r) + (lin-un-var Γ_2 r))])

;Checks if a field has unrestricted or linear type and returns the appropriate Γ
(define-metafunction Flint-t 
  lin-un-field : Γ r f -> Γ
  [(lin-un-field ((r_1 t_1) ... (r (C[u ... F_1 ... ((C[(< u_1 + u_2 >) F_C ...]) f) F_2 ...])) (r_2 t_2) ...) r f)
   ((r_1 t_1) ... (r (C[u ... F_1 ... F_2 ...])) (r_2 t_2) ...)]
  [(lin-un-field ((r_1 t_1) ... (r (C[u ... F_1 ... ((C_C[(lin{(m_C : u_C) ...}) F_C ...]) f) F_2 ...])) (r_2 t_2) ...) r f)
   ((r_1 t_1) ... (r (C[u ... F_1 ... F_2 ...])) (r_2 t_2) ...)]
  [(lin-un-field ((r_1 t_1) ... (r (C[u ... F_1 ... (f t) F_2 ...])) (r_2 t_2) ...) r f)
   ((r_1 t_1) ... (r (C[u ... F_1 ... (f t) F_2 ...])) (r_2 t_2) ...)]
  [(lin-un-field (Γ_1 + Γ_2) r f)
   ((lin-un-field Γ_1 r f) + (lin-un-field Γ_2 r f))]
  [(lin-un-field Γ r f)
   Γ])

;Assigns a new variable
(define-metafunction Flint-t
  t-assign-var : Γ r t -> Γ
  [(t-assign-var ((r_t t_t) ... (r (C[(un{}) F_old ...])) (r_f t_f) ...) r (C[u ... F_new ...]))
   ((r_t t_t) ... (r (C[u ... F_new ...])) (r_f t_f) ...)]
  [(t-assign-var ((r_1 t_1) ... (r t) (r_2 t_2) ...) r t)
   ((r_1 t_1) ... (r t) (r_2 t_2) ...)]
  [(t-assign-var ((r_1 t_1) ...) r t)
   ((r t) (r_1 t_1) ...)]
  [(t-assign-var (Γ_1 + Γ_2) r t)
   ((t-assign-var Γ_1 r t) + (t-assign-var Γ_2 r t))])

;Assigns new params
(define-metafunction Flint-t
  t-assign-params : Γ ((r : t) ...) -> Γ
  [(t-assign-params ((r_1 t_1) ...) ((r : t) ...))
   ((r_1 t_1) ... (r t) ...)])

;Assign a new state variable
(define-metafunction Flint-t 
  t-assign-field : Γ r f t -> Γ
  [(t-assign-field ((r_1 t_1) ... (r (C[u ... F_1 ... (f t) F_2 ...])) (r_2 t_2) ...) r f null)
   ((r_1 t_1) ... (r (C[u ... F_1 ... F_2 ...])) (r_2 t_2) ...)]
  [(t-assign-field ((r_1 t_1) ... (r (C[u ... F_1 ... F_2 ...])) (r_2 t_2) ...) r f null)
   ((r_1 t_1) ... (r (C[u ... F_1 ... F_2 ...])) (r_2 t_2) ...)]
  [(t-assign-field ((r_1 t_1) ... (r (C[u ... F_1 ... (f t) F_2 ...])) (r_2 t_2) ...) r f t)
   ((r_1 t_1) ... (r (C[u ... F_1 ... (f t) F_2 ...])) (r_2 t_2) ...)]
  [(t-assign-field ((r_1 t_1) ... (r (C[u ... F_1 ... ((C_a[u_old ... F_old ...]) f) F_2 ...])) (r_2 t_2) ...) r f (C_a[u_new ... F_new ...]))
   ((r_1 t_1) ... (r (C[u ... F_1 ... ((C_a[u_new ... F_new ...]) f) F_2 ...])) (r_2 t_2) ...)]
  [(t-assign-field ((r_1 t_1) ... (r (C[u ... F_1 ... (t_old f) F_2 ...])) (r_2 t_2) ...) r f t_new)
   ((r_1 t_1) ... (r (C[u ... F_1 ... (t_old f) F_2 ...])) (r_2 t_2) ...)]
  [(t-assign-field ((r_1 t_1) ... (r (C[u ... F ...])) (r_2 t_2) ...) r f t)
   ((r_1 t_1) ... (r (C[u ... F ... (f t)])) (r_2 t_2) ...)])

;Changes a variable's usage
(define-metafunction Flint-t 
  t-change-var-usage : Γ r t -> Γ
  [(t-change-var-usage ((r_1 t_1) ... (r (C[u_old F_old ...])) (r_2 t_2) ...) r (C[( μ X -> u_new ) F_new ...]))
   ((r_1 t_1) ... (r (C[u_new F_new ...])) (r_2 t_2) ...)]
  [(t-change-var-usage ((r_1 t_1) ... (r (C[u_old F_old ...])) (r_2 t_2) ...) r (C[u_new F_new ...]))
   ((r_1 t_1) ... (r (C[u_new F_new ...])) (r_2 t_2) ...)])

(define-metafunction Flint-t 
  t-change-w-usage : Γ w t -> Γ
  [(t-change-w-usage ((r_1 t_1) ... (w (C[u_old F_old ...])) (r_2 t_2) ...) w (C[( μ X -> u_new ) F_new ...]))
   ((r_1 t_1) ... (w (C[u_new F_new ...])) (r_2 t_2) ...)]
  [(t-change-w-usage ((r_1 t_1) ... (w (C[u_old F_old ...])) (r_2 t_2) ...) w (C[u_new F_new ...]))
   ((r_1 t_1) ... (w (C[u_new F_new ...])) (r_2 t_2) ...)])

;Changes a field's usage
(define-metafunction Flint-t 
  t-change-field-usage : Γ r f t -> Γ
  [(t-change-field-usage ((r_1 t_1) ... (r (C[u ... F_1 ... ((C_1[u_f F_f ...]) f) F_2 ...])) (r_2 t_2) ...) r f (C_1[( μ X -> u_t ) F_t ...]))
   ((r_1 t_1) ... (r (C[u ... F_1 ... ((C_1[u_t F_t ...]) f) F_2 ...])) (r_2 t_2) ...)]
  [(t-change-field-usage ((r_1 t_1) ... (r (C[u ... F_1 ... ((C_1[u_f F_f ...]) f) F_2 ...])) (r_2 t_2) ...) r f (C_1[u_t F_t ...]))
   ((r_1 t_1) ... (r (C[u ... F_1 ... ((C_1[u_t F_t ...]) f) F_2 ...])) (r_2 t_2) ...)])

;Returns a Γ with all of a class fields
(define-metafunction Flint-t 
  t-init-fields : Γ (r t) ... -> Γ
  [(t-init-fields ((r_1 t_1) ...) (r t) ...)
   ((r_1 t_1) ... (r t) ...)])

;Assigns a new usage variable
(define-metafunction Flint-t 
  t-assign-θ : θ u Γ -> θ
  [(t-assign-θ ((u_1 Γ_1) ... (u Γ_old) (u_2 Γ_2) ...) u Γ)
   ((u_1 Γ_1) ... (u Γ) (u_2 Γ_2) ...)]
  [(t-assign-θ ((u_1 Γ_1) ...) u Γ)
   ((u Γ) (u_1 Γ_1) ...)])

(define-metafunction Flint-t 
  class-fields-un : usages Γ -> boolean
  [(class-fields-un ( (C_t (X_t u_t)... ) ... (C_1 (X_C1 u_C1) ... (X u) (X_C2 u_C2) ...) (C_f (X_f u_f)... ) ... ) ((r_1 t_1) ... (self (C[u_C ... ((C_1[u F_1 ...] ) f) F ...])) (r_2 t_2) ...))
   (class-fields-un ( (C_t (X_t u_t)... ) ... (C_1 (X_C1 u_C1) ... (X u) (X_C2 u_C2) ...) (C_f (X_f u_f)... ) ... ) ((r_1 t_1) ... (self (C[u F ...])) (r_2 t_2) ...))]
  [(class-fields-un usages ((r_1 t_1) ... (self (C[u ... ((C_1[(< u_t + u_f >) F_1 ...] ) f) F ...])) (r_2 t_2) ...))
   #false]
  [(class-fields-un usages ((r_1 t_1) ... (self (C[u ... ((C_1[(lin{(m_1 : u_1) ...}) F_1 ...] ) f) F ...])) (r_2 t_2) ...))
   #false]
  [(class-fields-un usages ((r_1 t_1) ... (self (C[u ... (f t) F ...])) (r_2 t_2) ...))
   (class-fields-un usages ((r_1 t_1) ... (self (C[u ... F ...])) (r_2 t_2) ...))]
  [(class-fields-un usages (Γ_1 + Γ_2))
   ,(if (eq? (term (class-fields-un usages Γ_1)) #true) #true (term (class-fields-un usages Γ_2))  )]
  [(class-fields-un usages ((r_1 t_1) ... (self (C[u ...])) (r_2 t_2) ...))
   #true])

;Compares two types
(define-metafunction Flint-t 
  agree : t_1 t_2 -> Γ
  [(agree Int Int)
   ()]
  [(agree Bool Bool)
   ()]
  [(agree Void Void)
   ()]
  [(agree any null)
   ()]
  [(agree null any)
   ()]
  [(agree (C[u F_1 ...]) (C[u F_2 ...]))
   ()]
  [(agree (C[F_1 ...]) (C[F_2 ...]))
   ()]
  [(agree any_1 any_2)
   ((error Void))])

;Removes all local variables from Γ
(define-metafunction Flint-t 
  remove-local-vars : Γ -> Γ
  [( remove-local-vars ((r_t t_t) ... (self t) (r_f t_f) ...))
   ((self t))]
  [( remove-local-vars (Γ_1 + Γ_2))
   ( ( remove-local-vars Γ_1) + ( remove-local-vars Γ_2) )])

(define-metafunction Flint-t 
  usage-subtyping : Γ ((X u) ...) u_1 u_2 -> boolean
  [(usage-subtyping Γ ((X_t u_t) ...) u u)
   #true]
  [(usage-subtyping Γ ((X_t u_t) ...) ( μ X -> u ) u_2)
   (usage-subtyping Γ ((X u) (X_t u_t) ...) u u_2)]
  [(usage-subtyping Γ ((X_t u_t) ...) (q_1{(m_1 : u_1)}) (q_2{(m_2 : u_2) ...}))
   (usage-subtyping2 Γ ((X_t u_t) ...) u_1 (q_2{(m_2 : u_2) ...}))]
  [(usage-subtyping Γ ((X_t u_t) ...) (q_1{(m_1 : u_1) (m_2 : u_2) ... }) (q_3{(m_3 : u_3) ...}))
   (and (usage-subtyping2 Γ ((X_t u_t) ...) u_1 (q_3{(m_3 : u_3) ...}))
        (usage-subtyping Γ ((X_t u_t) ...) (q_1{(m_2 : u_2) ... }) (q_3{(m_3 : u_3) ...})))]
  [(usage-subtyping Γ ((X_t u_t) ...) (q_1{(m_1 : u_1)}) (un{}))
   (usage-subtyping2 Γ ((X_t u_t) ...) u_1 (un{}))]
  [(usage-subtyping Γ ((X_t u_t) ...) (< u_1 + u_2 >) (< u_3 + u_4 >))
   (and (usage-subtyping2 Γ ((X_t u_t) ...) u_1 u_3) (usage-subtyping2 Γ ((X_t u_t) ...) u_2 u_4))]
  [(usage-subtyping Γ any_1 any_2 any_3)
   #false])

(define-metafunction Flint-t 
  usage-subtyping2 : Γ ((X u) ...) u u -> boolean
  [(usage-subtyping2 Γ ((X_t u_t) ...) u u)
   #true]
  [(usage-subtyping2 Γ ((X_t u_t) ...) ( μ X -> u ) u_2)
   (usage-subtyping2 Γ ((X u) (X_t u_t) ...) u u_2)]
  [(usage-subtyping2 Γ ((X_t u_t) ... (X u_1) (X_f u_f) ...) (! X) u_2)
   (usage-subtyping2 Γ ((X_t u_t) ... (X_f u_f) ...) u_1 u_2)]
  [(usage-subtyping2 Γ ((X_t u_t) ...) (q_1{(m_1 : u_1)}) u_2)
   (usage-subtyping2 Γ ((X_t u_t) ...) u_1 u_2)]
  [(usage-subtyping2 Γ ((X_t u_t) ...) (< u_1 + u_2 >) u_3)
   (or (usage-subtyping2 Γ ((X_t u_t) ...) u_1 u_3) (usage-subtyping2 Γ ((X_t u_t) ...) u_2 u_3))]
  [(usage-subtyping2 Γ any_1 any_2 any_3)
   #false])

(define-metafunction Flint-t 
  t-env-subtyping : Γ Γ -> boolean
  [(t-env-subtyping Γ_1 (Γ_2 + Γ_3))
   (and (t-env-subtyping Γ_1 Γ_2) (t-env-subtyping Γ_1 Γ_3))]

  [(t-env-subtyping (Γ_1 + Γ_2) Γ_3)
   (and (t-env-subtyping Γ_1 Γ_3) (t-env-subtyping Γ_2 Γ_3))]
  
  [(t-env-subtyping ((r_t1 t_t1) ... (r (C[F_1 ...])) (r_f1 t_f1) ...)
                    ((r_t2 t_t2) ... (r (C[F_2 ...])) (r_f2 t_f2) ...))
   (and (t-env-subtyping ((r_t1 t_t1) ... (r_f1 t_f1) ...) ((r_t2 t_t2) ... (r_f2 t_f2) ...))
        (t-env-subtyping (t-init-fields () F_1 ...) (t-init-fields () F_2 ...)))]
  
  
  [(t-env-subtyping ((r_t1 t_t1) ... (r (C[u_1 F_1 ...])) (r_f1 t_f1) ...)
                    ((r_t2 t_t2) ... (r (C[u_2 F_2 ...])) (r_f2 t_f2) ...))
   (and (
         and (usage-subtyping () () u_1 u_2)
             (t-env-subtyping ((r_t1 t_t1) ... (r_f1 t_f1) ...) ((r_t2 t_t2) ... (r_f2 t_f2) ...)))
        (t-env-subtyping (t-init-fields () F_1 ...) (t-init-fields () F_2 ...)))]
  [(t-env-subtyping ((r_t1 t_t1) ... (r Void) (r_f1 t_f1) ...) ((r_t2 t_t2) ... (r Void) (r_f2 t_f2) ...))
   (t-env-subtyping ((r_t1 t_t1) ... (r_f1 t_f1) ...) ((r_t2 t_t2) ... (r_f2 t_f2) ...))]
  [(t-env-subtyping ((r_t1 t_t1) ... (r Int) (r_f1 t_f1) ...) ((r_t2 t_t2) ... (r Int) (r_f2 t_f2) ...))
   (t-env-subtyping ((r_t1 t_t1) ... (r_f1 t_f1) ...) ((r_t2 t_t2) ... (r_f2 t_f2) ...))]
  [(t-env-subtyping ((r_t1 t_t1) ... (r Bool) (r_f1 t_f1) ...) ((r_t2 t_t2) ... (r Bool) (r_f2 t_f2) ...))
   (t-env-subtyping ((r_t1 t_t1) ... (r_f1 t_f1) ...) ((r_t2 t_t2) ... (r_f2 t_f2) ...))]
  [(t-env-subtyping () ((r_t t_t) (r_f t_f) ... ) )
   #false]
  [(t-env-subtyping ((r_t t_t) ... ) () )
   #true])

;Unfolds an usage if needed
(define-metafunction Flint-t 
  deref-usage : usages C u -> u
  [(deref-usage ( (C_t (X_t u_t)... ) ... (C (X_C1 u_C1) ... (X u) (X_C2 u_C2) ...) (C_f (X_f u_f) ... ) ... ) C (! X))
   (refactor-usage u)]
  [(deref-usage any_1 any_2 u)
   (refactor-usage u)])

(define-metafunction Flint-t 
  deref-usage-constructor : u -> u
  [(deref-usage-constructor (μ X -> u))
   (refactor-usage u)]
  [(deref-usage-constructor u)
   (refactor-usage u)])

(define-metafunction Flint-t 
  refactor-usage : u -> u
  [(refactor-usage (q{(m_l : u_l) ... (m : (μ X -> u)) (m_r : u_r) ...}))
   (refactor-usage (q{(m_l : u_l) ... (m : (! X)) (m_r : u_r) ...}))]
  [(refactor-usage (q{(m_l : u_l) ... (m : (< (μ X -> u_1) + u_2 >)) (m_r : u_r) ...}))
   (refactor-usage (q{(m_l : u_l) ... (m : (< (! X) + u_2 >)) (m_r : u_r) ...}))]
  [(refactor-usage (q{(m_l : u_l) ... (m : (< u_1 + (μ X -> u_2) >)) (m_r : u_r) ...}))
   (refactor-usage (q{(m_l : u_l) ... (m : (< u_1 + (! X) >)) (m_r : u_r) ...}))]
  [(refactor-usage any)
   any])

(define-metafunction Flint-t 
  merge : Γ Γ -> Γ
  [(merge Γ Γ)
   Γ]
  [(merge Γ_1 Γ_2)
   (Γ_1 + Γ_2)])

(define-metafunction Flint-t 
  is-self : r -> Γ
  [(is-self self)
   ()]
  [(is-self any)
   ((error void))])

(define-metafunction Flint-t 
  is-bool-variant : Γ t u -> Γ
  [(is-bool-variant (Γ_1 + Γ_2) Bool any)
   (Γ_1 + Γ_2)]
  [(is-bool-variant Γ Bool (< u_1 + u_2 >))
   (Γ + Γ)]
  [(is-bool-variant Γ any_1 any_2)
   Γ])


#|(judgment-holds (⊢ () () () () 
                       (contract Auction
                       ;usages
                       ((lin{(Auction : (μ AuctionRunning -> (lin {(getHBidder : (! AuctionRunning)) (hasEnded : (! AuctionRunning)) (withdraw : (< (! AuctionRunning) + (! AuctionRunning) >)) (bid : (< (! AuctionRunning) + (! AuctionRunning) >)) (getHBid : (! AuctionRunning)) (endAuction : (μ AuctionEnded -> (lin {(getHBidder : (! AuctionEnded)) (getHBid : (! AuctionEnded)) (win : (< (! AuctionEnded) + (! AuctionEnded) >)) (withdraw : (< (! AuctionEnded) + (! AuctionEnded) >)) (hasEnded : (! AuctionEnded)) })))})))}))
                       ;fields
                       {(var owner : Int)
                        (var ended : Bool)
                        (var highestBid : Int)
                        (var highestBidder : Int)}
                       ;methods
                       (Auction @ (anystate) :: (anycaller) {
                           (public func Auction () -> Void {return ((self -> owner = 9) ((self -> ended = false) ((self -> highestBid = 0) ((self -> highestBidder = 9) (become auctionRunning)))))})
                           (public func getHBidder () -> Int {return (self -> highestBidder)})
                           (public func getHBid () -> Int {return (self -> highestBid)})
                           (public func hasEnded () -> Bool {return (self -> ended)})
                           (public func withdraw ((bidder : Int)) -> Bool {return (if ((bidder != (self -> highestBidder))) {true} else {false})})
                       })
                          
                        
                       (Auction @ (auctionRunning) :: (owner) {
                        (public func endAuction () -> Void { return ((self -> ended = true) (become auctionEnded))})} )
                       (Auction @ (auctionRunning) :: (any_caller) {
                        (public func bid ((bid : Int) (bidder : Int)) -> Bool { return
                           (if ((bid > (self -> highestBid))) {(if ((bidder != (self -> highestBidder))) {((self -> highestBid = bid) ((self -> highestBidder = bidder) true))} else {false})} else {false})
                           }) })
                       (Auction @ (auctionEnded) :: (any_caller) {
                        (public func win ((bidder : Int)) -> Bool {return (if ((bidder == (self -> highestBidder))) {true} else {false})})})
                     
                           
                       ) Void _ _ _
                   
                   ))

(judgment-holds (⊢ () () () () 
                       ((contract Auction
                       ;usages
                       ((lin{(Auction : (μ AuctionRunning -> (lin {(getHBidder : (! AuctionRunning)) (hasEnded : (! AuctionRunning)) (withdraw : (< (! AuctionRunning) + (! AuctionRunning) >)) (bid : (< (! AuctionRunning) + (! AuctionRunning) >)) (getHBid : (! AuctionRunning)) (endAuction : (μ AuctionEnded -> (lin {(getHBidder : (! AuctionEnded)) (getHBid : (! AuctionEnded)) (win : (< (! AuctionEnded) + (! AuctionEnded) >)) (withdraw : (< (! AuctionEnded) + (! AuctionEnded) >)) (hasEnded : (! AuctionEnded)) })))})))}))
                       ;fields
                       {(var owner : Int)
                        (var ended : Bool)
                        (var highestBid : Int)
                        (var highestBidder : Int)}
                       ;methods
                       (Auction @ (anystate) :: (anycaller) {
                           (public func Auction () -> Void {return ((self -> owner = 9) ((self -> ended = false) ((self -> highestBid = 0) ((self -> highestBidder = 9) (become auctionRunning)))))})
                           (public func getHBidder () -> Int {return (self -> highestBidder)})
                           (public func getHBid () -> Int {return (self -> highestBid)})
                           (public func hasEnded () -> Bool {return (self -> ended)})
                           (public func withdraw ((bidder : Int)) -> Bool {return (if ((bidder != (self -> highestBidder))) {true} else {false})})
                       })
                          
                        
                       (Auction @ (auctionRunning) :: (owner) {
                        (public func endAuction () -> Void { return ((self -> ended = true) (become auctionEnded))})} )
                       (Auction @ (auctionRunning) :: (any_caller) {
                        (public func bid ((bid : Int) (bidder : Int)) -> Bool { return
                           (if ((bid > (self -> highestBid))) {(if ((bidder != (self -> highestBidder))) {((self -> highestBid = bid) ((self -> highestBidder = bidder) true))} else {false})} else {false})
                           }) })
                       (Auction @ (auctionEnded) :: (any_caller) {
                        (public func win ((bidder : Int)) -> Bool {return (if ((bidder == (self -> highestBidder))) {true} else {false})})})
                     
                           
                       )
                        (contract Main
                          ((lin{(main : (un{}))}))
                          {}
                          (Main @ (anystate) :: (anycaller) {
                           
                           (public func main () -> Void {return ((var a : (Auction[(lin {(getHBidder : (! AuctionRunning)) (hasEnded : (! AuctionRunning)) (withdraw : (< (! AuctionRunning) + (! AuctionRunning) >)) (bid : (< (! AuctionRunning) + (! AuctionRunning) >)) (getHBid : (! AuctionRunning)) (endAuction : (μ AuctionEnded -> (lin {(getHBidder : (! AuctionEnded)) (getHBid : (! AuctionEnded)) (win : (< (! AuctionEnded) + (! AuctionEnded) >)) (withdraw : (< (! AuctionEnded) + (! AuctionEnded) >)) (hasEnded : (! AuctionEnded)) })))})]) = (Auction -> init (4))) ((a -> getHBid()) (a -> endAuction()) ))})
                           
                       }))

                                 )
 _ _ _ _
                   
                   ))
|#


#|(judgment-holds (⊢ () () () () 
                       (
                        (contract Auction
                       ;usages
                       ((lin{(Auction : (lin {(getHBidder : (un{}))}))}))
                       ;((lin{(Auction : (μ AuctionRunning -> (lin {(getHBidder : (! AuctionRunning)) (hasEnded : (! AuctionRunning)) (withdraw : (< (! AuctionRunning) + (! AuctionRunning) >)) (bid : (< (! AuctionRunning) + (! AuctionRunning) >)) (getHBid : (! AuctionRunning)) (endAuction : (μ AuctionEnded -> (lin {(getHBidder : (! AuctionEnded)) (getHBid : (! AuctionEnded)) (win : (< (! AuctionEnded) + (! AuctionEnded) >)) (withdraw : (< (! AuctionEnded) + (! AuctionEnded) >)) (hasEnded : (! AuctionEnded)) })))})))}))
                       ;fields
                       {(var owner : Int)
                        (var ended : Bool)
                        (var highestBid : Int)
                        (var highestBidder : Int)}
                       ;methods
                       (Auction @ (anystate) :: (anycaller) {
                           (public func Auction () -> Void {return ((self -> owner = 9) ((self -> ended = false) ((self -> highestBid = 0) ((self -> highestBidder = 9) (become auctionRunning)))))})
                           (public func getHBidder () -> Int {return (self -> highestBidder)})
                           (public func getHBid () -> Int {return (self -> highestBid)})
                           (public func hasEnded () -> Bool {return (self -> ended)})
                           (public func withdraw ((bidder : Int)) -> Bool {return (if ((bidder != (self -> highestBidder))) {true} else {false})})
                       })
                          
                        
                       (Auction @ (auctionRunning) :: (owner) {
                        (public func endAuction () -> Void { return ((self -> ended = true) (become auctionEnded))})} )
                       (Auction @ (auctionRunning) :: (any_caller) {
                        (public func bid ((bid : Int) (bidder : Int)) -> Bool { return
                           (if ((bid > (self -> highestBid))) {(if ((bidder != (self -> highestBidder))) {((self -> highestBid = bid) ((self -> highestBidder = bidder) true))} else {false})} else {false})
                           }) })
                       (Auction @ (auctionEnded) :: (any_caller) {
                        (public func win ((bidder : Int)) -> Bool {return (if ((bidder == (self -> highestBidder))) {true} else {false})})})
                     
                           
                       )
                        (contract Main
                          ((lin{(main : (un{}))}))
                          {(var a : (Auction[(lin{(Auction : (lin {(getHBidder : (un{}))}))})]))}
                          (Main @ (anystate) :: (anycaller) {
                           
                           (public func main () -> Void {return ((a = (Auction -> init (4))) ((a -> Auction ()) (a -> getHBidder()))) })
                           
                       }))

                                 )
 _ _ _ _
                   
                   ))|#

#|(judgment-holds (⊢ () () () () 
                       
                        (contract Client
                       ;usages
                       ((lin{(Client : (μ canBid -> (lin {(bid : (< (lin {(withdraw : (! canBid))}) + (μ ISHB -> (lin{(isHB : (< (! ISHB) + (lin {(withdraw : (! canBid))}) >)) (hasEnded : (< (lin {(isHB : (< (lin {(win : (un{}))}) + (lin {(withdraw : (un{}))}) >))}) + (! ISHB) >))}))  >)) (hasEnded : (< (un{}) + (! canBid) >))})))}))
                       ;((lin{(Auction : (μ AuctionRunning -> (lin {(getHBidder : (! AuctionRunning)) (hasEnded : (! AuctionRunning)) (withdraw : (< (! AuctionRunning) + (! AuctionRunning) >)) (bid : (< (! AuctionRunning) + (! AuctionRunning) >)) (getHBid : (! AuctionRunning)) (endAuction : (μ AuctionEnded -> (lin {(getHBidder : (! AuctionEnded)) (getHBid : (! AuctionEnded)) (win : (< (! AuctionEnded) + (! AuctionEnded) >)) (withdraw : (< (! AuctionEnded) + (! AuctionEnded) >)) (hasEnded : (! AuctionEnded)) })))})))}))
                       ;fields
                       {(var auction : Int)
                        }
                       ;methods
                       (Client @ (anystate) :: (anycaller) {
                           (public func Client () -> Void {return ((self -> auction = 4) (become canBid))})
                           (public func hasEnded () -> Bool {return true})})
                       (Client @ (canBid) :: (anycaller) {
                        (public func bid ((bid : Int)) -> Bool { return true})} )
                       (Client @ (canWithdraw) :: (anycaller) {
                        (public func withdraw () -> Void { return
                           unit
                           }) })
                       (Client @ (isHB) :: (anycaller) {
                        (public func isHB ((bidder : Int)) -> Bool {return true})})
                       (Client @ (won) :: (anycaller) {
                        (public func win () -> Void {return unit})})
                           
                       )
                                                
 _ _ _ _
                   
                   ))|#

#|(judgment-holds (⊢ ()
                   ()
                   ()
                   ()
                   ((class Client {
                                        (lin{(Client : (μ canBid -> (lin {(bid : (< (lin {(withdraw : (! canBid))}) + (μ ISHB -> (lin{(isHB : (< (! ISHB) + (lin {(withdraw : (! canBid))}) >)) (hasEnded : (< (lin {(isHB : (< (lin {(win : (un{}))}) + (lin {(withdraw : (un{}))}) >))}) + (! ISHB) >))}))  >)) (hasEnded : (< (un{}) + (! canBid) >))})))})
                                       
                                        ;fields
                                        (bool ended)
                                        (int hBid)
                                        (String hBidder)
                                        ((Auction[(lin {(bid : (< (! AuctionRunning) + (! AuctionRunning) >)) (getHBidder : (! AuctionRunning)) (getHBid : (! AuctionRunning)) (hasEnded : (! AuctionRunning)) (endAuction : (μ AuctionEnded -> (lin {(getHBidder : (! AuctionEnded)) (getHBid : (! AuctionEnded)) (hasEnded : (! AuctionEnded)) })))})]) auction)
                                        ;methods
                                        (void Client(void x) {((this -> ended = false) ((this -> hBid = 0) ((this -> auction = (new Auction(unit))) (this -> hBidder = ""))))})
                                        (void endAuction(void x) {(this -> ended = true)} )
                                        (int getHBid(void x){(this -> hBid)}) 
                                        (bool hasEnded(void x){(this -> ended)})
                                        (String getHBidder(void x) {(this -> hBidder)})
                                        (bool bid(void x) {(this -> auction -> bid (unit))})
                                        (void withdraw(void x) {unit})
                                        (bool isHB(void x) {true})
                                        (void win(void x) {unit})
                                        })
                    (class Auction {
                                        (lin{(Auction : (μ AuctionRunning -> (lin {(bid : (< (! AuctionRunning) + (! AuctionRunning) >)) (getHBidder : (! AuctionRunning)) (getHBid : (! AuctionRunning)) (hasEnded : (! AuctionRunning)) (endAuction : (μ AuctionEnded -> (lin {(getHBidder : (! AuctionEnded)) (getHBid : (! AuctionEnded)) (hasEnded : (! AuctionEnded)) })))})))})
                                       
                                        ;fields
                                        (bool ended)
                                        (int hBid)
                                        (String hBidder)
                                        ;methods
                                        (void Auction(void x) {((this -> ended = false) ((this -> hBid = 0) (this -> hBidder = "")))})
                                        (void endAuction(void x) {(this -> ended = true)} )
                                        (int getHBid(void x){(this -> hBid)}) 
                                        (int hasEnded(void x){(this -> hBid)})
                                        (String getHBidder(void x) {(this -> hBidder)})
                                        (bool bid(void x) {(if true true else false)})
                                        }))
                    
                     
                   
                     
                   _ _ usages Γ))|#