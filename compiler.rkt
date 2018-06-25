#lang racket

;; Author:
;; Zach Cora (zcora)
;; Partner:
;; Austin Moore (aulmoore)

(require "interp.rkt")
(require "utilities.rkt")
(require "uncover-types.rkt")

(provide r3-passes)

(define reserved '(+ - * / cons car cdr expt add1 sub1 if let define and not eq? read vector vector-set! vector-ref lambda: inject project boolean? integer? vector? procedure? void))

(define type-predicates (set 'boolean?  'integer? 'vector? 'procedure?))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Expand macros (list, car/cdr variations)

(define expand-macros
  (lambda (e)
    (match e
      [`(program ,defines ... ,e)
       `(program ,@(map expand-macros defines) ,(expand-macros e))]
      [`(define (,f-name ,args ...) ,es)
       `(define (,f-name . ,args) ,(expand-macros es))]
      [`(list ,es ...)
       (expand-list (map expand-macros es))]
      [`(,s ,e) #:when (and (symbol? s) (list-access? (symbol->string s)))
       (expand-list-access (string->list (symbol->string s)) (expand-macros e))]
      [`(,e1 ...) (map expand-macros e1)]
      [e e])))

(define expand-list
  (lambda (ls)
    (cond
      [(null? ls) `()]
      [else `(cons ,(car ls) ,(expand-list (cdr ls)))])))

(define expand-list-access
  (lambda (s e)
    (match s
      [`(#\r) e]
      [`(#\a ,es ... #\r) `(car ,(expand-list-access `(,@es #\r) e))]
      [`(#\d ,es ... #\r) `(cdr ,(expand-list-access `(,@es #\r) e))]
      [`(#\c ,es ... #\r) (expand-list-access `(,@es #\r) e)])))

(define list-access?
  (lambda (s)
    (match (string->list s)
      [`(#\c ,es ... #\r) (if
                           (member #f (map (lambda (x) (or (equal? #\a x) (equal? #\d x))) es))
                           #f #t)]
      [else #f])))
      
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Adds type nodes

(define typecheck
  (lambda (env)
    (lambda (e)
      (match e
        [`() `(hasType ,e Null)]
        [(? fixnum?) `(hasType ,e Integer)]
        [(? boolean?) `(hasType ,e Boolean)]
        [`(vector ,es ...)
         (let ([e-types (map (typecheck env) es)])
         `(hasType (vector . ,e-types) (Vector . ,(map caddr e-types))))]
        [`(vector-ref ,vec ,index)
         (if (and (fixnum? index) (>= index 0))
             (let ([vec^ ((typecheck env) vec)])
               (match-let ([`(hasType ,e^ ,t) vec^])
                 (match t
                   [`(Vector ,es ...)
                    `(hasType (vector-ref ,vec^ ,index) ,(list-ref es index))]
                   [`Any
                    `(hasType (vector-ref ,vec^ ,index) Any)]
                 [else (error "vector-ref expects a vector:" e)])))
             (error "index in vector must be a constant, non-negative integer:" e))]
        [`(vector-set! ,vec ,index ,arg)
         (if (and (fixnum? index) (>= index 0))
             (let ([v-type ((typecheck env) vec)][a-type ((typecheck env) arg)])
               (match (caddr v-type)
                 [`(Vector ,t1 ...)
                  (if (>= index (length t1)) (error "vector-set!: index out of range")
                      `(hasType (vector-set! ,v-type ,index ,a-type) Void)
                      )]
                 [`Any `(hasType (vector-set! ,v-type ,index ,a-type) Void)]
                 [else (error "vector-set! requires a vector")]))
             (error "index in vector must be a constant, non-negative integer:" e))]
        [(? symbol?) `(hasType ,e ,(lookup e env))]
        [`(read) `(hasType ,e Integer)]
        [`(void) `(hasType ,e Void)]
        [`(- ,e)
         (let ([e-type ((typecheck env) e)])
           (if (consistant? (caddr e-type) 'Integer)
               `(hasType (- ,e-type) Integer) (error "'-' expects an Integer:" e)))]
        [`(add1 ,e)
         (let ([e-type ((typecheck env) e)])
           `(hasType (add1 ,e-type) Integer))]
        [`(sub1 ,e)
         (let ([e-type ((typecheck env) e)])
           `(hasType (sub1 ,e-type) Integer))]
        [`(+ ,e1 ,e2)
         (let ([e1-type ((typecheck env) e1)][e2-type ((typecheck env) e2)])
               `(hasType (+ ,e1-type ,e2-type) Integer)
               )]
        [`(* ,e1 ,e2)
         (let ([e1-type ((typecheck env) e1)][e2-type ((typecheck env) e2)])
           `(hasType (* ,e1-type ,e2-type) Integer)
           )]
        [`(/ ,e1 ,e2)
         (let ([e1-type ((typecheck env) e1)][e2-type ((typecheck env) e2)])
               `(hasType (/ ,e1-type ,e2-type) Integer)
               )]
        [`(expt ,e1 ,e2)
         (let ([e1-type ((typecheck env) e1)][e2-type ((typecheck env) e2)])
               `(hasType (expt ,e1-type ,e2-type) Integer)
               )]
        [`(cons ,e1 ,e2)
         (let ([e1-type ((typecheck env) e1)][e2-type ((typecheck env) e2)])
           `(hasType (cons ,e1-type ,e2-type) (Cons ,(caddr e1-type) ,(caddr e2-type)))
           )]
        [`(car ,e)
         (let ([e-type ((typecheck env) e)])
           `(hasType (car ,e-type) ,(cadr (caddr e-type))))]
        [`(cdr ,e)
         (let ([e-type ((typecheck env) e)])
           `(hasType (cdr ,e-type) ,(caddr (caddr e-type))))]
        [`(let ([,x ,e]) ,body)
         (let ([e-type ((typecheck env) e)])
           (match-let ([`(hasType ,e^ ,t) e-type])
             (let ([b-type ((typecheck `((,x . ,t) . ,env)) body)])
               `(hasType (let ([,x ,e-type]) ,b-type) ,(caddr b-type)))))]
        [`(and ,e1 ,e2)
         (let ([e1-type ((typecheck env) e1)][e2-type ((typecheck env) e2)])
           (if (and (consistant? (caddr e1-type) 'Boolean)
                    (consistant? (caddr e2-type) 'Boolean))
               `(hasType (and ,e1-type ,e2-type) Boolean)
               (error "'and' expects a Boolean:" e)))]
        [`(eq? ,e1 ,e2)
         (let ([e1-type ((typecheck env) e1)][e2-type ((typecheck env) e2)])
               `(hasType (eq? ,e1-type ,e2-type) Boolean))]
        [`(not ,e)
         (let ([e-type ((typecheck env) e)])
           (if (consistant? (caddr e-type) 'Boolean)
               `(hasType (not ,e-type) Boolean)
               (error "'not' expects a Boolean:" e)))]
        [`(if ,cnd ,thn ,els)
         (let ([cnd-type ((typecheck env) cnd)]
               [thn-type ((typecheck env) thn)]
               [els-type ((typecheck env) els)])
           `(hasType (if ,cnd-type ,thn-type ,els-type) Any))]
        [`(program ,defines ... ,e)
         (define defines^ (map convert-structures-to-static defines))
         (define g-env (map get-def-env-type defines^))
         (let ([d-types (map (typecheck g-env) defines^)]
               [e-type ((typecheck g-env) (convert-structures-to-static e))])
           `(program (type ,(caddr e-type)) (defines . ,(map cadr d-types)) ,e-type))]
        [`(define (,f-name ,args ...) ,es)
         `(define (,f-name . ,(map (lambda (x) `[,x : Any]) args)) : Any es)]
        [`(define (,f-name ,args ...) : ,type ,es)
         (let ([es-type ((typecheck (append (get-definition-env args) env)) es)])
           (if (consistant?
                type
                (caddr es-type))
             `(hasType (define (,f-name . ,args) : ,type ,es-type) ,(lookup f-name env))
             (error "function has incorrect return type:" e)))]
        [`(lambda (,args ...) ,es)
         `(lambda: ,(map (lambda (x) `[,x : Any]) args) : Any ,es)]
        [`(lambda: ([,xs : ,Ts] ...) : ,rT ,body)
          (define new-env (append (map cons xs Ts) env))
          (let ([b-type ((typecheck new-env) body)])
          (cond
            [(consistant? rT (caddr b-type))
             `(hasType (lambda: ,(cadr e) : ,rT ,b-type) (,@Ts -> ,rT))]
            [else (error"mismatch in return type" (caddr b-type) rT)]))]
        [`(inject ,e ,ty)
          (define new-e ((typecheck env) e))
          (cond
            [(consistant? (caddr new-e) ty) `(hasType (inject ,new-e ,ty) Any)]
            [else (error"inject expected ~a to have type ~a" e ty)])]
        [`(project ,e ,ty)
          (define new-e ((typecheck env) e))
          (cond
            [(consistant? (caddr new-e) `Any) `(hasType (project ,new-e ,ty) ,ty)]
            [else (error "project expected ~a to have type Any" e)])]
        [`(,pred ,e) #:when (set-member? type-predicates pred)
          (define new-e ((typecheck env) e))
          (cond
            [(consistant? (caddr new-e) `Any) `(hasType (,pred ,new-e) Boolean)]
            [else (error"~a expected arg. of type Any, not ~a" pred (caddr new-e))])]
        [`(,function ,args ...)
         (let ([f-type (match function
                         [`(,f ,args ...) ((typecheck env) function)]
                         [e ((typecheck env) function)])]
               [a-types (map (typecheck env) args)])
           (match (caddr f-type)
             [`Any `(hasType (,f-type . ,a-types) Any)]
             [`(,args^ ... -> ,T)
              (if (consistant? args^ (map caddr a-types))
                  `(hasType (,f-type . ,a-types) ,T)
                  (error (string-append
                          "Function "
                          (~a function)
                          " requires arguments of types "
                          (~a args^)
                          ": ") e))]))]))))

(define convert-structures-to-static
  (lambda (e)
    (match e
      [`(program ,defines ... ,e)
       (append
        `(program  . ,(map convert-structures-to-static defines))
        `(,(convert-structures-to-static e)))]
      [`(define (,f-name [,args : ,t] ...) : ,type ,es)
       `(define ,(cadr e)
          : ,type ,(convert-structures-to-static es))]
      [`(define (,f-name ,args ...) ,es)
       `(define (,f-name . ,(map (lambda (x) `[,x : Any]) args)) : Any
          ,(convert-structures-to-static es))]
      [`(lambda: ([,args : ,t] ...) : ,type ,es)
       `(lambda: ,(cadr e) : ,type ,(convert-structures-to-static es))]
      [`(lambda (,args ...) ,es)
       `(lambda: ,(map (lambda (x) `[,x : Any]) args) : Any
                 ,(convert-structures-to-static es))]
      [`(,e1 ...) (map convert-structures-to-static e1)]
      [else e])))

(define (consistant? t1 t2)
  (if (or (equal? t1 'Any) (equal? t2 'Any)) #t
      (match t1
        [e #:when (equal? e t2) #t]
        [`(Vector ,t ...)
         (match t2
           [`(Vector ,t^ ...) (not (member #f (map consistant? t t^)))]
           [else #f]
           )]
        [`(,args ... -> ,return)
         (match t2
           [`(,args^ ... -> ,return^) (and (consistant? return return^)
                                           (not (member #f (map consistant? args args^))))]
           [else #f]
           )]
        [`(,e1 ...)
         (match t2
           [`(,e2 ...) (not (member #f (map consistant? e1 e2)))]
           [else #f])]
        [else #f])))

(define (get-def-env-type define)
  (match define
    [`(define (,f-name ,args ...) : ,type ,es)
     `(,f-name . ,(append (map caddr args) `(-> ,type)))]
    [else (error "get-def-env-type recieved wrong format:" define)]))

(define (get-arg-types args)
  (match args
    [`() '()]
    [`([,arg-name : ,arg-type] ,args^ ...)
     (cons arg-type (get-arg-types args^))]))

(define (get-definition-env args)
  (match args
    [`() '()]
    [`([,arg-name : ,arg-type] ,args^ ...)
     `((,arg-name . ,arg-type) . ,(get-definition-env args^))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Gives unique variable names

(define uniquify
  (lambda (alist)
    (lambda (e)
      (match e
        [`() `()]
        [`(hasType ,e^ ,type)
         `(hasType ,((uniquify alist) e^) ,type)]
        [(? boolean?) e]
        [(? fixnum?) e]
        [(? symbol?) (let ([t (assv e alist)])
                       (match t
                         [`(,a . ,d) d]
                         [#f e]))]
        [`(read) `(read)]
        [`(,var : ,type)
         `(,((uniquify alist) var) : ,type)]
        [`(program ,type ,defines ,e)
         (let ([alist^ (find-new-functions (cdr defines))])
           `(program
             ,type
             (defines . ,((uniquify alist^) (cdr defines)))
             ,((uniquify alist^) e)))]
        [`(let ([,x ,e]) ,body) (let ([s (gensym x)])
                                 `(let ([,s ,((uniquify alist) e)])
                                    ,((uniquify `((,x . ,s) . ,alist)) body)))]
        [`((define (,f-name ,args ...) : ,type ,es) ,es^ ...)
         (let* ([arg-vars (find-new-args args)][bindings (append alist arg-vars)])
           `((define (,((uniquify alist) f-name) . ,(map (uniquify bindings) args)) :
               ,type
               ,((uniquify bindings) es)) . ,((uniquify alist) es^)))]
        [`(lambda: (,args ...) : ,type ,es)
         (let* ([arg-vars (find-new-args args)][bindings (append alist arg-vars)])
           `(lambda: ,(map (uniquify arg-vars) args) :
               ,type
               ,((uniquify alist) ((uniquify arg-vars) es))))]
        [`(,op ,es ...)
         (let ([f-name ((uniquify alist) op)])
           `(,f-name ,@(map(uniquify alist) es)))]))))

(define (find-new-args args)
  (match args
    [`() `()]
    [`((,var : ,type) ,args^ ...)
     (let ([s (gensym var)])
       `((,var . ,s) . ,(find-new-args args^)))]))

(define (find-new-functions defines)
  (match defines
    [`() `()]
    [`((define (,f-name ,args ...) : ,type ,es) ,es^ ...)
     (let ([s (gensym "fun")])
       `((,f-name . ,s) . ,(find-new-functions es^)))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;adds app/function-refs for function calls

(define (reveal-functions functions f-refs)
  (lambda (e)
    (match e
      [`(hasType ,e^ ,type) #:when (symbol? e^)
       (cond
         [(member e^ functions) `(hasType (function-ref ,e) _)]
         [(member e^ f-refs) `(hasType ,e^ (Vector _))]
         [else `(hasType ,e^ ,type)])]
      [`(hasType ,e^ ,type)
       `(hasType ,((reveal-functions functions f-refs) e^) ,type)]   
      [(? symbol?) (cond
                     [(member e functions) `(hasType (function-ref ,e) _)]
                     [(member e f-refs) `(hasType ,e (Vector _))]
                     [else e])]
      [`(program ,type (defines ,defines ...) ,es)
       (let ([functions^ (find-functions defines)])
         `(program ,type
                   (defines . ,(map (reveal-functions functions^ f-refs) defines))
                   ,((reveal-functions functions^ f-refs) es)))]
      [`(define (,f-name ,vars ...) : ,type ,e)
       (let ([arg-functions (get-arg-functions vars)])
         `(define (,f-name . ,vars) : ,type
            ,((reveal-functions  functions arg-functions) e)))]
      [`(lambda: (,vars ...) : ,type ,e)
       (let ([arg-functions (get-arg-functions vars)])
         `(lambda: ,vars : ,type
                   ,((reveal-functions  functions arg-functions) e)))]
      [`(let ([,var ,e]) ,body)
       (define let-functions (get-let-functions functions e var 0))
       (if (null? let-functions)
           `(let ([,var ,((reveal-functions functions f-refs) e)])
              ,((reveal-functions functions f-refs) body))
           `(let ([,var ,((reveal-functions functions f-refs) e)])
             ,((reveal-functions functions (append let-functions f-refs)) body)) 
           )]
      [`(,op ,args ...)
       (let ([op^ ((reveal-functions functions f-refs) op)])
         (if (member op^ reserved)
         `(,op^ .
               ,(map (reveal-functions functions f-refs) args))
         `(app ,op^ .
               ,(map (reveal-functions functions f-refs) args))))]
      [else e])))

(define (get-let-functions functions e var n)
  (match e
    [(? symbol?) (if (member e functions) `(,var) `())]
    [`(vector ,es ...) (get-let-functions functions es var n)]
    [`(,f ,es ...) (if (member f functions)
                        `((vector-ref ,var ,n) .
                          ,(get-let-functions functions es var (add1 n)))
                       (get-let-functions functions es var (add1 n)))]
    [`(,ex ,es ...) (get-let-functions functions es var (add1 n))]   
    [`() `()]
    [else '()]))

(define (find-functions defines)
  (match defines
    [`() `()]
    [`((define (,f-name ,args ...) : ,type ,e) ,es ...)
     (cons f-name (find-functions es))]
    [`(program ,type (defines ,defines ...) ,e) (find-functions defines)]))

(define (get-arg-functions args)
  (match args
    [`() `()]
    [`([,var : (,arg-types ... -> ,return-type)] ,args^ ...)
     `(,var . ,(get-arg-functions args^))]
    [else (get-arg-functions (cdr args))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;bad name, but it adds projects/injects wherever needed

(define convert-body-to-static
  (lambda (e)
    (match e
      [(? fixnum?) `(hasType (inject ,e Integer) Any)]
      [(? boolean?) `(hasType (inject ,e Boolean) Any)]
      [`(program (type ,t) (defines ,defines ...) ,e)
       `(program  (type Any)
                  (defines . ,(map convert-body-to-static defines)) ,(convert-body-to-static e))]
      [`(define (,f-name [,args : ,t] ...) : ,type ,es)
       `(define ,(cadr e) : ,type ,(convert-body-to-static es))]
      [`(lambda: ([,args : ,t] ...) : ,type ,es)
       `(lambda: ,(cadr e) : ,type ,(convert-body-to-static es))]
      [`(hasType ,e^ _)
       `(hasType ,(convert-body-to-static e^) _)]
      [`(hasType ,e^ Integer) #:when (fixnum? e^)
       `(hasType (inject ,e Integer) Any)]
      [`(hasType ,e^ Boolean) #:when (boolean? e^)
       `(hasType (inject ,e Boolean) Any)]
      [`(hasType ,e^ ,t) #:when (symbol? e^)
       `(hasType ,e^ Any)]
      [`(hasType ,e^ ,t)
       `(hasType ,(convert-body-to-static e^) Any)]
      [`(read) `(inject (hasType (read) Integer) Integer)]
      [`(void) `(inject (hasType (void) Void) Void)]
      [`() `(inject (hasType () Null) Null)]
      [`(add1 ,e)
       (let ([e^ (convert-body-to-static e)])
         `(inject
           (hasType
            (add1
             (hasType (project ,e^ Integer) Integer))
            Integer) Integer))]
      [`(sub1 ,e)
       (let ([e^ (convert-body-to-static e)])
         `(inject
           (hasType
            (sub1
             (hasType (project ,e^ Integer) Integer))
            Integer) Integer))]
      [`(+ ,e1 ,e2)
       (let ([e1^ (convert-body-to-static e1)][e2^ (convert-body-to-static e2)])
         `(inject
           (hasType
           (+
            (hasType (project ,e1^ Integer) Integer)
            (hasType (project ,e2^ Integer) Integer))
           Integer) Integer))]
      [`(* ,e1 ,e2)
       (let ([e1^ (convert-body-to-static e1)][e2^ (convert-body-to-static e2)])
         `(inject
           (hasType
           (*
            (hasType (project ,e1^ Integer) Integer)
            (hasType (project ,e2^ Integer) Integer))
           Integer) Integer))]
      [`(/ ,e1 ,e2)
       (let ([e1^ (convert-body-to-static e1)][e2^ (convert-body-to-static e2)])
         `(inject
           (hasType
           (/
            (hasType (project ,e1^ Integer) Integer)
            (hasType (project ,e2^ Integer) Integer))
           Integer) Integer))]
      [`(expt ,e1 ,e2) (let ([e1^ (convert-body-to-static e1)][e2^ (convert-body-to-static e2)])
         `(inject
           (hasType
           (expt
            (hasType (project ,e1^ Integer) Integer)
            (hasType (project ,e2^ Integer) Integer))
           Integer) Integer))]
      [`(cons ,e1 ,e2)
       (let ([e1^ (convert-body-to-static e1)][e2^ (convert-body-to-static e2)])
         `(inject
           (hasType
           (cons
            ,e1^
            ,e2^)
           Cons) Cons))]
      [`(car ,e1)
       (let ([e1^ (convert-body-to-static e1)])
         `(vector-ref
           (hasType (project ,e1^ Cons) (Vectorof Any)) 0))]
      [`(cdr ,e1)
       (let ([e1^ (convert-body-to-static e1)])
         `(vector-ref
            (hasType (project ,e1^ Cons) (Vectorof Any)) 1))]
      [`(- ,e1)
       (let ([e1^ (convert-body-to-static e1)])
         `(inject
           (hasType
           (-
            (hasType (project ,e1^ Integer) Integer))
           Integer) Integer))]
      [`(eq? ,e1 ,e2)
       (let ([e1^ (convert-body-to-static e1)][e2^ (convert-body-to-static e2)])
         `(inject (hasType (eq? ,e1^ ,e2^) Boolean) Boolean))]
      [`(and ,e1 ,e2)
       (let ([e1^ (convert-body-to-static e1)][e2^ (convert-body-to-static e2)])
         `(if (eq? ,e1^ (hasType (inject (hasType #f Boolean) Boolean) Any))
              (hasType (inject (hasType #f Boolean) Boolean) Any)
              ,e2^))]
      [`(not ,e1)
       (let ([e1^ (convert-body-to-static e1)])
         `(inject (hasType (not (hasType (project ,e1^ Boolean) Boolean)) Boolean) Boolean))]
      [`(if ,e1 ,e2 ,e3)
       (let ([e1^ (convert-body-to-static e1)]
             [e2^ (convert-body-to-static e2)]
             [e3^ (convert-body-to-static e3)])
         `(if (hasType
               (not (eq? ,e1^ (hasType (inject (hasType #f Boolean) Boolean) Any))) Boolean)
              ,e2^
              ,e3^))]
      [`(vector-ref ,e1 ,e2)
       (let ([e1^
              `(hasType
                (project ,(convert-body-to-static e1) (Vectorof Any))
                (Vectorof Any))]
             [v1 (gensym)])
         `(let ([,v1 ,e1^])
            (hasType (vector-ref ,v1 ,e2) Any)))]
      [`(vector-set! ,v ,i ,e)
       `(inject
         (hasType
          (vector-set!
           (hasType (project ,(convert-body-to-static v) (Vectorof Any)) (Vectorof Any))
           ,i
           ,(convert-body-to-static e))
          Void)
         Void)]
      [`(vector ,e1 ...)
       (define new-es (map convert-body-to-static e1))
       `(inject (hasType (vector . ,new-es) (Vectorof Any)) (Vectorof Any))]
      [`(app ,f ,e1 ...)
       (let ([f^ (convert-body-to-static f)]
             [e1^ (map convert-body-to-static e1)]
             [any-list (map (lambda (x) 'Any) e1)])
         `(app
           ,f^
           . ,e1^))]
      [`(,e1 ...) (map convert-body-to-static e1)]
      [e e])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;adds closure vectors where necessary

(define (convert-to-closures lambda-defines)
  (lambda (e)
    (match e
      [`(hasType (app (hasType (function-ref ,op) _)  ,args ...) ,type)
       (let ((tmp (gensym "tmp")))
         (let-values ([(new-args new-defines) (convert-args args)])
         (values 
          `(hasType
            (let ([,tmp (hasType (vector (hasType (function-ref ,op) _)) (Vector _))])
              (hasType
               (app
                (hasType (vector-ref (hasType ,tmp (Vector _)) 0) _)
                (hasType ,tmp (Vector _)) . ,new-args) ,type))
            ,type) new-defines)))]
      [`(program ,type (defines ,defines ...) ,es)
       (let-values ([(es^ defines^) ((convert-to-closures '()) es)])
         `(program ,type (defines . ,(append defines^ (convert-defines defines))) ,es^))]
      [`(hasType (lambda: ,vars : ,type ,es) ,t)
       (let-values ([(es^ new-defines) ((convert-to-closures '()) es)])
         (let ([f-name (gensym "lambda")]
               [c-name (gensym "clos")]
               [free-vars ((find-free vars) es)])
           (values
            `(hasType (vector (hasType (function-ref ,f-name) _) . ,free-vars)
                      (Vector _ . ,(map caddr free-vars)))
            `((define (,f-name (,c-name : (Vector _ . ,(map caddr free-vars))) . ,vars)
                : ,type ,(collect-free-vars free-vars c-name es^ 1)) . ,new-defines)
        )))]
      [`(hasType (lambda: ,stuff ...) ,type)
       (let-values ([(es^ new-defines) ((convert-to-closures '()) `(lambda: . ,stuff))])
         (values es^ new-defines))]
      [`(hasType (app (hasType (lambda: ,vars : ,type ,es) ,t) ,args ...) ,ta)
       (let-values ([(new-args new-defines^) (convert-args args)])
       (let-values ([(es^ new-defines) ((convert-to-closures '()) es)])
         (let ([f-name (gensym "lambda")]
               [c-name (gensym "clos")]
               [free-vars ((find-free vars) es)])
           (values
            `(hasType
              (let ([,c-name (hasType (vector (hasType (function-ref ,f-name) _)
                                              . ,free-vars)
                                      (Vector _ . ,(map caddr free-vars)))])
                (hasType
                 (app (hasType (vector-ref ,c-name 0) _) ,c-name . ,new-args)
                 ,(caddr es^))) ,(caddr es^))
            (append
             new-defines^
             `((define (,f-name (,c-name : (Vector _ . ,(map caddr free-vars))) . ,vars)
                 : ,(caddr es^) ,(collect-free-vars free-vars c-name es^ 1))
               . ,new-defines))))))]
      [`(hasType (app ,op ,args ...) ,type)
       (let-values ([(new-args new-defines) (convert-args args)])
         (define-values (op^ op-defines) ((convert-to-closures lambda-defines) op))
         (define new-var (gensym "tmp"))
         (values
          `(hasType
            (let ([,new-var ,op^])
              (hasType
               (app (hasType (vector-ref ,new-var 0) _) (hasType ,new-var ,(caddr op^))
                    . ,new-args) ,type))
            ,type)
        (append op-defines new-defines)))]
      [`(hasType (function-ref ,function) ,t)
       (let ([tmp (gensym "fref")])
         (values `(hasType
                   (let ([,tmp ,e]) (hasType (vector ,tmp) `(Vector _)))
                   (Vector _)) '()))]
      [`(function-ref ,function)
       (let ([tmp (gensym "fref")])
         (values `(let ([,tmp (hasType ,e _)]) (hasType (vector ,tmp) `(Vector _))) '()))]
      [`(let ([,var ,val]) ,es)
       (let-values ([(es^ new-defines) ((convert-to-closures '()) es)])
         (let-values ([(val^ new-defines2) ((convert-to-closures '()) val)])
           (values `(let ([,var ,val^]) ,es^)
                   (append new-defines new-defines2))))]
      [`(,op ,args ...)
       (let-values ([(args^ defines) ((convert-to-closures '()) args)])
         (let-values ([(op^ defines^) ((convert-to-closures '()) op)])
           (values `(,op^ . ,args^) (append defines defines^))))]
      [other (values other '())]
      [`(hasType ,e^ ,type)
       (let-values ([(es^ new-defines) ((convert-to-closures '()) e^)])
         (values `(hasType ,es^ ,type) new-defines))])))

(define (convert-args args)
  (match args
    [`() (values `() `())]
    [else
     (let-values ([(other-args other-defines) (convert-args (cdr args))]
                  [(es new-defines) ((convert-to-closures '()) (car args))])
       (values (cons es other-args) (append other-defines new-defines)))]))

(define (convert-defines defines)
  (match defines
    ['() '()]
    [`((define (,f-name ,vars ...) : ,type ,es) . ,other)
     (let-values ([(es^ new-defines) ((convert-to-closures '()) es)])
       (let ([c-name (gensym "clos")])
       (append `((define (,f-name (,c-name : (Vector _)) . ,vars) : ,type ,es^) . ,new-defines)
               (convert-defines other))))]
    ))

(define (collect-free-vars free-vars c-name es n)
  (match free-vars
    [`() es]
    [`(,first ,the-rest ...)
     `(hasType
       (let ([,(cadr first)
              (hasType
               (vector-ref (hasType ,c-name (Vector _ . ,(map caddr free-vars))) ,n)
               ,(caddr first))])
         ,(collect-free-vars the-rest c-name es (add1 n)))
       ,(caddr es))]))

(define find-free
  (lambda (vars)
    (lambda (e)
      (remove-duplicates
       (match e
         [`(hasType ,e^ ,t) #:when (symbol? e^)
          (if (and (not (member^ e^ vars)) (not (member e^ reserved))) (list e) '())]
         [`(hasType (lambda: ,vars^ : ,type ,es) ,t)
          ((find-free (append vars vars^)) es)]
         [`(hasType (,exp ,es ...) ,t)
          (append ((find-free vars) exp) ((find-free vars) es))]
         [`(,e1 ,e2 ...)
          (append ((find-free vars) e1) ((find-free vars) e2))]
         ['() '()]
         [else '()])))))

(define member^
  (lambda (sym list)
    (match list
      [`() #f]
      [`((,es ...) ,others ...) (or (member^ sym es) (member^ sym others))]
      [(? list?) (or (member^ sym (car list)) (member^ sym (cdr list)))]
      [(? symbol?) (if (eq? sym list) #t #f)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Remove excess project/injects

(define remove-excess
  (lambda (e)
    (match e
      [`(program ,type (defines ,defines ...) ,es)
       `(program ,type (defines . ,(map remove-excess defines)) ,(remove-excess es))]
      [`(define (,f-name ,args ...) : ,type ,es)
       `(define (,f-name . ,args) : ,type ,(remove-excess es))]
      [`(hasType
         (project
          (hasType
           (inject
            ,es
            ,t)
           Any)
          ,t)
         ,t) (remove-excess es)]
      [`(,e1 ...)
       (map remove-excess e1)]
      [e e])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;turns cons cells into vectors

(define lower-cons-cells
  (lambda (e)
    (match e
      [`() `()]
      [`(program ,type (defines ,defines ...) ,es)
       `(program ,type (defines . ,(map lower-cons-cells defines))
                 ,(lower-cons-cells es))]
      [`(define (,f-name ,args ...) : ,type ,es)
       `(define (,f-name . ,args) : ,type ,(lower-cons-cells es))]
      [`(hasType (cons ,a ,b) Cons)
       (let ([a^ (lower-cons-cells a)][b^ (lower-cons-cells b)])
         `(hasType (vector ,a^ ,b^) (Vector ,(caddr a^) ,(caddr b^))))]
      [`(,e1 ...)
       (map lower-cons-cells e1)]
      [e e])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;flattens into a list of instructions

(define flatten
  (lambda (islet)
    (lambda (e)
      (match e
        [(? symbol?) (values e '())]
        [`(hasType ,e^ ,t) #:when (boolean? e^) (values `(hasType ,e^ ,t) '())]
        [`(hasType ,e^ ,t) #:when (fixnum? e^) (values `(hasType ,e^ ,t) '())]
        [`(hasType ,e^ ,t) #:when (symbol? e^) (values `(hasType ,e^ ,t) '())]
        [`(hasType (read) Integer)
         (let ([s (gensym "read")])
           (values `(hasType ,s Integer) `((assign ,s (hasType (read) Integer)))))]
        [`(program (type ,type) ,defines ,e)
         (define-values (val assignments) ((flatten false) e))
         (define vars (find-vars assignments))
            (append `(program ,vars (type ,type) ,((flatten false) defines))
                    assignments
                    `((return ,val)))]
        [`(defines ,defs ...)
         (let ([flat (map (flatten false) defs)])
           (append `(defines)
                   flat))]
        [`(define (,name ,vars ...) : ,type ,e)
         (define-values (val assignments) ((flatten false) e))
         (append `(define (,name . ,vars) : ,type ,(find-vars assignments))
                 assignments
                 `((return ,val)))]
        [`(hasType (let ([,x ,exp]) ,body) ,t)
         (define-values (val assignments) ((flatten true) exp))
         (define-values (val^ assignments^) ((flatten islet) body))
         (values val^ (append assignments `((assign ,x ,val)) assignments^))]
        [`(hasType (if ,cnd ,thn ,els) ,t)
         (match (cadr cnd)
           [`(not ,e1) ((flatten islet) `(hasType (if ,e1 ,els ,thn) ,t))]
           [else
            (define-values (val_c assignments_c)
              (match cnd
                [`(eq? ,e1 ,e2) ((flatten true) cnd)]
                [else ((flatten false) cnd)]))
            (define-values (val_t assignments_t) ((flatten true) thn))
            (define-values (val_e assignments_e) ((flatten true) els))
            (let ([s (gensym "if")])
              (values `(hasType ,s ,t) (append assignments_c
                                `((hasType (if ,(match val_c
                                                 [`(eq? ,e1 ,e2) val_c]
                                                 [else `(eq? #t ,val_c)])
                                      ,(append assignments_t `((assign ,s ,val_t)))
                                      ,(append assignments_e `((assign ,s ,val_e))))
                                           ,t)))))])]
        [`(hasType (and ,e1 ,e2) Boolean)
         ((flatten islet) `(hasType (if ,e1 ,e2 (hasType #f Boolean)) Boolean))]
        [`(hasType (function-ref ,f) ,t)
         (if islet
             (values e '())
             (let ([s (gensym)])
               (values `(hasType ,s ,t) `((assign ,s ,e)))))]
        [`(hasType (vector ,e1 ...) (Vector ,t1 ...))
         (define-values (vals asslists) (map^ (flatten false) e1))
         (if islet
             (values `(hasType (vector . ,vals) (Vector . ,t1)) asslists)
             (let ([s (gensym)])
               (values `(hasType ,s (Vector . ,t1))
                       (append asslists
                               `((assign ,s ,`(hasType (vector . ,vals)
                                                       (Vector . ,t1))))))))]
        [`(hasType (vector-ref ,v ,i) ,t)
         (define-values (val asslist) ((flatten false) v))
         (if islet
             (values `(hasType (vector-ref ,val ,i) ,t) asslist)
             (let ([s (gensym)])
               (values `(hasType ,s ,t)
                       (append asslist
                               `((assign ,s (hasType (vector-ref ,val ,i) ,t)))))))]
        [`(hasType (vector-set! ,v ,i ,x) Void)
         (define-values (val asslist) ((flatten false) v))
         (define-values (xval xasslist) ((flatten false) x))
         (define new-asslist (append xasslist asslist))
         (if islet
             (values `(hasType (vector-set! ,val ,i ,xval) Void) new-asslist)
             (let ([s (gensym)])
               (values `(hasType ,s Void)
                       (append new-asslist
                               `((assign ,s
                                         (hasType (vector-set! ,val ,i ,xval) Void)))))))]
        [`(hasType (project ,e1 ,type) ,type)
         (let-values ([(e1^ assignments)  ((flatten false) e1)])
           (if islet
             (values `(hasType (project ,e1^ ,type) ,type) assignments)
             (let ([s (gensym)])
               (values `(hasType ,s ,type)
                       (append assignments
                               `((assign ,s (hasType (project ,e1^ ,type) ,type))))))))]
        [`(hasType (,op ,es ...) ,t)
         (define-values (vals asslists) (map^ (flatten false) es))
         (if islet
             (values `(hasType (,op . ,vals) ,t) asslists)
             (let ([s (gensym)])
               (values `(hasType ,s ,t)
                       (append asslists `((assign ,s (hasType ,(append `(,op) vals) ,t)))))))]
        [`(hasType ,vec (Vector ,t1 ...))
         (if islet
             (values e '())
             (let ([s (gensym)])
               (values `(hasType ,s (Vector . ,t1)) `((assign ,s ,e)))))]
        [`(eq? ,e1 ,e2)
         (define-values (e1-val e1-a) ((flatten false) e1))
         (define-values (e2-val e2-a) ((flatten false) e2))
         (values `(eq? ,e1-val ,e2-val) (append e1-a e2-a))]
        [e (values e '())]))))

(define (map^ f ls)
  (if (null? ls) (values '() '())
      (let-values ([(v1 v2) (map^ f (cdr ls))])
      (let-values ([(v1^ v2^) (f (car ls))])
        (values `(,v1^ . ,v1) (append v2^ v2))))))

(define find-vars
  (lambda (x)
    (match x
      [`() `()]
      [`((assign ,var (hasType ,val ,t)) ,es ...)
       (cons (cons var t) (find-vars es))]
      [`((hasType (if ,cnd ,thn ,els) ,t) ,es ...)
       (append
        (remove-duplicates
         (append
          (find-vars thn)
          (find-vars els)))
        (find-vars es))])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;reveals memory allocations

(define rootstack-size 1000)
(define heap-size 1000)

(define ((expose-allocation vars) e)
  (match e
    [`() (values '() '())]
    [`(program ,vars ,type (defines ,defines ...) ,es ...)
     (define function-types (map get-definition-type defines))
     (let-values ([(vars^^ es^) ((expose-allocation vars) es)])
       `(program ,vars^^ ,type (defines . ,(map (expose-allocation function-types) defines))
                 (initialize ,rootstack-size ,heap-size) . ,es^))]
    [`((assign ,lhs (hasType (vector ,es ...) ,t)) ,es^ ...)
     (let-values ([(vars^^ es^^) ((expose-allocation vars) es^)])
       (let* ([void-var (gensym "void")]
              [len (length es)]
              [bytes (* 8 (add1 len))])
         (values `((,void-var . Void) . ,vars^^)
                 (append
                  `((hasType (if (hasType (collection-needed? ,bytes) Boolean)
                        ((collect ,bytes))
                        ()) Void)
                    (assign ,lhs (hasType (allocate ,len) ,(lookup lhs vars))))
                  (void-assignments lhs void-var es)
                  es^^))))]
    [`(define (,f-name ,args ...) : ,type ,vars^ ,e^ ...)
       (let-values ([(new-vars-e new-e) ((expose-allocation (append vars vars^)) e^)])
         `(define (,f-name . ,args) : ,type
            ,(append (locate-voids new-vars-e) vars^)
            . ,new-e))]
    [`((hasType (if ,cnd ,thn, els) ,t) ,other ...)
     (let-values ([(other-vars other^) ((expose-allocation vars) other)])
       (let-values ([(thn-vars thn^) ((expose-allocation vars) thn)])
         (let-values ([(els-vars els^) ((expose-allocation vars) els)])
           (values
            (append
             (locate-voids thn-vars)
             (locate-voids els-vars)
             (locate-voids other-vars)
             vars)
            `((hasType (if ,cnd ,thn^ ,els^) ,t) . ,other^)))))]
    [`((return (hasType ,v ,t))) (values vars e)]
    [`(,something-else ,es ...)
     (let-values ([(vars^ es^) ((expose-allocation vars) es)])
       (values (remove-duplicates (append vars^ vars)) `(,something-else . ,es^)))]))

(define (find-list e ls)
  (cond
    [(null? ls) (error "find-list in expose-allocation")]
    [(member e (car ls)) (car ls)]
    [else (find-list e (cdr ls))]))

(define (void-assignments lhs void-var es)
  (letrec ([void-set
            (lambda (n es)
              (cond
                [(null? es) '()]
                [else
                 `((assign ,void-var (hasType (vector-set! ,lhs ,n ,(car es)) Void))
                   . ,(void-set (add1 n) (cdr es)))]))])
    (void-set 0 es)))

(define (locate-voids new-vars)
  (match new-vars
    [`() '()]
    [`((,var . Void) ,others ...) (cons (car new-vars) (locate-voids (cdr new-vars)))]
    [else  (locate-voids (cdr new-vars))]))

(define (get-definition-type define)
  (match define
    [`(define (,f-name ,args ...) : ,type ,es ...)
     (cons f-name (append (map caddr args) `(-> ,type)))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;reveals where the garbage collector might need to be called, and on what

(define uncover-call-live-roots
  (lambda (roots types)
    (lambda (e)
      (match e
        [`() (values roots `())]
        [`((assign ,var (hasType ,exp ,t)) ,es ...)
         (let-values ([(roots^ es^) ((uncover-call-live-roots roots types) es)])
           (match exp
             [`(vector-ref ,vec ,i)
              (match vec
                [`(hasType ,v ,t) (values (remove-duplicates `(,v . ,(remove var roots^)))
                      (cons (car e) es^))]
                [v (values (remove-duplicates `(,v . ,(remove var roots^)))
                      (cons (car e) es^))])]
             [`(vector-set! ,vec ,i ,arg)
              (if (symbol? arg)
                  (let ([T (lookup arg types)])
                    (match T
                      [`(Vector ,t1 ...)
                       (values (remove-duplicates `(,arg . ,roots^)) (cons (car e) es^))]
                      [else (values roots^ (cons (car e) es^))]))
                (values roots^ (cons (car e) es^)))]
             [else (values (remove var roots^) (cons (car e) es^))]
             ))]
        [`((hasType (if (hasType (collection-needed? ,bytes) Boolean)
               ((collect ,bytes))
               ()) Void) ,es ...)
         (let-values ([(roots^ es^) ((uncover-call-live-roots roots types) es)])
           (values roots^
                   `((hasType (if (hasType (collection-needed? ,bytes) Boolean)
                          ((call-live-roots ,roots^ (collect ,bytes)))
                          ()) Void) . ,es^)))]
        [`((hasType (if ,cond ,thn ,els) ,t) ,other ...)
         (let-values ([(other-roots other^) ((uncover-call-live-roots roots types) other)])
           (let-values ([(thn-roots thn^) ((uncover-call-live-roots other-roots types) thn)]
                        [(els-roots els^) ((uncover-call-live-roots other-roots types) els)])
             (values (remove-duplicates (append thn-roots els-roots))
                     `((hasType (if ,cond ,thn^ ,els^) ,t) . ,other^))))]
        [`(program ,vars ,type (defines ,defines ...) ,es ...)
         (define f-types (map get-definition-type defines))
         (let-values
             ([(roots^ es^)
               ((uncover-call-live-roots roots
                                         (append vars f-types)) es)])
           `(program ,(map car vars) ,type
                     (defines ,(map (uncover-call-live-roots roots f-types) defines))
                     . ,es^))]
        [`(define (,f-name ,args ...) : ,type ,vars ,es ...)
         (let-values ([(roots^ es^)
                       ((uncover-call-live-roots roots
                                                 (append types vars
                                                         (map (lambda (x)
                                                                (cons (car x) (caddr x)))
                                                              args))) es)])
           `(define (,f-name . ,args) : ,type ,(map car vars)
              . ,es^))]
        [`(,something_else ,es ...)
         (let-values ([(roots^ es^) ((uncover-call-live-roots roots types) es)])
           (values roots^ (cons (car e) es^)))]
        ))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;selects x86 instructions

(define (select-instructions vars rootstack)
  (lambda (e)
    (match e
      [`() (values vars '() 0)]
      [`((return (hasType ,val ,t))) (values vars `((movq ,(si-help val) (reg rax))) 0)]
      [`((initialize ,rootlen ,heaplen) ,es ...)
       (let ([s (gensym "rootstack")])
         (let-values ([(vars^ es^ stack-args) ((select-instructions vars s) es)])
           (values `(,s . ,vars^)
                   `((movq (int ,rootlen) (reg rdi))
                     (movq (int ,heaplen) (reg rsi))
                     (callq initialize)
                     (movq (global-value rootstack_begin) (var ,s)) .
                     ,es^) stack-args s)))]
      [`((assign ,lhs (hasType ,val ,t)) ,other ...)
       (let-values ([(vars^ es^ stack-args) ((select-instructions vars rootstack) other)])
         (match val
           [(or (? fixnum?) (? symbol?) (? boolean?))
            (values vars^ `((movq ,(si-help val) ,(si-help lhs)) . ,es^) stack-args)]
           [`(add1 ,x)
            (values vars^
                    `((movq ,(si-help x) ,(si-help lhs))
                      (inc ,(si-help lhs)) . ,es^) stack-args)]
           [`(sub1 ,x)
            (values vars^
                    `((movq ,(si-help x) ,(si-help lhs))
                      (dec ,(si-help lhs)) . ,es^) stack-args)]
           [`(+ ,x1 ,x2)
            (values vars^
                    `((movq ,(si-help x1) ,(si-help lhs))
                      (addq ,(si-help x2) ,(si-help lhs)) .
                      ,es^) stack-args)]
           [`(* ,x1 ,x2)
            (values vars^
                    `((movq ,(si-help x1) ,(si-help lhs))
                      (imul ,(si-help x2) ,(si-help lhs)) .
                      ,es^) stack-args)]
           [`(/ ,x1 ,x2)
            (define new-var (gensym))
            (values `(,new-var . ,vars^)
                    `((movq ,(si-help x1) (var ,new-var))
                      (cmpq (int 0) (var ,new-var))
                      (setl (byte-reg al))
                      (movzbq (byte-reg al) ,(si-help lhs))
                      (if (eq? ,(si-help #t) ,(si-help lhs))
                          ((movq (var ,new-var) (reg rax))
                           (negq (reg rax))
                           (movq ,(si-help x2) (var ,new-var))
                           (cdq)
                           (idiv (var ,new-var))
                           (negq (reg rax))
                           (movq (reg rax) ,(si-help lhs)))
                          ((movq (var ,new-var) (reg rax))
                           (movq ,(si-help x2) (var ,new-var))
                           (cdq)
                           (idiv (var ,new-var))
                           (movq (reg rax) ,(si-help lhs)))) .
                           ,es^) stack-args)]
           [`(expt ,x1 ,x2)
            (define label (gensym "expt"))
            (define new-var (gensym))
            (values `(,new-var . , vars^)
                    `((movq (int 1) ,(si-help lhs))
                      (movq ,(si-help x2) (var ,new-var))
                      (label ,label)
                      (if (eq? (int 0) (var ,new-var))
                          ()
                          ((imul ,(si-help x1) ,(si-help lhs))
                           (dec (var ,new-var))
                           (jmp ,label))) . ,es^) stack-args)]
           [`(- ,x1)
            (values vars^
                    `((movq ,(si-help x1) ,(si-help lhs))
                      (negq ,(si-help lhs)) .
                      ,es^) stack-args)]
           [`(read)
            (values vars^
                    `((callq read_int)
                      (movq (reg rax) (var ,lhs)) .
                      ,es^) stack-args)]
           [`(void)
            (values vars^
                    `((movq (int 0) ,(si-help lhs)) .
                      ,es^) stack-args)]
           [`(not ,e1)
            (values vars^
                    `((movq ,(si-help e1) ,(si-help lhs))
                      (xorq ,(si-help 1) ,(si-help lhs)) .
                      ,es^) stack-args)]
           [`(eq? ,e1 ,e2)
            (values vars^
                    `((cmpq ,(si-help e1) ,(si-help e2))
                      (sete (byte-reg al))
                      (movzbq (byte-reg al) ,(si-help lhs)) .
                      ,es^) stack-args)]
           [`(vector-ref ,vec ,n)
            (values vars^
                    `((movq (offset ,(si-help vec) ,(* 8 (add1 n))) ,(si-help lhs)) .
                      ,es^) stack-args)]
           [`(vector-set! ,vec ,n ,arg)
            (values vars^
                    `((movq ,(si-help arg) (offset ,(si-help vec) ,(* 8 (add1 n)))) .
                      ,es^) stack-args)]
           [`(allocate ,len)
            (values vars^
                    `((movq (global-value free_ptr) ,(si-help lhs))
                      (addq (int ,(* 8 (add1 len))) (global-value free_ptr))
                      (movq (int ,(calculate-tag len t)) (offset ,(si-help lhs) 0)) .
                      ,es^) stack-args)]
            [`(function-ref (hasType ,f ,t))
            (values vars^
                    `((leaq (function-ref ,f) ,(si-help lhs)) . ,es^) stack-args)]
           [`(function-ref ,f)
            (values vars^
                    `((leaq (function-ref ,f) ,(si-help lhs)) . ,es^) stack-args)]
           [`(app (hasType ,fun ,t) ,args ...)
            (values vars^
                    (append (move-arguments args 0)
                            `((indirect-callq (var ,fun)) (movq (reg rax) ,(si-help lhs)) .
                              ,es^)) (max stack-args (length args)))]
           [`(inject (hasType ,val ,v-type) ,t)
            (match t
              [`(Vector ,t1 ...)
               (values vars^
                       `((movq ,(si-help val) ,(si-help lhs))
                         (orq (int ,(tagof t)) ,(si-help lhs)) .
                         ,es^)
                       stack-args)]
              [(or `(Vectorof Any) `Cons)
               (values vars^
                       `((movq ,(si-help val) ,(si-help lhs))
                         (orq (int ,(tagof t)) ,(si-help lhs)) .
                         ,es^)
                       stack-args)]
              [`(,t1 ... -> ,tr)
               (values vars^
                       `((movq ,(si-help val) ,(si-help lhs))
                         (orq (int ,(tagof t)) ,(si-help lhs)) .
                         ,es^)
                       stack-args)]
              [else
               (values vars^
                       `((movq ,(si-help val) ,(si-help lhs))
                         (salq (int 3) ,(si-help lhs))
                         (orq (int ,(tagof t)) ,(si-help lhs)) .
                         ,es^)
                       stack-args)])]
           [`(project (hasType ,val ,v-type) ,t)
            (match t
              [`(Vector ,t1 ...)
               (values vars^
                       `((movq ,(si-help val) ,(si-help lhs))
                         (andq (int 7) ,(si-help lhs))
                         (if (eq? ,(si-help lhs) ,(si-help (tagof t)))
                             ((movq (int 7) ,(si-help lhs))
                              (notq ,(si-help lhs))
                              (andq ,(si-help val) ,(si-help lhs)))
                             ((callq exit))) .
                         ,es^)
                       stack-args)]
              [(or `(Vectorof Any) `Cons)
               (values vars^
                       `((movq ,(si-help val) ,(si-help lhs))
                         (andq (int 7) ,(si-help lhs))
                         (if (eq? ,(si-help lhs) ,(si-help (tagof t)))
                             ((movq (int 7) ,(si-help lhs))
                              (notq ,(si-help lhs))
                              (andq ,(si-help val) ,(si-help lhs)))
                             ((callq exit))) .
                         ,es^)
                       stack-args)]
              [`(,t1 ... -> ,tr)
               (values vars^
                      `((movq ,(si-help val) ,(si-help lhs))
                        (andq (int 7) ,(si-help lhs))
                        (if (eq? ,(si-help lhs) ,(si-help (tagof t)))
                            ((movq (int 7) ,(si-help lhs))
                             (notq ,(si-help lhs))
                             (andq ,(si-help val) ,(si-help lhs)))
                            ((callq exit))) .
                        ,es^)
                       stack-args)]
              [else
               (values vars^
                       `((movq ,(si-help val) ,(si-help lhs))
                         (andq (int 7) ,(si-help lhs))
                         (if (eq? ,(si-help lhs) ,(si-help (tagof t)))
                             ((movq ,(si-help val) ,(si-help lhs))
                              (sarq (int 3) ,(si-help lhs)))
                             ((callq exit))) .
                         ,es^)
                       stack-args)])]
           [`(,pred (hasType ,val ,t)) #:when (set-member? type-predicates pred)
            (define tag (tagof (type-of pred)))
            (values vars^
                    `((movq ,(si-help val) ,(si-help lhs))
                      (andq (int 7) ,(si-help lhs))
                      (if (eq? ,(si-help tag) ,(si-help lhs))
                          ((movq ,(si-help #t) ,(si-help lhs)))
                          ((movq ,(si-help #f) ,(si-help lhs)))) .
                      ,es^)
                    stack-args)]
            ))]
      [`((hasType (if (hasType (collection-needed? ,bytes) Boolean) ,thn ,els) Void) ,es ...)
       (let*-values ([(vars^ es^ sa) ((select-instructions vars rootstack) es)]
                     [(vars^^ thn^ thn-sa) ((select-instructions vars^ rootstack) thn)]
                     [(vars^^^ els^ els-sa) ((select-instructions vars^^ rootstack) els)])
         (let ([end-var (gensym "end-data")][lt-var (gensym "lt")])
           (values `(,end-var ,lt-var . ,vars^)
                   `((movq (global-value free_ptr) (var ,end-var))
                     (addq (int ,bytes) (var ,end-var))
                     (cmpq (var ,end-var) (global-value fromspace_end))
                     (setl (byte-reg al))
                     (movzbq (byte-reg al) (var ,lt-var))
                     (if (eq? (int 0) (var ,lt-var)) ,els^ ,thn^) .
                     ,es^) (max sa thn-sa els-sa))))]
      [`((hasType (if (eq? ,var ,val)  ,thn ,els) ,t) ,es ...)
       (let*-values ([(vars^ es^ sa) ((select-instructions vars rootstack) es)]
                     [(vars^^ thn^ thn-sa) ((select-instructions vars^ rootstack) thn)]
                     [(vars^^^ els^ els-sa) ((select-instructions vars^^ rootstack) els)])
                    (values vars^^^
                            `((if (eq? ,(si-help var) ,(si-help val)) ,thn^ ,els^) .
                              ,es^)
                            (max sa thn-sa els-sa)))]
      [`((call-live-roots ,live-roots (collect ,bytes)))
       (values vars
               (append
                (move-live-roots live-roots rootstack 'to)
                `((movq ,(si-help rootstack) (reg rdi)))
                (if (null? live-roots) '() `((addq (int ,(* 8 (length live-roots))) (reg rdi))))
                `((movq (int ,bytes) (reg rsi))
                  (callq collect))
                (move-live-roots live-roots rootstack 'from)) 0)]
      [`(program ,vars^ ,type (defines ,defines) ,es ...)
       (let-values ([(vars^^ es^ sa RS) ((select-instructions vars^ rootstack) es)])
         (let ([defines^ (map (select-instructions vars RS) defines)])
           `(program
             (,(remove-duplicates
                (append vars^^ (get-arguments defines) (get-vars defines^))) ,(max 0 (- sa (vector-length arg-registers)))) ,type
                   (defines . ,defines^) . ,es^)))]
      [`(define (,f-name ,args ...) : ,type ,vars^ ,es ...)
       (let-values ([(vars^^ es^ sa) ((select-instructions vars^ rootstack) es)])
         `(define (,f-name) ,(length args)
            (,(append (map car args) vars^^) ,(max 0 (- sa (vector-length arg-registers))))
            . ,(append (collect-arguments args 0) es^)))]
      [else
       (let-values ([(vars^ es^ sa) ((select-instructions vars rootstack) (cdr e))])
         (values vars^ `(,(car e) . ,es^) sa))]
      )))

(define (tagof t)
  (match t
    [`Integer 0]
    [`Boolean 1]
    [`(Vector ,t1 ...) 2]
    [`(Vectorof ,t1) 2]
    [`(,t1 ... -> ,tr) 3]
    [`Void 4]
    [`Cons 5]
    [`Null 6]))

(define (type-of p)
  (match p
    [`boolean? `Boolean]
    [`integer? `Integer]
    [`vector? `(Vector _)]
    [`procedure? `(Thing -> Thing)]
    [`void? `Void]))

(define (get-arguments defines)
  (match defines
    [`() `()]
    [`((define (,f-name ,args ...) : ,type ,vars^ ,es ...) ,others ...)
     (append (map car args) vars^ (get-arguments others))]))

(define (get-vars defines)
  (match defines
    [`() `()]
    [`((define (,f-name) ,args (,vars ,sa) ,es ...) ,others ...)
     (append vars (get-vars others))]))

(define (move-arguments args n)
  (if (null? args) '()
  (let ([num_registers (vector-length arg-registers)])
    (if (< n num_registers)
        `((movq ,(si-help (car args)) (reg ,(vector-ref arg-registers n))) .
          ,(move-arguments (cdr args) (add1 n)))
        `((movq ,(si-help (car args)) (stack-arg ,(* 8 (- n num_registers))))
          . ,(move-arguments (cdr args) (add1 n)))))))

(define (collect-arguments args n)
  (if (null? args) '()
      (let ([num_registers (vector-length arg-registers)])
        (match (car args)
          [`(,var : ,type)
           (if (< n num_registers)
               `((movq (reg ,(vector-ref arg-registers n)) ,(si-help var)) .
                 ,(collect-arguments (cdr args) (add1 n)))
               `((movq
                  (offset (reg rbp) ,(+ 16 (* 8 (- n num_registers)))) ,(si-help var))
                 . ,(collect-arguments (cdr args) (add1 n))))]))))
  
(define si-help
  (lambda (e)
    (match e
      [`() `(int 0)]
      [`(hasType ,e ,t) (si-help e)]
      [`rax `(reg rax)]
      [(? symbol?) `(var ,e)]
      [(? fixnum?) `(int ,e)]
      [(? boolean?) (if e (si-help 1) (si-help 0))]
      [`(,op ,es ...) e])))

(define (move-live-roots live-roots rootstack-var direction)
  (letrec
      ([move-roots
        (lambda (n roots)
          (if (null? roots) '()
              (let ([next (move-roots (add1 n) (cdr roots))])
                (match direction
                  ['to
                   `((movq (var ,(car roots)) (offset (var ,rootstack-var) ,(* 8 n))) .
                     ,next)]
                  ['from
                   `((movq (offset (var ,rootstack-var) ,(* 8 n)) (var ,(car roots))) .
                     ,next)]
                  [else (error "move-live-roots requires a direction ('to or 'from)")]
                  ))))])
    (move-roots 0 live-roots)))

(define (calculate-tag len type)
  (let ([n (+ 1 (* 2 len))])
    (add-types n (cdr type) 7)))

(define (add-types tag type n)
  (cond
    [(> n 56) (error "vectors limited to length 50")]
    [(null? type) tag]
    [else (add-types
           (match (car type)
             [`(Vector ,es ...) (+ tag (expt 2 n))]
             [else tag])
           (cdr type)
           (add1 n))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;uncovers what variables are live at what times

(define uncover-live
  (lambda (after)
    (lambda (e)
      (match e
        ['() (values (list after) e)]
        [`(int ,x) `()]
        [`(var ,x) (list x)]
        [`(reg ,x) `()]
        [`(stack-arg ,n) '()]
        [`(offset (var ,var) ,n) (list var)]
        [`(offset (reg ,reg) ,n) `()]
        [`(global-value ,var) '()]  
        [`((callq ,function) ,es ...)
         (let-values ([(x es^) ((uncover-live after) es)])
           (values `(,(car x) . ,x) `((callq ,function) . ,es^)))]
        [`((indirect-callq ,function) ,es ...)
         (let-values ([(x es^) ((uncover-live after) es)])
           (values `(,(append ((uncover-live after) function) (car x)) . ,x) `((indirect-callq ,function) . ,es^)))]
        [`((movq ,a ,b) ,es ...)
         (let-values ([(x es^) ((uncover-live after) es)])
           (define b-vars (match b
                            [`(offset ,var ,n) ((uncover-live '()) b)]
                            [e `()]))
           (define-values (thing1 thing2)
             (values `(,(remove-duplicates
                         (append ((uncover-live '()) a) b-vars
                                 (remove* ((uncover-live '()) b) (car x))))
                       . ,x) `((movq ,a ,b) . ,es^)))
           (match b
             [`(var ,v) (if (not (member v (car x))) (values x es^) (values thing1 thing2))]
             [e (values thing1 thing2)]
           ))]
        [`((movzbq ,a ,b) ,es ...)
         (let-values ([(x es^) ((uncover-live after) es)])
           (define b-vars ((uncover-live '()) b))
           (define in-after (map (lambda (y) (member y (car x))) b-vars))
           (if (member #f in-after) (values x es^)
           (values `(,(remove* ((uncover-live '()) b) (car x)) . ,x)
                   `(,(car e) . ,es^))))]
        [`((leaq ,a ,b) ,es ...)
         (let-values ([(x es^) ((uncover-live after) es)])
           (define b-vars ((uncover-live '()) b))
           (define in-after (map (lambda (y) (member y (car x))) b-vars))
           (if (member #f in-after) (values x es^)
           (values `(,(remove* ((uncover-live after) b) (car x)) . ,x)
                   `(,(car e) . ,es^))))]
        [`((if ,cnd ,thn ,els) ,es ...)
         (let-values ([(x es^) ((uncover-live after) es)])
           (let-values ([(thn-lives thn-es) ((uncover-live (car x)) thn)]
                        [(els-lives els-es) ((uncover-live (car x)) els)])
             (if (and (null? thn-es) (null? els-es)) (values x es^)
             (values `(,(remove-duplicates (append (vars-from-eq cnd) (car thn-lives) (car els-lives))) . ,x)
                     `((if ,cnd ,thn-es ,(cdr thn-lives) ,els-es ,(cdr els-lives)) . ,es^)))))]
         [(or `((negq ,a) ,es ...) `((notq ,a) ,es ...))
          (let-values ([(x es^) ((uncover-live after) es)])
            (values
             `(,(remove-duplicates (append ((uncover-live '()) a) (car x))) . ,x)
             `(,(car e) . ,es^)))]
        [`((sete ,thing) ,es ...)
         (let-values ([(x es^) ((uncover-live after) es)])
           (values `(,(car x) . ,x) `((sete ,thing) . ,es^)))]
        [`((setl ,thing) ,es ...)
         (let-values ([(x es^) ((uncover-live after) es)])
           (values `(,(car x) . ,x) `((setl ,thing) . ,es^)))]
        [`(program (,vars ,sa) ,type (defines ,defines ...) ,es ...)
         (let-values ([(la es^) ((uncover-live after) es)])
           `(program (,vars ,(cdr la) ,sa) ,type
                     (defines . ,(map (uncover-live after) defines)) . ,es^))]
        [`(define (,f-name) ,args (,vars ,sa) ,es ...)
         (let-values ([(la es^) ((uncover-live after) es)])
           `((define (,f-name) ,args (,vars ,sa) . ,es^) . ,(cdr la)))]
        [`((cmpq ,a ,b) ,es ...)
         (let-values ([(x es^) ((uncover-live after) es)])
            (values
             `(,(remove-duplicates
                (append ((uncover-live '()) a) ((uncover-live '()) b) (car x))) . ,x)
             `(,(car e) . ,es^)))]
        [`((idiv ,thing) ,es ...)
         (let-values ([(x es^) ((uncover-live after) es)])
           (values `(,(append ((uncover-live '()) thing) (car x)) . ,x)
                   `((idiv ,thing) . ,es^)))]
        [`((inc ,a) ,es ...)
         (let-values ([(x es^) ((uncover-live after) es)])
           (values `(,(remove-duplicates (append ((uncover-live '()) a) (car x))) . ,x)
                   `(,(car e) . ,es^)))]
        [`((dec ,a) ,es ...)
         (let-values ([(x es^) ((uncover-live after) es)])
           (values `(,(remove-duplicates (append ((uncover-live '()) a) (car x))) . ,x)
                   `(,(car e) . ,es^)))]
        [`((,instruction ,a ,b) ,es ...) #:when (member instruction reads-both)
         (let-values ([(x es^) ((uncover-live after) es)])
           (define b-vars ((uncover-live '()) b))
           (define in-after (map (lambda (y) (member y (car x))) b-vars))
           (if (member #f in-after) (values x es^)
            (values
             `(,(remove-duplicates
                (append ((uncover-live '()) a) ((uncover-live '()) b) (car x))) . ,x)
             `(,(car e) . ,es^))))]
        [`(,inst ,es ...)
         (let-values ([(x es^) ((uncover-live after) es)])
           (values `(,(car x) . ,x) `(,inst . ,es^)))]
        ))))

(define reads-both `(sarq salq orq andq cmpq xorq addq imul))

(define (vars-from-eq eq)
  (match eq
    [`(reg ,r) '()]
    [`(int ,n) '()]
    [`(var ,v) (list v)]
    [`(eq? ,e1 ,e2) (append (vars-from-eq e1) (vars-from-eq e2))]
    [else '()]
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;builds interference graph of variables

(define (build-interference live-after graph)
  (lambda (e)
    (match e
      [`() graph]
      [`(program (,vars ,la ,sa) ,type (defines ,defines ...) ,es ...)
       (let ([g ((build-interference la (make-graph vars)) es)])
         (map (lambda (def) ((build-interference (cdr def) g) (car def))) defines)
         `(program (,vars ,g ,sa) ,type (defines . ,(map car defines)) . ,es))]
      [`(define (,f-name) ,args (,vars ,sa) ,es ...)
       ((build-interference live-after graph) es)]
      [`((callq exit) ,es ...)
       ((build-interference (cdr live-after) graph) es)]
      [`((callq ,function) ,es ...)
       (let ([caller-save '(1 2 3 4 5 6 7 8)])
         (map (lambda (v)
                (map (lambda (w)
                       (add-edge graph w v)) caller-save)) (car live-after))
         ((build-interference (cdr live-after) graph) es))]
      [`((indirect-callq (var ,function)) ,es ...)
       (let ([caller-save '(1 2 3 4 5 6 7 8)])
         (map (lambda (v)
                (map (lambda (w)
                       (add-edge graph w v)) caller-save)) (car live-after))
         (map (lambda (v) (add-edge graph v function)) caller-save)
         (map (lambda (v) (add-edge graph v function)) (car live-after))
         ((build-interference (cdr live-after) graph) es))]
      [`((movq ,a ,b) ,es ...)
       (define index (get-vector-index arg-registers (cadr a) 0))
       (if index (map (lambda (v) (add-edge graph v (vector-ref arg-reg-conversions index)))
                      (car live-after)) 42)
       (define index2 (get-vector-index arg-registers (cadr b) 0))
       (if index2
           (map (lambda (v) (add-edge graph v (vector-ref arg-reg-conversions index2)))
                (car live-after)) 42)  
       (match b
         [`(var ,x)
          (map (lambda (v)
                 (cond
                   [(and (not (eq? x v))
                         (not (eq? v (match a
                                       [`(var ,c) c]
                                       [a a]))))
                    (add-edge graph x v)])) (car live-after))
          ((build-interference (cdr live-after) graph) es)]
         [`(offset (var ,x) ,n)
          (map (lambda (v)
                 (cond
                   [(and (not (eq? x v))
                         (not (eq? v (match a
                                       [`(var ,c) c]
                                       [a a]))))
                    (add-edge graph x v)])) (car live-after))
          ((build-interference (cdr live-after) graph) es)]
         [`(reg ,reg) ((build-interference (cdr live-after) graph) es)]
         [`(stack-arg ,n) ((build-interference (cdr live-after) graph) es)])]
      [(or `((andq ,a ,b) ,es ...) `((addq ,a ,b) ,es ...) `((imul ,a ,b) ,es ...))
       (match b
         [`(var ,x) (map (lambda (v)
                           (if (not (eq? x v)) (add-edge graph x v) void))
                         (car live-after))
          ((build-interference (cdr live-after) graph) es)]
         [`(global-value ,gv) ((build-interference (cdr live-after) graph) es)]
         [`(reg ,reg) ((build-interference (cdr live-after) graph) es)])]
      [`((cdq) (idiv ,a) ,es ...)
       (map (lambda (v)
              (add-edge graph 2 v))
            (car live-after))
       ((build-interference (cddr live-after) graph) es)]
      [(or `((negq ,a) ,es ...) `((notq ,a) ,es ...))
       ((build-interference (cdr live-after) graph) es)]
      [`((,instruction ,a ,b) ,es ...) #:when (member instruction no-interference)
       ((build-interference (cdr live-after) graph) es)]
      [`((leaq ,a ,b) ,es ...) ((build-interference live-after graph) `((movq (int 0) ,b) . ,es))]
      [(or `((sete ,a) ,es ...) `((setl ,a) ,es ...) `((inc ,a) ,es ...) `((dec ,a) ,es ...))
       ((build-interference (cdr live-after) graph) es)]
      [`((movzbq ,a ,b) ,es ...)
         (match b
           [`(var ,x)
            (map (lambda (v)
                   (cond
                     [(not (eq? x v))
                      (add-edge graph x v)])) (car live-after))
            ((build-interference (cdr live-after) graph) es)]
           [`(reg rax) ((build-interference (cdr live-after) graph) es)])]
       [`((if ,cnd ,thn ,thn-la ,els ,els-la) ,es ...)
         ((build-interference thn-la graph) thn)
         ((build-interference els-la graph) els)
         ((build-interference (cdr live-after) graph) es)]
      [(or `((label ,label) ,es ...) `((jmp ,label) ,es ...))
       ((build-interference (cdr live-after) graph) es)])))

(define no-interference `(sarq salq orq cmpq xorq))

(define (get-vector-index vector e n)
  (if (>= n (vector-length vector)) #f
  (cond 
    [(equal? e (vector-ref vector n)) n]
    [else (get-vector-index vector e (add1 n))])))

(define arg-reg-conversions (vector 4 3 2 1 5 6))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;allocates registers to variables based on interference graph

(define allocate-registers
  (lambda (e)
    (match e
      [`(program (,vars ,graph ,sa) ,type (defines ,defines ...) ,es ...)
       (let ([move-graph (graph-moves (make-graph vars) es)])
         (map (lambda (def)
                (match def
                  [`(define (,f-type) ,args (,vars ,sa) ,es^ ...)
                   (graph-moves move-graph es^)]))
              defines)
         `(program (,sa . ,(allocate-homes graph vars move-graph)) ,type
                   (defines . ,defines) . ,es))])))
                      
(define allocate-homes
  (lambda (graph vars move-graph)
    (cond
      [(null? vars) `(0 () ())]
      [else
       (let* ([v (find-least-saturated graph vars)]
              [moves (adjacent move-graph v)])
         (match-let* ([`(,n ,cs ,assigned) (allocate-homes graph (remove v vars) move-graph)])
           (let* ([adj (adjacent graph v)]
                  [reg (assign-register graph v adj moves assigned)])
             (set-map adj (lambda (a) (add-edge graph a reg)))
             `(,(if (>= reg (vector-length registers-for-alloc)) (add1 n) n)
               ,(match-let ([`(,something ,register) (find-register reg)])
                  (if (set-member? callee-save register)
                      (cons register cs)
                      cs))
               ((,v . ,reg) . ,assigned)))))])))

(define assign-register
  (lambda (graph v adj moves assigned)
    (cond
      [(or (set-empty? moves) (null? assigned))
       (let ([reg (lowest-reg adj 0)])
         reg)]
      [else
       (let ([first (set-first moves)])
         (match-let ([a (assv first assigned)])
         (if (or (not a) (set-member? adj (cdr a)))
             (assign-register graph v adj (set-remove moves first) assigned)
             (cdr a))))])))

(define find-least-saturated
  (lambda (graph vars)
    (let ([min +inf.0][res null])
      (begin
        (map
         (lambda (v)
           (let ([l (set-count (adjacent graph v))])
             (if (< l min)
                 (begin
                   (set! min l)
                   (set! res v)
                   "set!")
                 "not set!")))
         vars) res))))
      
(define (lowest-reg st n)
  (if (set-member? st n) (lowest-reg st (add1 n)) n))

(define (graph-moves graph e)
  (match e
    [`() graph]
    [`((movq (var ,x) (var ,y)) ,es ...)
     (add-edge graph x y)
     (graph-moves graph es)]
    [(or `((movq (offset (var ,x) ,n) (var ,y)) ,es ...)
         `((movq (var ,x) (offset (var ,y) ,n)) ,es ...))
     (add-edge graph x y)
     (graph-moves graph es)]
    [`((movq (offset (var ,x) ,n1) (offset (var ,y) ,n2)) ,es ...)
     (add-edge graph x y)
     (graph-moves graph es)]
    [`((if ,cnd ,thn ,thn-la ,els ,els-la) ,es ...)
     (graph-moves graph thn)
     (graph-moves graph els)]
    [`(,anything ,es ...)
     (graph-moves graph es)]))             
  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;changes variables to assigned registers/memory locations

(define assign-homes
  (lambda (vars)
    (lambda (e)
      (match e
        [`() `()]
        [`(offset (var ,x) ,n)
         `(offset ,(find-register (cdr (assoc x vars))) ,n)]
        [`(var ,x)
         (find-register (cdr (assv x vars)))]
        [`((,instruction ,a ,b) ,es ...)
         (cons
          `(,instruction ,((assign-homes vars) a) ,((assign-homes vars) b))
          ((assign-homes vars) es))]
        [`(program (,stack-args ,stack-vars ,callee-save ,assignments) ,type
                   (defines ,defines ...) ,es ...)
         `(program (,stack-args ,stack-vars ,(remove-duplicates callee-save)) ,type
                   (defines . ,(map (assign-homes assignments) defines)) .
          ,((assign-homes assignments) es))]
        [`(define (,f-name) ,args (,vars^ ,sa) ,es ...)
         `(define (,f-name) ,args (,vars^ ,sa) . ,((assign-homes vars) es))]
        [`((,instruction ,a) ,es ...)
         (cons
          `(,instruction ,((assign-homes vars) a))
          ((assign-homes vars) es))]
        [`((if (eq? ,e1 ,e2) ,thn ,thn-la ,els ,els-la) ,es ...)
         (cons
          `(if
            (eq? ,((assign-homes vars) e1) ,((assign-homes vars) e2))
            ,((assign-homes vars) thn)
            ,((assign-homes vars) els))
          ((assign-homes vars) es))]
        [`(,something_else ,es ...) `(,something_else . ,((assign-homes vars) es))]
        [anything_else anything_else]
        ))))

(define (find-register n)
  (if (>= n (vector-length registers-for-alloc))
      `(stack ,(* (- (add1 n) (vector-length registers-for-alloc)) (- 8)))
      `(reg ,(vector-ref registers-for-alloc n))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;lowers if statements into lists (flattening it)

(define lower-conditionals
  (lambda (e)
    (match e
      [`() `()]
      [`(program (,stack-args ,stack-vars ,callee-save)
                 ,type (defines ,defines ...) ,es ...)
       `(program (,stack-args ,stack-vars ,callee-save) ,type
                 (defines . ,(map lower-conditionals defines)) . ,(lower-conditionals es))]
      [`((if (eq? ,e1 ,e2) ,thn ,els) ,es ...)
       (let ([s1 (gensym "Then")][s2 (gensym "End")])
         (append
          `((cmpq ,e1 ,e2)
            (je ,s1))
          (lower-conditionals els)
          `((jmp ,s2)
            (label ,s1))
          (lower-conditionals thn)
          `((label ,s2))
          (lower-conditionals es)))]
      [`(,anything_else ,es ...)
       `(,anything_else . ,(lower-conditionals es))])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;patches anything that may cause issues in x86

(define patch-instructions
  (lambda (ls)
    (match ls
      [`() `()]
      [`(program ,info ,type (defines ,defines ...) ,es ...)
       `(program ,info ,type (defines . ,(map patch-instructions defines)) .
                 ,(patch-instructions es))]
      [`((movq ,var1 ,var2) ,es ...)
       (cond
         [(equal? var1 var2) (patch-instructions es)]
         [(and (inMemory? var1) (inMemory? var2))
          (patch-instructions `((movq ,var1 (reg rax)) (movq (reg rax) ,var2) . ,es))]
         [(stackOffset? var1)
          (match var1
            [`(offset (stack ,n) ,k)
             `((movq (stack ,n) (reg r11)) (movq (offset (reg r11) ,k) ,var2) .
               ,(patch-instructions es))])]
         [(stackOffset? var2)
          (match var2
            [`(offset (stack ,n) ,k)
             `((movq (stack ,n) (reg r11)) (movq ,var1 (offset (reg r11) ,k)) .
               ,(patch-instructions es))])]
         [else `(,(car ls) . ,(patch-instructions es))]
         )]
      [`((movzbq ,br ,var) ,es ...)
       (if (inMemory? var)
           `((movzbq ,br (reg rax)) (movq (reg rax) ,var) . ,(patch-instructions es))
           `(,(car ls) . ,(patch-instructions es)))]
      [`((addq (stack ,a) (stack ,b)) ,es ...)
       (append
        `((movq (stack ,a) (reg rax)) (addq (reg rax) (stack ,b)))
        (patch-instructions es))]
      [`((imul ,a ,b) ,es ...)
       (cond
         [(inMemory? b)
          (append
           `((movq ,b (reg rax)) (imul ,a (reg rax)) (movq (reg rax) ,b))
           (patch-instructions es))]
         [else (cons (car ls) (patch-instructions es))])]
      [`((cmpq ,e1 ,e2) ,es ...) #:when (immediate? e2)
       `((movq ,e2 (reg rax)) (cmpq ,e1 (reg rax)) . ,(patch-instructions es))]
      [`((cmpq ,e1 ,e2) ,es ...) #:when (and (inMemory? e1) (inMemory? e2))
       `((movq ,e1 (reg rax)) (cmpq (reg rax) ,e2) . ,(patch-instructions es))]
      [`((leaq ,e1 ,e2) ,es ...) #:when (inMemory? e2)
                                 `((leaq ,e1 (reg rax))
                                   (movq (reg rax) ,e2) .
                                   ,(patch-instructions es))]
      [`(,something_else ,es ...) `(,something_else . ,(patch-instructions es))])))

(define (immediate? x)
  (match x
    [`(int ,x) #t]
    [else #f]))

(define (stackOffset? e)
  (match e
    [`(offset (stack ,n) ,k) #t]
    [else #f]))

(define (inMemory? e)
  (match e
    [`(stack ,n) #t]
    [`(offset ,vec ,n) #t]
    [`(global-value ,var) #t]
    [`(stack-arg ,n) #t]
    [else #f]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;converts to a string of x86 assembly code

(define print-x86
  (lambda (e)
    (match e
      [`() ""]
      [`(stack-arg ,n) (format "~a(%rsp)" n)]
      [`(program (,stack-args ,stack-vars ,callee-saved) (type ,ty)
                 (defines ,defines ...) ,es ...)
       (define callee-saved-registers (remove-duplicates callee-saved))
       (define stack-increment
         (print-x86 (determine_stack (+ stack-vars (length callee-saved-registers) stack-args))))
       (string-append
        (print-defines defines)     
        (string-append "\t.globl " (check_os "main") "\n" (check_os "main") ":\n")
        "\tpushq\t%rbp\n"
        "\tmovq\t%rsp, %rbp\n"
        (push-callee-save callee-saved-registers stack-vars)  
        (if (equal? stack-increment (format "$~a" 0))
            ""
            (string-append "\tsubq\t" stack-increment ", %rsp\n\n"))
        (print-x86 es)
        "\n\tmovq\t%rax, %rdi\n"
        "\tmovq\t$0, %rsi\n"
        (print-statements ty 1)
        "\tmovq\t$0, %rax\n\n"
        (pop-callee-save callee-saved-registers stack-vars)
        "\tmovq\t%rbp, %rsp\n"
        "\tpopq\t%rbp\n"       
        "\n"
        "\tretq\n"
        )]
      [`((label ,labelname) ,es ...)
       (string-append (symbol->string labelname) ":\n"
                      (print-x86 es))]
      [`((callq ,label) ,es ...)
       (string-append
        (format "\tcallq\t~a\n" (check_os (format "~a" label)))
        (print-x86 es))]
      [`((indirect-callq ,arg) ,es ...) (string-append "\tcallq\t*" (print-x86 arg) "\n" (print-x86 es))]
      [`(stack ,n) (format "~a(%rbp)" n)]
      [(or `(reg ,reg) `(byte-reg ,reg)) (format "%~a" reg)]
      [`(int ,n) (format "$~a" n)]
      [(? symbol?) (symbol->string e)]
      [`(global-value ,var) (check_os (format "~a(%rip)" var))]
      [`(function-ref ,label) (format "~a(%rip)" label)]
      [`(offset ,var ,n) (string-append (format "~a(" n) (print-x86 var) ")")]
      [`((,instruction ,a ,b) ,es ...)
       (string-append
        "\t" (symbol->string instruction) "\t"(print-x86 a) ", " (print-x86 b) "\n" (print-x86 es))]
      [`((,instruction ,a) ,es ...)
       (string-append
        "\t" (symbol->string instruction) "\t" (print-x86 a) "\n" (print-x86 es))]
      [`((,instruction) ,es ...)
       (string-append
        "\t" (symbol->string instruction) "\n" (print-x86 es))])))

(define callee-save-regs `(rbx r12 r13 r14 r15))

(define print-defines
  (lambda (defines)
    (match defines
      [`((define (,label) ,arg-count (,vars ,stack-args) ,es ...) ,others ...)
       (define stack-increment
         (cadr (determine_stack (+ (length vars)
                                   (length callee-save-regs)
                                   stack-args))))
       (string-append
        (format "\t.globl ~a\n" label)
        (format "~a:\n" label)
        "\tpushq\t%rbp\n"
        "\tmovq\t%rsp, %rbp\n"
        (push-callee-save callee-save-regs (length vars))
        (format "\tsubq\t$~a, %rsp\n" stack-increment)
        "\n"
        (print-x86 es)
        "\n"       
        (pop-callee-save callee-save-regs (length vars))
        "\tmovq\t%rbp, %rsp\n"
        "\tpopq\t%rbp\n"
        "\tretq\n\n"
        (print-defines (cdr defines)))]
      [`() ""])))

(define (push-callee-save registers vars)
  (cond
    [(null? registers) ""]
    [else
     (string-append
      "\tmovq\t"
      "%" (symbol->string (car registers))
      ", "
      (format "-~a(%rbp)" (* 8 (add1 vars)))
      "\n"
      (push-callee-save (cdr registers) (add1 vars)))]))

(define (pop-callee-save registers vars)
  (cond
    [(null? registers) ""]
    [else
     (string-append
      "\tmovq\t"
      (format "-~a(%rbp)" (* 8 (add1 vars)))
      ", "
      "%" (symbol->string (car registers))
      "\n"
      (pop-callee-save (cdr registers) (add1 vars)))]))

(define print-assembly
  (lambda (e)
    (display (print-x86 e))))

(define check_os
  (lambda (s)
    (let ([os (system-type 'os)])
      (match os
        ['macosx (string-append "_" s)]
        [else s]))))

(define determine_stack
  (lambda (n)
    (let ([m (* 8 n)])
      (if (equal? (remainder m 16) 0) `(int ,m) `(int ,(+ m 8))))))

(define (print-statements type n)
  (match type
    ['Any (string-append "\tcallq\t" (check_os "print_any\n"))]
    ['Integer (string-append "\tcallq\t" (check_os "print_int\n"))]
    ['Boolean (string-append "\tcallq\t" (check_os "print_bool\n"))]
    [`Void    (string-append "\tcallq\t" (check_os "print_void\n"))]
    [`(Vector ,vec-t ...)
     (string-append
      "\tmovq\t%rdi, %rax\n"
      "\tcallq\t" (check_os "print_vecbegin\n")
      (print-statements vec-t n))]
    [`(,type1 ,type2 ...)
     (string-append
      (format "\tmovq\t~a(%rax), %rdi\n" (* 8 n))
      (print-statements type1 n)
      (print-statements type2 (add1 n)))]
    [`() (string-append "\tcallq\t" (check_os "print_vecend\n\n"))]))
        
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Pass list

(define r3-passes
  (list
   `("expand-macros" ,expand-macros ,interp-scheme)
   `("typecheck" ,(typecheck '()) ,interp-scheme)
   `("uniquify" ,(uniquify '()) ,interp-scheme)
   `("reveal functions" ,(reveal-functions '() '()) ,interp-C)
   `("convert-body-to-static" ,convert-body-to-static ,interp-C)
   `("convert-to-closures" ,(convert-to-closures '()) ,interp-C)
   `("remove-excess" ,remove-excess ,interp-C)
   `("lower-cons-cells" ,lower-cons-cells ,interp-C)
   `("flatten" ,(flatten false) ,interp-C)
   `("expose allocations" ,(expose-allocation '()) ,interp-C)
   `("uncover-call-live-roots" ,(uncover-call-live-roots '() '()) ,interp-C)
   `("SI" ,(select-instructions '() '()) ,interp-x86)
   `("Live-after" ,(uncover-live '()) ,interp-x86)
   `("Build Interference Graph" ,(build-interference '() '()) ,interp-x86)
   `("Allocate Registers" ,allocate-registers ,interp-x86)
   `("Assign Homes" ,(assign-homes '()) ,interp-x86)
   `("Lower Conditionals" ,lower-conditionals ,interp-x86)
   `("Patch Instructions" ,patch-instructions ,interp-x86)
   `("Print-x86" ,print-x86 ,interp-x86) 
   ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Testing

(define (test-compiler)
  ;; (compiler-tests "R1" (typecheck '()) r3-passes "r1" (range 1 20))
  ;; (newline)
  ;; (compiler-tests "R1a" (typecheck '()) r3-passes "r1a" (range 1 9))
  ;; (newline)
  ;; (compiler-tests "R2" (typecheck '()) r3-passes "r2" (range 1 24))
  ;; (newline)
  ;; (compiler-tests "R3" (typecheck '()) r3-passes "r3" (range 1 16))
  ;; (newline)
  ;; (compiler-tests "R4" (typecheck '()) r3-passes "r4" (range 1 20))
  ;; (newline)
  ;; (compiler-tests "R5" (typecheck '()) r3-passes "r5" (range 1 13))
  ;; (newline)
  (compiler-tests "R7" #f r3-passes "r7" (range 1 12))
  (newline)
  (compiler-tests "R8" #f r3-passes "r8" (range 1 16))
  (newline)
  (print "All Tests Passed!"))

(test-compiler)

(define (test-times n)
  (match n
    [0 0]
    [else (test-compiler) (test-times (sub1 n))]))
