(def ast @{:kind :program
           :name "main"
           :at 0x800
           :globals @[@{:kind :var :name "result" :type :byte :at 0xf0}]
           :procs @[@{:kind :proc
                      :at 0x1000
                      :name "test"
                      :args @[@{:kind :var :name "A" :type :byte}
                              @{:kind :var :name "B" :type :byte}]
                      :locals @[]
                      :returns @[@{:kind :var :name "C" :type :byte}]
                      :body @[@{:kind :set
                                :lvalue @{:kind :ident :value "C"}
                                :rvalue @{:kind :binop
                                          :op :add
                                          :lhs @{:kind :ident :value "A"}
                                          :rhs @{:kind :ident :value "B"}}}
                              @{:kind :return}]}]
           :body @[@{:kind :call
                     :target @{:kind :ident :value "test"}
                     :args   @[@{:kind :num :value 34}
                               @{:kind :num :value 35}]
                     :into   @[@{:kind :ident :value "result"}]}
                   @{:kind :return}]})

(defn fits-in-type? [value dst-type]
  (case dst-type
    :byte (<= value 255)
    :address (<= value 65535)
    (errorf "Invalid type `%V`" dst-type)))

(defn assignable? [expr]
  (case (expr :kind)
    :ident true
    false))

(defn new-scope [parent] @{:names @{} :parent parent})

(defn lookup [scope name]
  (or (get (scope :names) name)
      (when (scope :parent) (lookup (scope :parent) name))))

(defn resolve [scope ident]
  (def name (ident :value))
  (def decl (lookup scope name))
  (unless decl (errorf "Undeclared symbol `%s`" name))
  (put ident :decl decl)
  decl)

(defn declare [scope decl]
  (def name (decl :name))
  (when (lookup scope name)
    (errorf "Redeclaration of symbol `%s`" name))
  (put (scope :names) name decl))

(defn declare-all [scope decls]
  (each decl decls (declare scope decl)))

(defn infer-expr [scope expr]
  (case (expr :kind)
    :ident
    (let [name (expr :value)
          decl (lookup scope name)]
      (unless decl
        (errorf "Name `%s` was not declared" name))
      (unless (= (decl :kind) :var)
        (errorf "Tried to use `%s` as a variable" name))
      (put expr :decl decl)
      (put expr :type (decl :type))
      (decl :type))
    
    :num
    (errorf "Cannot infer type of number literal `%q`" (expr :value))
    
    :binop
    (let [lhs-type (infer-expr scope (expr :lhs))
          rhs-type (infer-expr scope (expr :rhs))]
      (unless (= lhs-type rhs-type)
        (errorf "Type missmatch in `%q`: %V vs %V" expr lhs-type rhs-type))
      (put expr :type lhs-type)
      lhs-type)))

(var expect-binop nil)

(defn expect-expr [scope expr expected-type]
  (case (expr :kind)
    :ident
    (let [actual-type (infer-expr scope expr)]
      (unless (= expected-type actual-type)
        (errorf "Type missmatch for `%s`: expected %V, got %V" (expr :value) expected-type actual-type))
      actual-type)
    
    :num
    (do
      (unless (fits-in-type? (expr :value) expected-type)
        (errorf "Value %d doesn't fit in type %V" (expr :value) expected-type))
      (put expr :type expected-type)
      expected-type)
    
    :binop
    (expect-binop scope expr expected-type)))

(set expect-binop 
     (fn [scope expr expected-type]
       (case (expr :op)
         :add
         (do
           (expect-expr scope (expr :lhs) expected-type)
           (expect-expr scope (expr :rhs) expected-type)
           (put expr :type expected-type)
           expected-type))))

(defn verify-arity [what name expected got]
  (unless (= (length expected) (length got))
    (errorf "%s arity error in call to `%s`" what name)))

(defn expect-lvalue [scope expr expected-type]
  (unless (assignable? expr)
    (errorf "Expression `%q` is not a valid lvalue" expr))
  
  (let [actual-type (infer-expr scope expr)]
    (unless (= actual-type expected-type)
      (errorf "Expected lvalue of type %V, got %V"
              expected-type actual-type))))

(defn annotate-stmt [scope stmt]
  (case (stmt :kind)
    :set (let [lvalue (stmt :lvalue)
               ltype (infer-expr scope (stmt :lvalue))]
           (unless (assignable? lvalue)
             (errorf "Expression `%q` is not a valid lvalue" lvalue))
           (expect-expr scope (stmt :rvalue) ltype))
    :call (let [target (stmt :target)
                callee (resolve scope target)]
            (unless (= (callee :kind) :proc)
              (errorf "`%q` is not a procedure" target))

            (verify-arity "argument" (target :name) (callee :args) (stmt :args))
            (verify-arity "return" (target :name) (callee :returns) (stmt :into))

            (for i 0 (length (stmt :args))
              (let [arg ((stmt :args) i)
                    expected-type (((callee :args) i) :type)]
                (expect-expr scope arg expected-type)))

            (for i 0 (length (stmt :into))
              (let [dst ((stmt :into) i)
                    expected-type (((callee :returns) i) :type)]
                (expect-lvalue scope dst expected-type))))
    :return ()
    (errorf "Unknown statement `%V`" (stmt :kind))))

(defn annotate-proc [parent proc]
  (assert (= (proc :kind) :proc))

  (def scope (new-scope parent))
  
  (declare-all scope (proc :args))
  (declare-all scope (proc :locals))
  (declare-all scope (proc :returns))
  (each stmt (proc :body) (annotate-stmt scope stmt)))

(defn annotate-program [prog]
  (assert (= (prog :kind) :program))
  
  (def scope (new-scope nil))
  
  (declare-all scope (prog :globals))
  (each proc (prog :procs) (declare scope proc))
  (each proc (prog :procs) (annotate-proc scope proc))
  (each stmt (prog :body)  (annotate-stmt scope stmt)))

(annotate-program ast)
