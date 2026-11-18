# program main at $0800 is
# result: byte at $f0;
# proc test (A: byte; B: byte) returns (C: byte) at $1000 is
# begin
# set C = A + B;
# return;
# end proc;
# begin
# call test (34, 35) into (result);
# return;
# end program;
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

(def type-info
  {:byte    {:fits? (fn [v] (<= v 255))
             :size 1}
   :address {:fits? (fn [v] (<= v 65535))
             :size 2}})

# ------------- TYPE CHECKING & ANNOTATION ------------- #

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

(defn infer-expr-type [scope expr]
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
    (let [lhs-type (infer-expr-type scope (expr :lhs))
          rhs-type (infer-expr-type scope (expr :rhs))]
      (unless (= lhs-type rhs-type)
        (errorf "Type missmatch in `%q`: %V vs %V" expr lhs-type rhs-type))
      (put expr :type lhs-type)
      lhs-type)
    
    (errorf "Cannot infer type of expression `%q`" expr)))

(var expect-binop-type nil)

(defn expect-expr-type [scope expr expected-type]
  (case (expr :kind)
    :ident
    (let [actual-type (infer-expr-type scope expr)]
      (unless (= expected-type actual-type)
        (errorf "Type missmatch for `%s`: expected %V, got %V" (expr :value) expected-type actual-type))
      actual-type)
    
    :num
    (do
      (unless (((type-info expected-type) :fits?) (expr :value))
        (errorf "Value %d doesn't fit in type %V" (expr :value) expected-type))
      (put expr :type expected-type)
      expected-type)
    
    :binop
    (expect-binop-type scope expr expected-type)))

(set expect-binop-type 
     (fn [scope expr expected-type]
       (case (expr :op)
         :add
         (do
           (expect-expr-type scope (expr :lhs) expected-type)
           (expect-expr-type scope (expr :rhs) expected-type)
           (put expr :type expected-type)
           expected-type))))

(defn verify-arity [what name expected got]
  (unless (= (length expected) (length got))
    (errorf "%s arity error in call to `%s`" what name)))

(defn expect-lvalue-type [scope expr expected-type]
  (unless (assignable? expr)
    (errorf "Expression `%q` is not a valid lvalue" expr))
  
  (let [actual-type (infer-expr-type scope expr)]
    (unless (= actual-type expected-type)
      (errorf "Expected lvalue of type %V, got %V"
              expected-type actual-type))))

(defn annotate-stmt [scope stmt]
  (case (stmt :kind)
    :set (let [lvalue (stmt :lvalue)
               ltype (infer-expr-type scope (stmt :lvalue))]
           (unless (assignable? lvalue)
             (errorf "Expression `%q` is not a valid lvalue" lvalue))
           (expect-expr-type scope (stmt :rvalue) ltype))
    :call (let [target (stmt :target)
                callee (resolve scope target)]
            (unless (= (callee :kind) :proc)
              (errorf "`%q` is not a procedure" target))

            (verify-arity "argument" (target :name) (callee :args) (stmt :args))
            (verify-arity "return" (target :name) (callee :returns) (stmt :into))

            (for i 0 (length (stmt :args))
              (let [arg ((stmt :args) i)
                    expected-type (((callee :args) i) :type)]
                (expect-expr-type scope arg expected-type)))

            (for i 0 (length (stmt :into))
              (let [dst ((stmt :into) i)
                    expected-type (((callee :returns) i) :type)]
                (expect-lvalue-type scope dst expected-type))))
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
  (each stmt (prog :body)  (annotate-stmt scope stmt))
  prog)

# ------------- LABELING AND ADDRESSING (if neccessary) ------------- #

(defn allocate-decl [decl labl]
  (put decl :label labl)
  (put decl :size ((type-info (decl :type)) :size))
  (cond
    (decl :at) nil
    (= (decl :type) :address) (put decl :zp true)
    nil))

(defn allocate-proc [proc]
  (assert (= (proc :kind) :proc))
  (put proc :label (proc :name)) 
  (each decl (proc :args)    (allocate-decl decl (string (proc :name) "_" (decl :name))))
  (each decl (proc :returns) (allocate-decl decl (string (proc :name) "_" (decl :name))))
  (each decl (proc :locals)  (allocate-decl decl (string (proc :name) "_" (decl :name)))))

(defn allocate-program [prog]
  (assert (= (prog :kind) :program))
  (each decl (prog :globals) (allocate-decl decl (decl :name)))
  (each proc (prog :procs)
    (allocate-proc proc))
  prog)

# ------------- CODEGEN ------------- #

# [:org at] -> * = at
# [:label lbl] -> lbl
# [:equ label at] -> label = at
# [:zp label size] -> label = <allocated address>
# [:res label size] -> label .fill size
# [instr :imp] -> instr
# [instr :imm val] -> instr #val
# [instr :abs val] -> instr val

(defn trivial? [expr]
  (case (expr :kind)
    :num true
    :ident true
    false))

(defn codegen [out instr] (array/concat out instr))

(defn codegen-decl [equates vars decl]
  (cond
    (decl :at) (codegen equates [:equ (decl :label) (decl :at)])
    (decl :zp) (codegen equates [:zp (decl :label) (decl :size)])
    (codegen vars [:res (decl :label) (decl :size)])))

(defn decl-operand [decl]
  [:abs (decl :label)])

(defn operand [expr]
  (case (expr :kind)
    :num [:imm (expr :value)]
    :ident (decl-operand (expr :decl))
    (errorf "`%q` is not a trivial expression" (expr :kind))))

(defn codegen-label [out node]
  (codegen out [:label (node :label)]))

(defn codegen-store [dst oprnd]
  (codegen dst [:sta ;oprnd]))

(defn codegen-add [out operands] 
  (codegen out [:clc :imp])
  (codegen out [:adc ;operands]))

(defn codegen-sub [out operands]
  (codegen out [:sec :imp])
  (codegen out [:sbc ;operands]))

(def binops
  {:add {:gen codegen-add :commutative true}
   :sub {:gen codegen-sub :commutative false}})

(var codegen-expr nil)

(defn codegen-expr-binop [out expr]
  (def op (binops (expr :op)))
  (def lhs (expr :lhs))
  (def rhs (expr :rhs))
  
  (cond
    (trivial? rhs)
    (do (codegen-expr out lhs) # ex. (b * c) + a
        ((op :gen) out (operand rhs)))
    
    (and (op :commutative) (trivial? lhs)) # ex. a + (b * c)
    (do (codegen-expr out rhs) # swap sides
        ((op :gen) out (operand lhs)))
    
    (errorf "Expression too complex; split it into two statements pls")))

(set codegen-expr (fn [out expr]
  (cond
    (trivial? expr)
    (codegen out [:lda ;(operand expr)])

    (= (expr :kind) :binop)
    (codegen-expr-binop out expr)
    
    (errorf "Cannot generate expression `%q`" (expr :kind)))))

(defn codegen-stmt-return [out stmt] (codegen out [:rts :imp]))

(defn codegen-stmt-call [out stmt]
  (def callee (get-in stmt [:target :decl]))
  (for i 0 (length (stmt :args))
    (codegen-expr out ((stmt :args) i))
    (codegen-store out (decl-operand ((callee :args) i))))
  (for i 0 (length (stmt :into))
    (codegen out [:lda ;(decl-operand ((callee :returns) i))])
    (codegen-store out (operand ((stmt :into) i)))))

(defn codegen-stmt-set [out stmt]
  (codegen-expr out (stmt :rvalue))
  (codegen-store out (operand (stmt :lvalue))))

(defn codegen-stmt [out stmt]
  (case (stmt :kind)
    :set    (codegen-stmt-set out stmt)
    :call   (codegen-stmt-call out stmt)
    :return (codegen-stmt-return out stmt)
    (errorf "Cannot generate statement `%V`" (stmt :kind))))

(defn codegen-proc [out proc]
  (when-let [at (proc :at)] (codegen out [:org at]))
  (codegen-label out proc)
  (each stmt (proc :body) (codegen-stmt out stmt)))

(defn codegen-program [prog]
  (def equates     @[]) # constants: label = value 
  (def main-body   @[])
  (def procs       @[])
  (def vars        @[]) # variables: label .fill size  
  (def fixed-procs @[]) # `proc` with `at` 
  
  (each decl (prog :globals)   (codegen-decl equates vars decl))
  (each proc (prog :procs)
    (each decl (proc :args)    (codegen-decl equates vars decl))
    (each decl (proc :returns) (codegen-decl equates vars decl))
    (each decl (proc :locals)  (codegen-decl equates vars decl))
    (codegen-proc (if (proc :at) fixed-procs procs) proc))
  
  (when-let [at (prog :at)] (codegen main-body [:org at]))
  (codegen main-body [:label (prog :label)])
  (each stmt (prog :body) (codegen-stmt main-body stmt))
  (array/concat @[]
                equates
                main-body
                procs
                vars
                fixed-procs))

(pp (codegen-program (allocate-program (annotate-program ast))))
