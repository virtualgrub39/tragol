# program main at $0800 is
# result: byte;
# proc test (A: byte, B: byte) returns (C: byte) at $1000 is
# begin
# set C = A + B;
# end proc;
# begin
# call test (34, 35) into result;
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

(def call-graph @{})

(defn new-scope [parent] @{:names @{} :parent parent})

(defn lookup [name scope]
  (or (get (scope :names) name)
      (when (scope :parent) (lookup name (scope :parent)))))

(defn resolve [ident scope]
  (def name (ident :value))
  (def decl (lookup name scope))
  (unless decl (errorf "Unknown name `%s`" name))
  (put ident :decl decl)
  decl)

(defn declare [decl scope]
  (def name (decl :name))
  (when (lookup name scope)
    (errorf "Redefinition of `%s`" name))
  (put (scope :names) name decl))

(defn declare-all [decls scope storage]
  (each d decls
    (put d :storage storage)
    (declare d scope)))

(defn annotate-expr [expr scope]
  (case (expr :kind)
    :ident (let [name (expr :value)
                 d    (lookup name scope)]
             (unless d (errorf "Unknown name `%s`" name))
             (unless (= (d :kind) :var) (errorf "`%s` is not a variable" name))
             (put expr :decl d)
             (put expr :type (d :type)))
    :binop (let [l (annotate-expr (expr :lhs) scope)
                 r (annotate-expr (expr :rhs) scope)]
             (unless (= l r) (errorf "Type mismatch: %q vs %q" l r))
             (put expr :type l))
    :num   (let [v (expr :value)]
             (if (< v 256)
               (put expr :type :byte)
               (put expr :type :address)))
    (errorf "Unknown expression type `%V`" (expr :kind)))
  (expr :type))

(defn annotate-stmt [stmt caller scope]
  (case (stmt :kind)
    :set (let [rt (annotate-expr (stmt :rvalue) scope)
               lt (annotate-expr (stmt :lvalue) scope)]
           (unless (= lt rt) (errorf "Cannot assign %V to %V" rt lt)))
    :call (let [target (stmt :target)
                callee (resolve target scope)]
            (unless (= (callee :kind) :proc) (errorf "`%s` is not a procedure" (target :value)))
            (unless (= (length (stmt :args)) (length (callee :args))) (errorf "arity error in call to `%s`" (target :value)))
            (unless (= (length (stmt :into)) (length (callee :returns))) (errorf "arity error in call to `%s`" (target :value)))
            (each arg (stmt :args) (annotate-expr arg scope))
            (each arg (stmt :into) (annotate-expr arg scope))
            (put (call-graph caller) (callee :name) true))
    :return ()
    (errorf "Unknown statement `%V`" (stmt :kind))))

(defn annotate-proc [proc parent]
  (assert (= (proc :kind) :proc))

  (def scope (new-scope parent))
  (def name (proc :name))
  (put call-graph name @{})

  (declare-all (proc :args)    scope :param)
  (declare-all (proc :locals)  scope :local)
  (declare-all (proc :returns) scope :result)
  (each stmt (proc :body) (annotate-stmt stmt name scope)))

(defn annotate-program [prog] # adds type information to expressions, does some basic type checking
  (assert (= (prog :kind) :program))

  (def scope (new-scope nil))
  (put call-graph "<main>" @{})

  (declare-all (prog :globals) scope :global)
  (each proc (prog :procs) (declare proc scope))
  (each proc (prog :procs) (annotate-proc proc scope))
  (each stmt (prog :body) (annotate-stmt stmt "<main>" scope)))

(defn check-cycles [graph]
  (def state @{})              # nil = unvisited, :active = on current path, :done
  (def path @[])
  (def order @[])              # callees before callers
  (defn visit [n]
    (case (state n)
      :done nil
      :active (errorf "Recursion: %s"
                      (string/join [;(slice path (index-of n path)) n] " -> "))
      (do (put state n :active)
          (array/push path n)
          (each c (keys (graph n)) (visit c))
          (array/pop path)
          (put state n :done)
          (array/push order n))))
  (each n (keys graph) (visit n))
  order)

(defn type-size [t]
  (case t
    :byte 1
    :address 2
    (errorf "No size for type %q" t)))

(defn alloc! [decl labl]
  (put decl :label labl)
  (put decl :size (type-size (decl :type)))
  (cond
    (decl :at) nil                                   # equate emitted from :at
    (= (decl :type) :address) (put decl :zp true)    # assembler places it in the ZP block
    nil))                                            # plain RAM: nothing to decide

(defn allocate-program [prog]
  (put prog :label (prog :name))
  (each d (prog :globals) (alloc! d (d :name)))
  (each p (prog :procs)
    (put p :label (p :name))
    (each d (p :args)    (alloc! d (string (p :name) "_" (d :name))))
    (each d (p :returns) (alloc! d (string (p :name) "_" (d :name))))
    (each d (p :locals)  (alloc! d (string (p :name) "_" (d :name))))))

(defn gen [out & items] (array/push out items))

(defn trivial? [expr]
  (or (= (expr :kind) :num) (= (expr :kind) :ident)))

(defn decl-operand [decl]
  [:abs (decl :label)])

(defn operand [expr]
  (case (expr :kind)
    :num [:imm (expr :value)]
    :ident (decl-operand (expr :decl))
    (errorf "`%q` is not a trivial expression" (expr :kind))))

(defn gen-store [dst oprnd]
  (gen dst :sta ;oprnd))

(defn gen-add [dst operands] (gen dst :clc :imp) (gen dst :adc ;operands))
(defn gen-sub [dst operands] (gen dst :sec :imp) (gen dst :sbc ;operands))

(def binops
  {:add {:gen gen-add :commutative true}
   :sub {:gen gen-sub :commutative false}})

(defn codegen-expr [dst expr]
  (cond
    (trivial? expr)
    (gen dst :lda ;(operand expr))
    
    (= (expr :kind) :binop)
    (let [op  (binops (expr :op))
          lhs (expr :lhs)
          rhs (expr :rhs)]
      (cond
        (trivial? rhs)
        (do (codegen-expr dst lhs)
            ((op :gen) dst (operand rhs)))

        (and (op :commutative) (trivial? lhs))
        (do (codegen-expr dst rhs) # swap sides
            ((op :gen) dst (operand lhs)))
        
        (errorf "Expression too complex; split it into two statements pls")))
   (errorf "Cannot generate expression `%q`" (expr :kind))))

(defn codegen-var [d equates vars]
  (cond
    (d :at) (gen equates :equ (d :label) (d :at))
    (d :zp) (gen equates :zp (d :label) (d :size))
    (gen vars :res (d :label) (d :size))))

(defn codegen-label [dst node]
  (gen dst :label (node :label)))

(defn codegen-stmt [dst stmt]
  (case (stmt :kind)
    :set (do (codegen-expr dst (stmt :rvalue))
             (gen-store dst (operand (stmt :lvalue))))
    :call
    (let [callee (get-in stmt [:target :decl])]
      (for i 0 (length (stmt :args))
        (codegen-expr dst ((stmt :args) i))
        (gen-store dst (decl-operand ((callee :args) i))))
      (gen dst :jsr :abs (callee :label))
      (for i 0 (length (stmt :into))
        (gen dst :lda ;(decl-operand ((callee :returns) i)))
        (gen-store dst (operand ((stmt :into) i)))))

    :return (gen dst :rts :imp)
    (errorf "Cannot generate statement `%V`" (stmt :kind))))

(defn codegen-proc [dst proc]
  (when-let [at (proc :at)] (gen dst :org at))
  (codegen-label dst proc)
  (each s (proc :body) (codegen-stmt dst s)))

(defn codegen-program [prog]
  (def equates @[]) # constants: label = value
  (def main @[])
  (def procs @[])
  (def vars @[]) # variables: label .byte/.word value/?
  (def fixed_procs @[]) # `proc` with `at`

  (each d (prog :globals) (codegen-var d equates vars))
  (each p (prog :procs)
    (each d (p :args) (codegen-var d equates vars))
    (each d (p :returns) (codegen-var d equates vars))
    (each d (p :locals) (codegen-var d equates vars))
    (codegen-proc (if (p :at) fixed_procs procs) p))

  (when-let [at (prog :at)] (gen main :org at)) # * = at
  (gen main :label (prog :label))
  (each s (prog :body) (codegen-stmt main s))
  (array/concat @[] equates main procs vars fixed_procs))

(def modes
  {:imp  (fn [mnemonic _]     (string "    " mnemonic))
   :imm  (fn [mnemonic value] (string "    " mnemonic " #" ;value))
   :abs  (fn [mnemonic value] (string "    " mnemonic " " ;value))
   :absx (fn [mnemonic value] (string "    " mnemonic " " ;value ",x"))
   :absy (fn [mnemonic value] (string "    " mnemonic " " ;value ",y"))
   :indy (fn [mnemonic value] (string "    " mnemonic " (" ;value "),y"))})

(defn emit-item [code]
  (match code
    [:org addr]       (printf "* = $%04x" addr)
    [:label labl]     (print labl)
    [:equ labl value] (printf "%s = $%x" labl value)
    [:res labl size]  (printf "%s .fill %d" labl size) 
    [mnemonic mode & value] (print ((modes mode) mnemonic value))
    (errorf "Malformed code `%q`" code)))

(pp ast)
(annotate-program ast) # side-effect: call-graph
(check-cycles call-graph)
(allocate-program ast)
(def code (codegen-program ast))
(pp code)
(each item code (emit-item item))
