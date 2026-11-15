# program main at $0800 is
# result: byte;
# proc test (A: byte, B: byte) returns (C: byte) is
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
                                          :rhs @{:kind :ident :value "B"}}}]}]
           :body @[@{:kind :call
                     :target "test"
                     :args   @[@{:kind :num :value 34}
                               @{:kind :num :value 35}]
                     :into   @[@{:kind :ident :value "result"}]}]})

(def call-graph @{})

(defn new-scope [parent] @{:names @{} :parent parent})

(defn lookup [name scope]
  (or (get (scope :names) name)
      (when (scope :parent) (lookup name (scope :parent)))))

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
                callee (lookup (stmt :target) scope)]
            (unless callee (errorf "Unknown name `%s`" target))
            (unless (= (callee :kind) :proc) (errorf "`%s` is not a procedure" target))
            (unless (= (length (stmt :args)) (length (callee :args))) (errorf "arity error in call to `%s`" target))
            (unless (= (length (stmt :into)) (length (callee :returns))) (errorf "arity error in call to `%s`" target))
            (each arg (stmt :args) (annotate-expr arg scope))
            (each arg (stmt :into) (annotate-expr arg scope))
            (put (call-graph caller) (callee :name) true)
            (put stmt :callee callee))
    (errorf "Unknown statement kind %V" (stmt :kind))))

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
  # (each d (prog :globals) (alloc! d (string (prog :name) "_" (d :name))))
  (each p (prog :procs)
    # (each d (p :args)    (alloc! d (string (prog :name) "_" (p :name) "_" (d :name))))
    # (each d (p :returns) (alloc! d (string (prog :name) "_" (p :name) "_" (d :name))))
    # (each d (p :locals)  (alloc! d (string (prog :name) "_" (p :name) "_" (d :name))))
    (each d (p :args)    (alloc! d (string (p :name) "_" (d :name))))
    (each d (p :returns) (alloc! d (string (prog :name) "_" (p :name) "_" (d :name))))
    (each d (p :locals)  (alloc! d (string (p :name) "_" (d :name))))))

(defn gen [out & items] (array/push out items))

(defn codegen-var [d equates vars]
  (cond
    (d :at) (gen equates :equ (d :label) (d :at))
    (d :zp) (gen equates :zp (d :label) (d :size))
    (gen vars :res (d :label) (d :size))))

(defn codegen-label [dst node]
  (gen :label (node :label)))

(defn trivial? [e]
  (or (= (e :kind) :num)
      (= (e :kind) :ident)))

(defn operand [e]
  (case (e :kind)
    :num [:imm (e :value)]
    :ident [:abs ((e :decl) :label)]
    (errorf "Not a trivial operand: `%V`" (e :kind))))

(defn emit-leaf [out e]
  (emit out :lda ;(operand e)))

(def emitters {:num emit-leaf :ident emit-leaf :binop emit-binop})

(defn emit-expr [out e]
  (if-let [f (emitters (e :kind))]
    (f out e)
    (errorf "Cannot generate expression %q" (e :kind))))

(defn store [out lv]
  (emit out :sta ;(operand lv))) # ';' unpacks a tuple

(defn codegen-stmt [dst stmt]
  (case (stmt :kind)
    :set (do (codegen-expr dst (stmt :rvalue))
             (store dst (s :lvalue)))
    (errorf "Can't generate statement `%V`" (stmt :kind))))

(defn codegen-proc [dst proc]
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
  (gen main :label "start")
  (each s (prog :body) (codegen-stmt main s))
  (gen main :rts))

(annotate-program ast) # side-effect: call-graph
(check-cycles call-graph)
(allocate-program ast)
(pp ast)
(codegen-program ast)
# (pp ast)
