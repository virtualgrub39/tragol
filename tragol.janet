# ------------- LEXING ------------- #

(def- trivial-toks
  {":"   :colon      ";"   :semicolon   "," :comma
   "="   :equals     "("   :left-paren  ")" :right-paren
   "\\/" :logical-or "/\\" :logical-and "[" :left-bracket
   "]"   :right-bracket "+" :plus "-" :minus "?=" :compare
   "(+)" :logical-xor "&" :addrof})

(def- keywords
  {"proc"    :kw-proc    "is"     :kw-is
   "begin"   :kw-begin   "end"    :kw-end
   "set"     :kw-set     "returns" :kw-returns
   "byte"    :kw-byte    "address" :kw-address
   "program" :kw-program "at"     :kw-at
   "into"    :kw-into    "call"   :kw-call
   "return"  :kw-return   "of"    :kw-of})

(def- punct-strings (sort-by |(- (length $)) (keys trivial-toks)))

(def- lexer
  (peg/compile
   ~{:ws (+ (set " \t\r\n") (* "--" (any (if-not "\n" 1))))
     :punct  (/ (capture (choice ,;punct-strings))
                ,(fn [s] [(trivial-toks s)]))
     :word   (/ (capture (* (+ :a "_") (any (+ :w "_"))))
                ,(fn [w] (if-let [kw (keywords w)] [kw] [:ident w])))
     :number (/ (capture (* (some :d) (not :w)))
                ,(fn [n] [:num (scan-number n)]))
     :hex (/ (capture (* "$" (some :h) (not :w)))
             ,(fn [s] [:num (scan-number (string "0x" (string/slice s 1)))]))
     :token (/ (* ($) (+ :punct :word :hex :number)) ,(fn [p [k v]] [k v p]))
     :main   (* (any (* (any :ws) :token)) (any :ws) ($))}))

(defn lex [src]
  (def toks (peg/match lexer src))
  (def pos (array/pop toks))
  (if (< pos (length src))
    (errorf "Syntax error near %q" (string/slice src pos (min (length src) (+ pos 10))))
    (array/push toks [:eof])))

# ------------- PARSING ------------- #

(var- pos 0)
(var- toks nil)

(defn- peek [] (get toks pos))
(defn- kind [] (get (peek) 0))
(defn- at? [tag] (= (kind) tag))
(defn- next! [] (def t (toks pos)) (unless (at? :eof) (++ pos)) t)
(defn- accept [k] (when (at? k) (next!)))
(defn- expect [k]
  (if (at? k)
    (next!)
    (errorf "expected %v, got %v at offset %d" k (kind) ((toks pos) 2))))
(defn- expect-name [] ((expect :ident) 1))
(defn- expect-num [] ((expect :num) 1))

(defn- fail [what]
  (errorf "expected %s, got %v at offset %v" what (kind) ((toks pos) 2)))

(defn- expect-type []
  (case (kind)
    :kw-byte    (do (next!) :byte)
    :kw-address (do (next!) :address)
    (fail "type")))

# '(' item (sep item)* ')'
(defn- parse-list [item sep]
  (expect :left-paren)
  (def items @[])
  (unless (at? :right-paren)
    (array/push items (item))
    (while (accept sep)
      (array/push items (item))))
  (expect :right-paren)
  items)

(defn- parse-typed-name []
  (def name (expect-name))
  (expect :colon)
  # (def typ (expect-type))
  (cond
    (at? :num)
    (let [len (expect-num)
          _ (expect :kw-of)
          typ (expect-type)]
      @{:kind :array :name name :length len :type typ})
    (let [typ (expect-type)]
          @{:kind :var :name name :type typ})))

(defn- parse-var-decl []
  (def v (parse-typed-name))
  (when (accept :kw-at) (put v :at (expect-num)))
  (expect :semicolon)
  v)

(defn- parse-var-decls []            # for proc locals
  (def out @[])
  (while (not (at? :kw-begin))
    (array/push out (parse-var-decl)))
  out)

(def- binary-ops
  {:logical-or  {:bp 10 :op :or}   # weakest
   :logical-xor {:bp 15 :op :xor}
   :logical-and {:bp 20 :op :and}
   :plus        {:bp 40 :op :add}
   :minus       {:bp 40 :op :sub}}) # strongest

(defn- parse-ident []
  @{:kind :ident :value (expect-name)})

(var- parse-deref-or-ident nil)

(defn parse-expr [&opt min-bp]
  (default min-bp 0)
  (var lhs
       (case (kind)
         :num        (let [t (next!)] @{:kind :num :value (t 1)})
         :ident      (parse-deref-or-ident)
         :left-paren (do (next!)
                         (def e (parse-expr 0))
                         (expect :right-paren)
                         e)
         :addrof (do (next!)
                     (def what (parse-deref-or-ident))
                     @{:kind :addrof :what what})
         (fail "expression")))
  (forever
    (def info (binary-ops (kind)))
    (when (or (nil? info) (< (info :bp) min-bp)) (break))
    (next!)
    (def rhs (parse-expr (+ (info :bp) 1)))
    (set lhs @{:kind :binop :op (info :op) :lhs lhs :rhs rhs}))
  lhs)

(set parse-deref-or-ident (fn []
  (def id (parse-ident))
  (if (at? :left-bracket)
    (do (next!)
        (def idx (parse-expr 0))
        (expect :right-bracket)
        @{:kind :deref-ident :what id :idx idx})
    id)))

(defn- parse-stmt-set []
  (expect :kw-set)
  (def lvalue (parse-deref-or-ident))
  (expect :equals)
  (def rvalue (parse-expr))
  (expect :semicolon)
  @{:kind :set :lvalue lvalue :rvalue rvalue})

(defn- parse-stmt-return []
  (expect :kw-return)
  (expect :semicolon)
  @{:kind :return})

(defn- parse-stmt-call []
  (expect :kw-call)
  (def target (parse-ident))
  (def args (parse-list parse-expr :comma))
  (def into (if (accept :kw-into) (parse-list parse-ident :comma) @[]))
  (expect :semicolon)
  @{:kind :call :target target :args args :into into})

(defn- parse-stmts []
  (def stmts @[])
  (while (not (at? :kw-end))
    (array/push stmts
                (case (kind)
                  :kw-set    (parse-stmt-set)
                  :kw-return (parse-stmt-return)
                  :kw-call   (parse-stmt-call)
                  (fail "statement"))))
  stmts)

(defn- parse-proc []
  (expect :kw-proc)
  (def name (expect-name))
  (def args (if (at? :left-paren)
              (parse-list parse-typed-name :semicolon) @[]))
  (def returns (if (accept :kw-returns)
                 (parse-list parse-typed-name :semicolon) @[]))
  (def addr (when (accept :kw-at) (expect-num)))
  (expect :kw-is)
  (def locals (parse-var-decls))
  (expect :kw-begin)
  (def body (parse-stmts))
  (expect :kw-end)
  (expect :kw-proc)
  (expect :semicolon)
  @{:kind :proc :name name :at addr :args args
    :locals locals :returns returns :body body})

(defn- parse-decls []                # program level: vars and procs mixed
  (def globals @[])
  (def procs @[])
  (while (not (at? :kw-begin))
    (if (at? :kw-proc)
      (array/push procs (parse-proc))
      (array/push globals (parse-var-decl))))
  [globals procs])

(defn parse-program [tokens]
  (set toks tokens)
  (set pos 0)
  (expect :kw-program)
  (def name (expect-name))
  (def addr (when (accept :kw-at) (expect-num)))
  (expect :kw-is)
  (def [globals procs] (parse-decls))
  (expect :kw-begin)
  (def body (parse-stmts))
  (expect :kw-end)
  (expect :kw-program)
  (expect :semicolon)
  (expect :eof)
  @{:kind :program :name name :at addr
    :globals globals :procs procs :body body})

(def type-info
  {:byte    {:fits? (fn [v] (<= v 255))
             :size 1}
   :address {:fits? (fn [v] (<= v 65535))
             :size 2}})

# ------------- TYPE CHECKING & ANNOTATION ------------- #

(defn assignable? [expr]
  (case (expr :kind)
    :ident true
    :deref-ident true
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

    :deref-ident
    (let [what (expr :what)
          idx  (expr :idx)]
      (unless (= (what :kind) :ident)
        (errorf "Can only index an identifier for now"))
      (def decl (resolve scope what))
      (if (= (idx :kind) :num)
        (do
          (unless (((type-info :byte) :fits?) (idx :value))
            (errorf "Array index %d doesn't fit in :byte" (idx :value)))
          (put idx :type :byte))
        (let [idx-type (infer-expr-type scope idx)]
          (unless (= :byte idx-type)
            (errorf "Array index must be :byte, got %V" idx-type))))
      (case (decl :kind)
        :array
        (do
          (put expr :type (decl :type))
          (decl :type))
        :var
        (if (= (decl :type) :address)
          (do
            (put expr :type :byte)
            :byte)
          (errorf "Cannot index value of type %V" (decl :type)))
        (errorf "Cannot index value of kind %V" (decl :kind))))

    :addrof
    (do
      (def what (expr :what))
      (unless (= (what :kind) :ident)
        (errorf "Can only take the address of an identifier for now"))
      (resolve scope what)
      (put expr :type :address)
      :address)

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
      (unless (type-info expected-type)
        (errorf "Internal: expected-type is %q, not a known type" expected-type))
      (unless (((type-info expected-type) :fits?) (expr :value))
        (errorf "Value %d doesn't fit in type %V" (expr :value) expected-type))
      (put expr :type expected-type)
      expected-type)

    :binop
    (expect-binop-type scope expr expected-type)

    :deref-ident
    (let [actual-type (infer-expr-type scope expr)]
      (unless (= expected-type actual-type)
        (errorf "Type missmatch: expected %V, got %V" expected-type actual-type))
      actual-type)

    :addrof
    (let [actual-type (infer-expr-type scope expr)]
      (unless (= expected-type actual-type)
        (errorf "Type missmatch: expected %V, got %V" expected-type actual-type))
      actual-type)

    (errorf "Cannot type-check expression `%q`" expr)))

(def- typed-binops {:add true :sub true})  # ops that codegen actually supports

(set expect-binop-type
     (fn [scope expr expected-type]
       (unless (typed-binops (expr :op))
         (errorf "Operator %V is not supported yet" (expr :op)))
       (expect-expr-type scope (expr :lhs) expected-type)
       (expect-expr-type scope (expr :rhs) expected-type)
       (put expr :type expected-type)
       expected-type))

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

# ------------- REGISTER ALLOCATION ------------- #

(defn classify-program [prog] prog)

# ------------- CALL GRAPH ------------- #

(def main-node "<main>")

(defn build-call-graph [prog]
  (def graph @{})
  (defn ensure [n] (unless (graph n) (put graph n @[])))

  (ensure main-node)
  (each proc (prog :procs) (ensure (proc :name)))

  (defn scan-body [from body]
    (each stmt body
      (when (= (stmt :kind) :call)
        (def callee (get-in stmt [:target :decl :name]))
        (array/push (graph from) callee))))

  (scan-body main-node (prog :body))
  (each proc (prog :procs)
    (scan-body (proc :name) (proc :body)))

  graph)

(defn check-cycles [graph]
  (def state @{})                       # nil => unvisited, :on-stack, :done

  (defn visit [node path]
    (case (get state node)
      :done     nil
      :on-stack
      (let [start (find |(= $ node) path)
            cycle (array/slice path start)]
        (errorf "Recursion is forbidden: %s"
                (string/join (map string cycle) " -> ")))
      (do
        (put state node :on-stack)
        (array/push path node)
        (each callee (graph node) (visit callee path))
        (array/pop path)
        (put state node :done))))

  (each node (sorted (keys graph))
    (visit node @[])))

(defn compute-depths [graph root]
  (def callers @{})
  (each from (keys graph)
    (each callee (graph from)
      (unless (get callers callee) (put callers callee @[]))
      (array/push (callers callee) from)))

  (def depths @{})
  (each node (keys graph) (put depths node 0))

  (var changed true)
  (while changed
    (set changed false)
    (each node (keys graph)
      (each caller (get callers node @[])
        (def candidate (+ 1 (depths caller)))
        (when (> candidate (depths node))
          (put depths node candidate)
          (set changed true)))))

  depths)

# ------------- LABELING AND ADDRESSING ------------- #

(defn proc-all-vars [proc]
  (array/concat @[] (proc :args) (proc :returns) (proc :locals)))

(defn proc-frame-size [proc]
  (var n 0)
  (each decl (proc-all-vars proc)
    (unless (decl :at)
      (+= n ((type-info (decl :type)) :size))))
  n)

(defn decl-size [decl]
  (case (decl :kind)
    :array (* (decl :length) ((type-info (decl :type)) :size))
    ((type-info (decl :type)) :size)))

(defn assign-proc-labels [proc depth]
  (var off 0)
  (each decl (proc-all-vars proc)
    (put decl :size (decl-size decl))
    (if (decl :at)
      (put decl :label (string (proc :name) "_" (decl :name)))
      (do
        (put decl :label (string "frame_" depth "+" off))
        (+= off (decl :size))))))

(defn allocate-shared-frames [prog]
  (def graph (build-call-graph prog))
  (check-cycles graph)
  (def depths (compute-depths graph main-node))

  (def procs-by-depth @{})
  (each proc (prog :procs)
    (def depth (depths (proc :name)))
    (unless (get procs-by-depth depth) (put procs-by-depth depth @[]))
    (array/push (procs-by-depth depth) proc))

  (each depth (keys procs-by-depth)
    (each proc (procs-by-depth depth)
      (assign-proc-labels proc depth)))

  (def frames @[])
  (each depth (sorted (keys procs-by-depth))
    (var max-size 0)
    (each proc (procs-by-depth depth)
      (set max-size (max max-size (proc-frame-size proc))))
    (when (> max-size 0)
      (array/push frames @{:label (string "frame_" depth)
                           :size  max-size})))
  frames)

(defn allocate-program [prog]
  (put prog :label (prog :name))

  (each proc (prog :procs)
    (put proc :label (proc :name)))

  (each decl (prog :globals)
    (put decl :label (decl :name))
    (put decl :size (decl-size decl)))

  (put prog :frames (allocate-shared-frames prog))
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

(defn codegen [out & instr] (array/concat out instr))

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

(defn codegen-copy-value [out src-operand dst-label size]
  (for off 0 size
    (codegen out [:lda ;src-operand])
    (codegen out [:sta :abs (string dst-label "+" off)])))

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

(defn codegen-deref-read [out expr]
  (def decl ((expr :what) :decl))
  (def idx (expr :idx))

  (case (decl :kind)
    :array
    (do
      (codegen-expr out idx)
      (codegen out [:tay :imp])
      (codegen out [:lda :abs-y (decl :label)]))
    :var
    (do
      (codegen-expr out idx)
      (codegen out [:tay :imp])
      (codegen out [:lda :abs   (decl :label)])
      (codegen out [:sta :abs   "tragolptr0"])
      (codegen out [:lda :abs   (string (decl :label) "+1")])
      (codegen out [:sta :abs   "tragolptr0+1"])
      (codegen out [:lda :ind-y "tragolptr0"]))))

(defn codegen-deref-store [out lvalue]
  (def decl ((lvalue :what) :decl))
  (def idx  (lvalue :idx))

  (case (decl :kind)
    :array
    (do
      (codegen-expr out idx)
      (codegen out [:tay :imp])
      (codegen out [:pla :imp])
      (codegen out [:sta :abs-y (decl :label)]))

    :var
    (do
      (codegen-expr out idx)
      (codegen out [:tay :imp])
      (codegen out [:lda :abs   (decl :label)])
      (codegen out [:sta :abs   "tragolptr0"])
      (codegen out [:lda :abs   (string (decl :label) "+1")])
      (codegen out [:sta :abs   "tragolptr0+1"])
      (codegen out [:pla :imp])
      (codegen out [:sta :ind-y "tragolptr0"]))

    (errorf "Cannot store to deref of kind %V" (decl :kind))))

(set codegen-expr
     (fn [out expr]
       (cond
         (trivial? expr)
         (codegen out [:lda ;(operand expr)])

         (= (expr :kind) :binop)
         (codegen-expr-binop out expr)

         (= (expr :kind) :deref-ident)
         (codegen-deref-read out expr)

         (= (expr :kind) :addrof)
         (errorf "& is only supported for right-hand-side of `set` (for now?)")

         (errorf "Cannot generate expression `%q`" (expr :kind)))))

(defn codegen-stmt-return [out stmt] (codegen out [:rts :imp]))

(defn codegen-arg [out arg arg-decl]
  (case (arg-decl :type)
    :address
    (let [src (get-in arg [:decl :label])
          dst (arg-decl :label)]
      (codegen out [:lda :abs src])
      (codegen out [:sta :abs dst])
      (codegen out [:lda :abs (string src "+1")])
      (codegen out [:sta :abs (string dst "+1")]))
    (do
      (codegen-expr out arg)
      (codegen-store out (decl-operand arg-decl)))))

(defn codegen-stmt-call [out stmt]
  (def callee (get-in stmt [:target :decl]))
  (for i 0 (length (stmt :args))
    (codegen-arg out ((stmt :args) i) ((callee :args) i)))
  (codegen out [:jsr :abs (callee :label)])
  (for i 0 (length (stmt :into))
    (let [dst ((stmt :into) i)
          ret ((callee :returns) i)]
      (case (ret :type)
        :address
        (do
          (codegen out [:lda :abs (ret :label)])
          (codegen out [:sta :abs (get-in dst [:decl :label])])
          (codegen out [:lda :abs (string (ret :label) "+1")])
          (codegen out [:sta :abs (string (get-in dst [:decl :label]) "+1")]))
        (do
          (codegen out [:lda :abs (ret :label)])
          (codegen-store out (operand dst)))))))

(defn codegen-stmt-set [out stmt]
  (def lvalue (stmt :lvalue))
  (def rvalue (stmt :rvalue))

  (cond
    (and (= (lvalue :kind) :ident)
         (= (rvalue :kind) :addrof))
    (let [src-decl  ((rvalue :what) :decl)
          src-label (src-decl :label)
          dst-label (get-in lvalue [:decl :label])]
      (codegen out [:lda :imm (string "<" src-label)])
      (codegen out [:sta :abs dst-label])
      (codegen out [:lda :imm (string ">" src-label)])
      (codegen out [:sta :abs (string dst-label "+1")]))

    (= (lvalue :kind) :ident)
    (do (codegen-expr out rvalue)
        (codegen-store out (operand lvalue)))

    (= (lvalue :kind) :deref-ident)
    (do (codegen-expr out rvalue)
        (codegen out [:pha :imp])
        (codegen-deref-store out lvalue))

    (errorf "Cannot assign to `%q`" lvalue)))

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

  (codegen equates [:equ "tragolptr0"   0xFB]) # TODO: configurable

  (each decl (prog :globals)
    (if (decl :at)
      (codegen equates [:equ (decl :label) (decl :at)])
      (codegen vars    [:res (decl :label) (decl :size)])))

  (each proc (prog :procs)
    (each decl (proc-all-vars proc)
      (when (decl :at)
        (codegen equates [:equ (decl :label) (decl :at)]))))

  (each frame (prog :frames)
    (codegen vars [:res (frame :label) (frame :size)]))

  (each proc (prog :procs)
    (codegen-proc (if (proc :at) fixed-procs procs) proc))

  (when-let [at (prog :at)] (codegen main-body [:org at]))
  (codegen main-body [:label (prog :label)])
  (each stmt (prog :body) (codegen-stmt main-body stmt))

  (array/concat @[] equates main-body procs vars fixed-procs))

# ------------- ASSEMBLY GENERATION (backend) ------------- #

(def modes
  {:imp   (fn [mnemonic]       (string "    " mnemonic))
   :imm   (fn [mnemonic value] (string "    " mnemonic " #" value))
   :abs   (fn [mnemonic value] (string "    " mnemonic " " value))
   :abs-x (fn [mnemonic value] (string "    " mnemonic " " value ",x"))
   :abs-y (fn [mnemonic value] (string "    " mnemonic " " value ",y"))
   :ind-y (fn [mnemonic value] (string "    " mnemonic " (" value "),y"))})

(defn emit-item [code]
  (match code
    [:org addr]           (printf "* = $%04X" addr)
    [:label labl]         (print labl)
    [:equ labl value]     (printf "%s = $%X" labl value)
    [:res labl size]      (printf "%s .fill %d" labl size)
    [mnemonic :imp]       (print ((modes :imp) mnemonic))
    [mnemonic mode value] (print ((modes mode) mnemonic value))
    (errorf "Malformed code: `%q`" code)))

# ------------- WORKFLOW ------------- #

(defn main [& args]
  (when (< (length args) 2)
    (errorf "Usage: %s src-path" (args 0)))
  (def src (slurp (args 1)))

  (def program (parse-program (lex src)))
  # (def program ast)

  (def passed-around   # all info codegen could ever need
    (allocate-program  # compute frames and allocate labels
     (classify-program # assign registers, clobber tables, etc.
      (annotate-program program)))) # typecheck, link declarations
  (def ir (codegen-program passed-around))  # emit a flat internal representation
  (each item ir (emit-item item)))  # emit 64tass 6502 assembly

# kept for debugging purposes
(def source `program addressing is
    buffer: 10 of byte;  -- buffer .fill 10
    i: byte;
    buffer_ptr: address;

    proc stuff (ptr: address; idx: byte) returns (thing: byte) is
    begin
        set thing = ptr[idx];
        return;
    end proc;
begin
    set buffer_ptr = &buffer;
    set i = 3;

    set buffer[i] = 69;

    call stuff (buffer_ptr, i) into (i);
end program;
`)
(def ast @{:kind :program
           :name "addressing"
           :globals @[@{:kind :array :name "buffer" :length 10 :type :byte}
                      @{:kind :var :name "i" :type :byte}
                      @{:kind :var :name "buffer_ptr" :type :address}]
           :procs @[@{:kind :proc
                      :name "stuff"
                      :args @[@{:kind :var :name "ptr" :type :address}
                              @{:kind :var :name "idx" :type :byte}]
                      :locals @[]
                      :returns @[@{:kind :var :name "thing" :type :byte}]
                      :body @[@{:kind :set
                                :lvalue @{:kind :ident :value "thing"}
                                :rvalue @{:kind :deref-ident
                                          :what @{:kind :ident :value "ptr"}
                                          :idx @{:kind :ident :value "idx"}}}
                              @{:kind :return}]}]
           :body @[@{:kind :set
                     :lvalue @{:kind :ident :value "buffer_ptr"}
                     :rvalue @{:kind :addrof
                               :what @{:kind :ident :value "buffer"}}}
                   @{:kind :set
                     :lvalue @{:kind :ident :value "i"}
                     :rvalue @{:kind :num :value 3}}
                   @{:kind :set
                     :lvalue @{:kind :deref-ident
                               :what @{:kind :ident :value "buffer"}
                               :idx @{:kind :ident :value "i"}}
                     :rvalue @{:kind :num :value 69}}
                   @{:kind :call
                     :target @{:kind :ident :value "stuff"}
                     :args @[@{:kind :ident :value "buffer_ptr"}
                             @{:kind :ident :value "i"}]
                     :into @[@{:kind :ident :value "i"}]}]})
