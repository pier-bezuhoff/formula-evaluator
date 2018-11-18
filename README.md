# formula-evaluator
Simple formula parser and evaluator from scratch.
Could parse Double, Bool and mixed expression,
it could be extended by providing `Parseable` instance with list of expectable predefined variables and functions
# Expression syntax
```
<delimiter-character> ::= " " | "," | ";"
<delimiter> ::= <delimiter-character>+
<symbol> ::= (not <delimiter-character>)+
<prefix-expression> ::= [<delimiter>] <symbol> (<delimiter> <unary>)+ | "(" <prefix-expression> ")"
<infix-expression> ::= <unary> <delimiter> <symbol> <delimiter> <unary> | "(" <infix-expression> ")"
<unary> ::= [<delimiter>] (<symbol> | <prefix-expression> | <infix-expression>) [<delimiter>]
<expression> ::= <unary>
<statement> ::= <symbol> " "+ "=" " "+ <expression> | <expression>
```
# Plan:
- [x] Parse and evaluate `Parseable t => Expr t`
- [x] Parse reverse polish notation
- [x] `Parseable t => defaultScope :: Scope t`, custom default symbols which are interpretered as `t`
- [x] Prefix and infix operators
- [x] Precedence for infix operators
- [x] Arity for prefix operators
- [x] Right/left associativity for infix operators
- [x] Processing file
- [x] REPL (on \<expression\> or \<statement\>)
- [x] REPL additional commands: `:parse`, `:tokenize`, `:toRPN`, `:parseRPN`, `:evalRPN`, `:type` and then \<expression\>; `:vars`, `:ops`, `:typedOps`, `:help`, `:quit`
- [x] Type for parseable types via existentials
- [x] Poly-type operator signature (e.g. `== : [Double, Double] -> Bool`)
- [x] Auto-generate `==`, `!=`, `ifThenElse` functions for `Parseable` instances
- [x] When failed, show error for each of tried strategies
- [x] Overlapping operators (e.g. `==` for `Double` and `Bool`) resolved by signature
- [ ] Generalize `Op` type in order to allow cross-type equality (e.g. `10 === False` -> `False`)
- [ ] Maybe replace `ifThenElse cond a b` with `if cond then a else b`
- [ ] Parse S-expressions
