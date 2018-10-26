# formula-evaluator
Simple formula parser and evaluator.
Now could parse Double and Bool expression,
it could be extended by providing Ops instance with list of expectable functions
# Expression syntax
```
<delimiter-character> ::= " " | "," | ";"
<delimiter> ::= <delimiter-character>+
<symbol> ::= (not <delimiter-character>)+
<prefix-expression> ::= [<delimiter>] <symbol> (<delimiter> <unary>)+ | "(" <prefix-expression> ")"
<infix-expression> ::= <unary> <delimiter> <symbol> <delimiter> <unary> | "(" <infix-expression> ")"
<unary> ::= [<delimiter>] (<symbol> | <prefix-expression> | <infix-expression>) [<delimiter>]
<expression> ::= <unary>
```
# Plan:
- [x] Parse and evaluate `Parse t => Expr t`, if specified list of operators under `t` then `Ops t`, `Parse t = (Read t, Ops t)`
- [x] `Parse t => WithDefaults t`, custom default symbols which are interpretered as `t`
- [x] Prefix and infix operators
- [x] Precedence for infix operators
- [x] Arity for prefix operators
- [x] Right/left associativity for infix operators
- [ ] Processing file
- [ ] `type ExprOp t = forall a. Parse a => Op a t` instead of `Op t t`
