# formula-evaluator
Simple formula parser and evaluator.
Now could parse Double and Bool expression,
it could be extended by providing `Parse` instance with list of expectable functions
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
- [x] Parse and evaluate `Parse t => Expr t`, if specified list of operators under `t` then `Ops t`, `Parse t = (Read t, Ops t)`
- [x] Parse reverse polish notation
- [x] `Parse t => WithDefaults t`, custom default symbols which are interpretered as `t`
- [x] Prefix and infix operators
- [x] Precedence for infix operators
- [x] Arity for prefix operators
- [x] Right/left associativity for infix operators
- [x] Processing file
- [x] REPL (on <statement>)
- [x] REPL additional functions: `:parse`, `:tokenize`, `:toRPN`, `:parseRPN`, `:evalRPN` and then <expression>; `:help`, `:quit`
- [ ] Parse S-expressions
- [ ] Poly-type signature:
```haskell
type Type = forall t. Parse t => t
data Op = { ... signature :: [Type] ... }
```
