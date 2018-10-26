# formula-evaluator
Simple formula parser and evaluator.
Now could parse Double and Bool expression,
it could be extended by providing Ops instance with list of expectable functions
# Expression syntax
```bison
<delimiter-character> ::= " " | "," | ";"
<delimiter> ::= <delimiter-character>+
<symbol> ::= (not <delimiter-character>)+
<prefix-expression> ::= [<delimiter>] <symbol> (<delimiter> <unary>)+ | "(" <prefix-expression> ")"
<infix-expression> ::= <unary> <delimiter> <symbol> <delimiter> <unary> | "(" <infix-expression> ")"
<unary> ::= [<delimiter>] (<symbol> | <prefix-expression> | <infix-expression>) [<delimiter>]
<expression> ::= <unary>
```
# TODO:
- [ ] Associativity
