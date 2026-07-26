# Basic practical grammar benchmark suite

This suite provides a token-level JSON grammar and two arithmetic grammars.
Tokenization is deliberately outside the CFG: `STRING`, `NUMBER`, `NUM`, and
punctuation/operator names each denote one lexer token. This keeps benchmarks
focused on parsing rather than character-level lexing.

All three grammars are epsilon-free. JSON has no left recursion. The two
arithmetic grammars use conventional direct left recursion, which the Earley
parser supports; this also avoids adding epsilon productions merely to encode
operator tails.

Repetition notation such as `(COMMA NUMBER)^n` is used only to specify generated
inputs. It is not part of the grammar.

## JSON

```text
JSON     -> Value

Value    -> Object
Value    -> Array
Value    -> STRING
Value    -> NUMBER
Value    -> TRUE
Value    -> FALSE
Value    -> NULL

Object     -> LBRACE ObjectBody

ObjectBody -> RBRACE
ObjectBody -> Pair ObjectRest

ObjectRest -> RBRACE
ObjectRest -> COMMA Pair ObjectRest

Pair       -> STRING COLON Value

Array      -> LBRACKET ArrayBody

ArrayBody  -> RBRACKET
ArrayBody  -> Value ArrayRest

ArrayRest  -> RBRACKET
ArrayRest  -> COMMA Value ArrayRest
```

This is an epsilon-free, non-left-recursive, predictive grammar when the lexer
provides the token kinds shown above. It is explicitly left-factored and LL(1):
after an opening brace/bracket, the closing token selects the empty form and a
value-starting token selects the nonempty form.

### Generated JSON inputs

Use a flat numeric array for a controlled linear family:

```text
JSON-array(n) =
  LBRACKET NUMBER (COMMA NUMBER)^(n-1) RBRACKET
```

| Size | Elements | Token count | Concrete/token-pattern input |
|---|---:|---:|---|
| Small | 4 | 9 | `[ 0 , 1 , 2 , 3 ]` |
| Medium | 64 | 129 | `[ NUMBER (COMMA NUMBER)^63 ]` |
| Large | 1,024 | 2,049 | `[ NUMBER (COMMA NUMBER)^1023 ]` |

Use a flat object to exercise member parsing:

```text
JSON-object(n) =
  LBRACE STRING COLON NUMBER
    (COMMA STRING COLON NUMBER)^(n-1)
  RBRACE
```

| Size | Members | Token count | Concrete/token-pattern input |
|---|---:|---:|---|
| Small | 3 | 13 | `{ "a" : 1 , "b" : 2 , "c" : 3 }` |
| Medium | 32 | 129 | `{ STRING COLON NUMBER (COMMA STRING COLON NUMBER)^31 }` |
| Large | 256 | 1,025 | `{ STRING COLON NUMBER (COMMA STRING COLON NUMBER)^255 }` |

Use recursive singleton arrays to isolate nesting depth:

```text
JSON-nested(d) = LBRACKET^d NUMBER RBRACKET^d
```

| Size | Depth | Token count | Concrete/token-pattern input |
|---|---:|---:|---|
| Small | 4 | 9 | `[ [ [ [ 0 ] ] ] ]` |
| Medium | 32 | 65 | `LBRACKET^32 NUMBER RBRACKET^32` |
| Large | 256 | 513 | `LBRACKET^256 NUMBER RBRACKET^256` |

## Naive arithmetic without precedence

```text
Expr -> Expr PLUS Expr
Expr -> Expr MINUS Expr
Expr -> Expr TIMES Expr
Expr -> Expr DIV Expr
Expr -> LPAREN Expr RPAREN
Expr -> NUM
```

All binary operators have the same undifferentiated status. This grammar is
epsilon-free and intentionally ambiguous: an unparenthesized chain with `n`
operands has the different binary association trees, and mixed operators do
not receive precedence. For example, `NUM PLUS NUM TIMES NUM` has parses
corresponding to both `(NUM + NUM) * NUM` and `NUM + (NUM * NUM)`.

### Generated naive-arithmetic inputs

Use an unparenthesized mixed-operator cycle:

```text
NAIVE(n) =
  NUM (op_i NUM)^(n-1)

op_i cycles through PLUS, TIMES, MINUS, DIV
```

| Size | Operands | Token count | Concrete/token-pattern input |
|---|---:|---:|---|
| Small | 4 | 7 | `1 + 2 * 3 - 4` |
| Medium | 32 | 63 | `NUM (cycled-op NUM)^31` |
| Large | 256 | 511 | `NUM (cycled-op NUM)^255` |

These inputs intentionally exercise ambiguity. For a uniquely parsed control
using the same grammar, fully parenthesize every operation:

```text
NAIVE-control(n) =
  LPAREN^(n-1) NUM
  (op_i NUM RPAREN)^(n-1)
```

The control has `4n - 3` tokens: 13 for 4 operands, 125 for 32 operands, and
1,021 for 256 operands.

## Arithmetic with precedence

```text
Expr   -> Expr PLUS Term
Expr   -> Expr MINUS Term
Expr   -> Term

Term   -> Term TIMES Factor
Term   -> Term DIV Factor
Term   -> Factor

Factor -> LPAREN Expr RPAREN
Factor -> NUM
```

This epsilon-free grammar gives `TIMES` and `DIV` higher precedence than
`PLUS` and `MINUS`; direct left recursion gives left associativity within each
precedence level. Every valid token stream has one parse.

### Generated precedence-arithmetic inputs

For direct comparison with the naive grammar, use the identical mixed-operator
token stream:

```text
PREC(n) =
  NUM (op_i NUM)^(n-1)

op_i cycles through PLUS, TIMES, MINUS, DIV
```

| Size | Operands | Token count | Concrete/token-pattern input |
|---|---:|---:|---|
| Small | 4 | 7 | `1 + 2 * 3 - 4` |
| Medium | 32 | 63 | `NUM (cycled-op NUM)^31` |
| Large | 256 | 511 | `NUM (cycled-op NUM)^255` |

The shared token stream makes the comparison useful: the naive grammar builds
an ambiguous chart, while the precedence grammar recognizes one intended parse.

Use an additional parenthesized family to test nesting:

```text
PREC-nested(d) = LPAREN^d NUM PLUS NUM RPAREN^d
```

| Size | Depth | Token count | Concrete/token-pattern input |
|---|---:|---:|---|
| Small | 4 | 11 | `( ( ( ( 1 + 2 ) ) ) )` |
| Medium | 32 | 67 | `LPAREN^32 NUM PLUS NUM RPAREN^32` |
| Large | 256 | 515 | `LPAREN^256 NUM PLUS NUM RPAREN^256` |

## Input generation

The following language-neutral pseudocode produces the scalable families:

```text
json_array(n):
  return [LBRACKET]
       + intersperse(COMMA, repeat(NUMBER, n))
       + [RBRACKET]

json_object(n):
  pair = [STRING, COLON, NUMBER]
  return [LBRACE]
       + intersperse(COMMA, repeat(pair, n))
       + [RBRACE]

json_nested(d):
  return repeat(LBRACKET, d) + [NUMBER] + repeat(RBRACKET, d)

arithmetic(n):
  ops = cycle([PLUS, TIMES, MINUS, DIV])
  result = [NUM]
  for i in 0 .. n - 2:
    result += [ops[i], NUM]
  return result
```

Generate token lists once and reuse the exact lists across parser
implementations. Report the operand/element count, total token count,
acceptance result, ambiguity policy, chart size, and timing for each run.
