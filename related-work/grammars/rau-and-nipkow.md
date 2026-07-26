The JSON grammar from `Examples.thy`.

## Commented JSON grammar

`Examples.thy` also contains a substantially larger JSON grammar, but its
entire section—including `JSON_rules`, `JSON_cfg`, and five JSON inputs—is
inside an Isabelle block comment. It is therefore reference material rather
than part of the active `Earley_Parser` session. The rule list expands the
`character` range into individual character productions; the equivalent
compact grammar written in the source is:

```text
json       -> element

value      -> object
            | array
            | string
            | number
            | "true"
            | "false"
            | "null"

object     -> "{" "}"
            | "{" ws "}"
            | "{" members "}"

members    -> member
            | member "," members

member     -> identifier ":" element

identifier -> string
            | ws string
            | string ws
            | ws string ws

array      -> "[" "]"
            | "[" ws "]"
            | "[" elements "]"

elements   -> element
            | element "," elements

element    -> value
            | ws value
            | value ws
            | ws value ws

ws         -> wssymbol
            | wssymbol ws

wssymbol   -> U+0020
            | U+000A
            | U+000D
            | U+0009

string     -> DQUOTE DQUOTE
            | DQUOTE characters DQUOTE

characters -> character
            | character characters

character  -> U+0020..U+00FF except DQUOTE and REVERSE_SOLIDUS
            | REVERSE_SOLIDUS escape

escape     -> DQUOTE
            | REVERSE_SOLIDUS
            | "/"
            | "b"
            | "f"
            | "n"
            | "r"
            | "t"
            | "u" hex hex hex hex

hex        -> digit
            | "A" | "B" | "C" | "D" | "E" | "F"
            | "a" | "b" | "c" | "d" | "e" | "f"

number     -> integer
            | integer exponent
            | integer fraction
            | integer fraction exponent

fraction   -> "." digits

exponent   -> expsymbol digits
            | expsymbol sign digits

expsymbol  -> "E" | "e"
sign       -> "+" | "-"

integer    -> digit
            | onenine digits
            | "-" digit
            | "-" onenine digits

digits     -> digit
            | digit digits

digit      -> "0"
            | onenine

onenine    -> "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9"
```

Here `DQUOTE` is `"` (U+0022) and `REVERSE_SOLIDUS` is `\` (U+005C).
The prose grammar calls the nonterminal `value`; its Isabelle datatype
constructor and rule-list symbol are named `val`.

The source explicitly notes that characters from U+0100 through U+10FFFF are
omitted. Its implemented `character` alternatives cover U+0020 through U+00FF
except `"` and `\`, plus the escape-prefixed form. The source also proves
`JSON_cfg` epsilon-free, although that proof is inactive while the section
remains commented out.
