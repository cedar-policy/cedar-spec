/-
 Copyright Cedar Contributors

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

import VersoManual
import Verso.Doc.ArgParse
import Verso.Doc.Elab

/-! # `grammar` code block

A Verso code block for the extension-type grammars, structured in the `format_spec` style with
three keyword-introduced sections:

```grammar
grammar
  Decimal  ::= Integer '.' Fraction
  …
value
  value(Decimal) = …
constraints
  value(Decimal) ∈ [Int64.min, Int64.max]
```

Rendering is the plain code block, except that a line consisting solely of one of the section
keywords `grammar` / `value` / `constraints` is set in bold with the Cedar accent color, visually
separating the three tiers from the production rules themselves. -/

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual Html
open Verso.Output (Html)

namespace CedarDoc

/-- Is this line exactly a section keyword (modulo trailing whitespace)? -/
private def isKeywordLine (l : String) : Bool :=
  let t := l.trimAsciiEnd.toString
  t == "grammar" || t == "value" || t == "constraints"

block_extension Block.grammarBlock (content : String) where
  data := Json.str content
  extraCss := [
    r#"
pre.cedar-grammar {
  font-family: var(--verso-code-font-family);
  background-color: var(--verso-code-background-color, #f6f6f6);
  padding: 0.75rem 1rem;
  overflow-x: auto;
}
pre.cedar-grammar .cedar-grammar-kw {
  font-weight: 700;
  color: #2f6f4f;
}
"#
  ]
  traverse _ _ _ := pure none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      let .str s := data
        | reportError "Expected string JSON for grammar block" *> pure .empty
      let lines := s.splitToList (· == '\n')
      let rendered : Array Html := lines.toArray.map fun l =>
        if isKeywordLine l then
          {{ <span class="cedar-grammar-kw">{{l}}</span> }} ++ Html.text false "\n"
        else
          Html.text false (l ++ "\n")
      pure {{ <pre class="cedar-grammar">{{rendered}}</pre> }}
  toTeX :=
    some <| fun _ _ _ data _ => do
      let .str s := data
        | reportError "Expected string JSON for grammar block" *> pure .empty
      pure (.raw s!"\\begin\{verbatim}\n{s}\n\\end\{verbatim}\n")

@[code_block]
def grammar : CodeBlockExpanderOf Unit
  | (), str =>
    ``(Verso.Doc.Block.other (Block.grammarBlock $(quote str.getString))
        #[Verso.Doc.Block.code $(quote str.getString)])

end CedarDoc
