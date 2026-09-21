module

public import SynthDom.Syntax.Ty.Syntax

@[expose] public section

declare_syntax_cat term_lang
syntax:max ident : term_lang
syntax:max "_" : term_lang
syntax:max "[" term "]ₛ" : term_lang
syntax:max "[" term "]ₘ" : term_lang
syntax:max "♯(" num "," ppSpace num ")" : term_lang

syntax:90 "λ" ppSpace ident (ppSpace ":" ppSpace type_lang)? "." ppSpace term_lang : term_lang
syntax:90 "λ" ppSpace "_" (ppSpace ":" ppSpace type_lang)? "." ppSpace term_lang : term_lang
syntax:90 "fix" ppSpace ident (ppSpace ":" ppSpace type_lang)? "." ppSpace term_lang : term_lang
syntax:90 "fix" ppSpace "_" (ppSpace ":" ppSpace type_lang)? "." ppSpace term_lang : term_lang
syntax:90 "∀" ppSpace ident (ppSpace ":" ppSpace type_lang)? "." ppSpace term_lang : term_lang
syntax:90 "∀" ppSpace "_" (ppSpace ":" ppSpace type_lang)? "." ppSpace term_lang : term_lang
syntax:90 "∃" ppSpace ident (ppSpace ":" ppSpace type_lang)? "." ppSpace term_lang : term_lang
syntax:90 "∃" ppSpace "_" (ppSpace ":" ppSpace type_lang)? "." ppSpace term_lang : term_lang

syntax:100 term_lang:101 ppSpace term_lang:100 : term_lang
syntax:80 "delay" ppSpace term_lang:arg : term_lang
syntax:80 "adv" ppSpace num ppSpace term_lang:arg : term_lang

syntax:min term_lang:50 ppSpace ":" ppSpace type_lang:50 : term_lang
syntax:max "δ" term:arg (ppSpace ":" ppSpace term)? : term_lang
syntax:50 "⌜" term_lang "⌝" : term_lang
syntax:100 term_lang:101 ppSpace (("⊙{" term "}") <|> "⊙") ppSpace term_lang:100 : term_lang
syntax "⟨" term_lang "," ppSpace term_lang "⟩" : term_lang
syntax:50 "π₁" ppSpace term_lang:arg : term_lang
syntax:50 "π₂" ppSpace term_lang:arg : term_lang
syntax:50 "inl" ppSpace term_lang:arg : term_lang
syntax:50 "inr" ppSpace term_lang:arg : term_lang
syntax:50 "case" ppSpace term_lang:arg ppSpace term_lang:arg ppSpace term_lang:arg : term_lang
syntax "(" ppDedent(term_lang) ")" : term_lang

syntax:25 term_lang:26 ppSpace "→" ppSpace term_lang:25 : term_lang
syntax:30 term_lang:31 ppSpace "∨" ppSpace term_lang:30 : term_lang
syntax:35 term_lang:36 ppSpace "∧" ppSpace term_lang:35 : term_lang

syntax:80 "lift" ppSpace term_lang:arg : term_lang
syntax "⊤" : term_lang
syntax "⊥" : term_lang
syntax:10 term_lang:10 ppSpace "=" ppSpace term_lang:10 : term_lang
syntax "⟪" term_lang "⟫" : term
