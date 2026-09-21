module

@[expose] public section
declare_syntax_cat type_lang
syntax:60 "Δ" ppSpace term:arg : type_lang
syntax:50 type_lang:51 ppSpace "×" ppSpace type_lang:50 : type_lang
syntax:45 type_lang:46 ppSpace "⊕" ppSpace type_lang:45 : type_lang
syntax:30 type_lang:31 ppSpace "→" ppSpace type_lang:30 : type_lang
syntax:60 "▸" ppSpace type_lang:arg : type_lang
syntax "Ω" : type_lang
syntax "(" ppDedent(type_lang) ")" : type_lang
syntax:max "[" term "]" : type_lang
syntax:max "[" term "]ₘ" : type_lang
syntax:max ident : type_lang
syntax "⦃" type_lang "⦄" : term
