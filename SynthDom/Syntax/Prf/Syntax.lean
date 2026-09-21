module

public import Lean
public import SynthDom.Syntax.Ty.Syntax
public import SynthDom.Syntax.Expr.Syntax

@[expose] public section

syntax local_hyp := ppIndent(term:max " : " ((type_lang <|> term_lang <|> term)))
syntax ctx_line := local_hyp <|> "─────▷─────"
syntax "Guarded:" ppIndent((ppLine ctx_line)*) ppLine ppIndent("⊢ " ((term_lang <|> term))) : term
