module

public import Lean
public import SynthDom.Syntax.Prf.Syntax

@[expose] public section

syntax "gintro " (ppSpace colGt ident)+ : tactic
syntax "gsplit" : tactic
syntax "gleft" : tactic
syntax "gright" : tactic
syntax "gexfalso" : tactic

declare_syntax_cat gcases_pat
syntax ident : gcases_pat
syntax "_" : gcases_pat
syntax "⟨" gcases_pat ", " gcases_pat "⟩" : gcases_pat
syntax "⟨" gcases_pat ", " gcases_pat ", " gcases_pat "⟩" : gcases_pat
syntax "(" gcases_pat " | " gcases_pat ")" : gcases_pat
syntax "gcases " term_lang:max " with " gcases_pat : tactic
syntax "gapply " ident (ppSpace colGt term_lang:arg)* : tactic
syntax "gapply " "(" term ")" (ppSpace colGt term_lang:arg)* : tactic
syntax "glöb " ident : tactic
syntax "gsimpl" : tactic
syntax "gnext" : tactic
syntax "gunfold " ident " at " ident : tactic
syntax "gunfold " ident : tactic
syntax "gembed" : tactic
syntax "gpoints" ppSpace ident : tactic
syntax "gtrivial" : tactic
syntax "grfl" : tactic
syntax "gfix" : tactic
syntax "grename " "hypothesis" ident " to " ident : tactic
syntax "gclear " "hypothesis" ident : tactic
syntax "gspecialize " ident (ppSpace colGt term_lang:arg)+ " as " ident : tactic
syntax "gspecialize " ident (ppSpace colGt term_lang:arg)+ : tactic
syntax "gexact " ident : tactic
syntax "gassumption" : tactic
syntax "gexists " term_lang:arg : tactic
syntax "ginjection " ident " as " ident : tactic
syntax "grewrite " ident (ppSpace colGt term_lang:arg)* (" at " ident)? : tactic
syntax "grewrite " "←" ident (ppSpace colGt term_lang:arg)* (" at " ident)? : tactic
syntax "grewrite " "(" term ")" (ppSpace colGt term_lang:arg)* (" at " ident)? : tactic
syntax "grewrite " "←" "(" term ")" (ppSpace colGt term_lang:arg)* (" at " ident)? : tactic
syntax "gassert " ident " of " term_lang:arg : tactic
syntax "gmono " (ppSpace colGt ident)+ " as " (ppSpace colGt ident)+ : tactic
syntax "gpose " term " as " ident : tactic
syntax "gcong" : tactic
