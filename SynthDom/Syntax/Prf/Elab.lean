module

public meta import Lean
public meta import Qq

public meta import SynthDom.Syntax.Prf.Core
public meta import SynthDom.Syntax.Prf.Wrappers
public import SynthDom.Syntax.Expr.Syntax
public meta import SynthDom.Syntax.Expr.Elab
public meta import SynthDom.Config.Options
public meta import SynthDom.Config.Attr

@[expose] public meta section

section ty

open Lean Elab Meta PrettyPrinter Delaborator SubExpr Qq

syntax "gtheorem" ident (ppSpace bracketedBinder)* (" : " term_lang) " := " term : command
elab_rules : command | `(gtheorem $id $bs:bracketedBinder* : $e := $prf) => do
  let name : Name := id.getId
  guardedAttrExt.add name
  Command.elabCommand
    (← `(command| theorem $id $bs:bracketedBinder* : GOAL [[]] [[]] [[]] [[]] ⟪ $e ⟫ := $prf))
