module

public import Lean
public import Qq

public import SynthDom.Syntax.Ty.Core
public import SynthDom.Syntax.Ty.Syntax
public import SynthDom.Config.Options
public meta import SynthDom.Config.Attr

public import SynthDom.Semantics.Base

@[expose] public section

section ty

open Lean Elab Meta PrettyPrinter Delaborator SubExpr Qq

abbrev TypeElabM := ReaderT Unit TermElabM

meta def TypeElabM.run (x : TypeElabM α) : TermElabM α :=
  ReaderT.run x ()

meta partial def elabTYPE (i : Level) : TSyntax `type_lang → TypeElabM Q(TYPE.{i})
  | `(type_lang| [ $id:term ]) => do
    try
      let s ← elabTermEnsuringTypeQ id (expectedType := q(TYPE.{i}))
      pure s
    catch _ =>
      throwError "Unexpected identifier {id}."
  | `(type_lang| $id:ident) => do
    try
      let s ← elabTermEnsuringTypeQ id (expectedType := q(TYPE.{i}))
      pure s
    catch _ =>
      throwError "Unexpected identifier {id}."
  | `(type_lang| [ $id:term ]ₘ) => do
    try
      let s ← elabTermEnsuringTypeQ id (expectedType := q(ℐ.{i}))
      pure q(TYPE.ax $s)
    catch _ =>
      throwError "Unexpected identifier {id}."
  | `(type_lang| Δ $x:term) => do
    let t ← Term.elabType x
    if let some r ← checkTypeQ t q(Type (imax i 0)) then
      pure q(TYPE.embed $(r))
    else
      throwError "Invalid type: {t} is not a type of level {i}"
  | `(type_lang| $x:type_lang × $y:type_lang) => do
    pure q(TYPE.prod $(← elabTYPE i x) $(← elabTYPE i y))
  | `(type_lang| $x:type_lang ⊕ $y:type_lang) => do
    pure q(TYPE.sum $(← elabTYPE i x) $(← elabTYPE i y))
  | `(type_lang| $x:type_lang → $y:type_lang) => do
    pure q(TYPE.arr $(← elabTYPE i x) $(← elabTYPE i y))
  | `(type_lang| ▸ $x:type_lang) => do
    pure q(TYPE.later $(← elabTYPE i x))
  | `(type_lang| ($T:type_lang)) => elabTYPE i T
  | `(type_lang| Ω) => pure q(TYPE.prop.{i})
  | _ => throwUnsupportedSyntax

elab_rules : term
  | `(⦃ $t:type_lang ⦄) => do
    let u ← Lean.Meta.mkFreshLevelMVar
    elabTYPE u t |>.run

end ty
