module

public meta import Lean

public meta import SynthDom.Syntax.Ty.Core
public import SynthDom.Syntax.Ty.Syntax
public meta import SynthDom.Syntax.Ty.Elab
public meta import SynthDom.Config.Options

@[expose] public meta section

section ty

open Lean PrettyPrinter Delaborator SubExpr

open Parenthesizer in
@[category_parenthesizer type_lang]
def type_lang.parenthesizer : CategoryParenthesizer := fun prec => do
  maybeParenthesize `type_lang false (fun stx => Unhygienic.run `(type_lang| ($(⟨stx⟩):type_lang))) prec <|
    parenthesizeCategoryCore `type_lang prec

def annotateTermInfoTL (stx : Term) : Delab := do
  let stx ← annotateCurPos stx
  addDelabTermInfo (← getPos) stx (← getExpr) (explicit := false)
  pure stx

def delabChildTL (n : Nat) : DelabM (TSyntax `type_lang) := do
  withNaryArg n do
    match ← delab with
    | `(⦃ $x:type_lang ⦄) => pure x
    | t => do
      let t ← annotateTermInfoTL t
      match t with
      | `($x:ident) => `(type_lang| $x:ident)
      | _ => `(type_lang| [$t:term])

@[delab app.TYPE.embed]
def TYPE.delabEmbed : Delab :=
  whenPPOption (·.get pp.type.name pp.type.defValue) do
    let e ← getExpr
    guard $ e.isAppOfArity' `TYPE.embed 1
    match ← delab (e.getArg! 0) with
    | `($t:term) =>
      let stx ← `(⦃Δ $t⦄)
      let inf := stx.raw[1]!
      let tok := inf[1]!
      let tok ← annotateTermInfo (TSyntax.mk tok)
      let inf' := inf.setArg 1 tok
      let stx : TSyntax `term := TSyntax.mk (stx.raw.setArg 1 inf')
      Pure.pure <| TSyntax.mk stx

@[delab app.TYPE.prod]
def TYPE.delabProd : Delab :=
  whenPPOption (·.get pp.type.name pp.type.defValue) do
    let e ← getExpr
    guard $ e.isAppOfArity' `TYPE.prod 2
    match ← delabChildTL 0, ← delabChildTL 1 with
    | x, y =>
      let stx ← `(⦃$x:type_lang × $y:type_lang⦄)
      let stx ← parenthesizeCategory `type_lang stx
      let inf := stx[1]!
      let tok := inf[1]!
      let tok ← annotateTermInfo (TSyntax.mk tok)
      let inf' := inf.setArg 1 tok
      let stx : TSyntax `term := TSyntax.mk (stx.setArg 1 inf')
      Pure.pure <| TSyntax.mk stx

@[delab app.TYPE.sum]
def TYPE.delabSum : Delab :=
  whenPPOption (·.get pp.type.name pp.type.defValue) do
    let e ← getExpr
    guard $ e.isAppOfArity' `TYPE.sum 2
    match ← delabChildTL 0, ← delabChildTL 1 with
    | x, y =>
      let stx ← `(⦃$x:type_lang ⊕ $y:type_lang⦄)
      let stx ← parenthesizeCategory `type_lang stx
      let inf := stx[1]!
      let tok := inf[1]!
      let tok ← annotateTermInfo (TSyntax.mk tok)
      let inf' := inf.setArg 1 tok
      let stx : TSyntax `term := TSyntax.mk (stx.setArg 1 inf')
      Pure.pure <| TSyntax.mk stx

@[delab app.TYPE.arr]
def TYPE.delaArr : Delab :=
  whenPPOption (·.get pp.type.name pp.type.defValue) do
    let e ← getExpr
    guard $ e.isAppOfArity' `TYPE.arr 2
    match ← delabChildTL 0, ← delabChildTL 1 with
    | x, y =>
      let stx ← `(⦃$x:type_lang → $y:type_lang⦄)
      let stx ← parenthesizeCategory `type_lang stx
      let inf := stx[1]!
      let tok := inf[1]!
      let tok ← annotateTermInfo (TSyntax.mk tok)
      let inf' := inf.setArg 1 tok
      let stx : TSyntax `term := TSyntax.mk (stx.setArg 1 inf')
      Pure.pure <| TSyntax.mk stx

@[delab app.TYPE.later]
def TYPE.delabLater : Delab :=
  whenPPOption (·.get pp.type.name pp.type.defValue) do
    let e ← getExpr
    guard $ e.isAppOfArity' `TYPE.later 1
    match ← delabChildTL 0 with
    | t =>
      let stx ← `(⦃ ▸ $t:type_lang⦄)
      let inf := stx.raw[1]!
      let tok := inf[1]!
      let tok ← annotateTermInfo (TSyntax.mk tok)
      let inf' := inf.setArg 1 tok
      let stx : TSyntax `term := TSyntax.mk (stx.raw.setArg 1 inf')
      Pure.pure <| TSyntax.mk stx

@[delab app.TYPE.prop]
def TYPE.delabProp : Delab :=
  whenPPOption (·.get pp.type.name pp.type.defValue) do
    let e ← getExpr
    guard $ e.isAppOfArity' `TYPE.prop 0
    let stx ← `(⦃ Ω ⦄)
    let inf := stx.raw[1]!
    let tok := inf[1]!
    let tok ← annotateTermInfo (TSyntax.mk tok)
    let inf' := inf.setArg 1 tok
    let stx : TSyntax `term := TSyntax.mk (stx.raw.setArg 1 inf')
    Pure.pure <| TSyntax.mk stx

@[delab app.TYPE.ax]
def TYPE.delabAx : Delab :=
  whenPPOption (·.get pp.type.name pp.type.defValue) do
    let e ← getExpr
    guard $ e.isAppOfArity' `TYPE.ax 1
    let x ← withNaryArg 0 do
      match ← delab with
      | `($x:term) => annotateTermInfoTL x
    let stx ← `(⦃ [$x:term]ₘ ⦄)
    let inf := stx.raw[1]!
    let tok ← annotateTermInfo (TSyntax.mk inf[2]!)
    let inf' := inf.setArg 2 tok
    let stx : TSyntax `term := TSyntax.mk (stx.raw.setArg 1 inf')
    Pure.pure <| TSyntax.mk stx

end ty
