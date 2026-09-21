module

public meta import Lean

public meta import SynthDom.Syntax.Expr.Core
public import SynthDom.Syntax.Expr.Syntax
public meta import SynthDom.Syntax.Expr.Elab
public meta import SynthDom.Config.Options

public meta import SynthDom.Syntax.Ty.Delab

@[expose] public meta section

section expr

open Lean PrettyPrinter Delaborator SubExpr

open Parenthesizer in
@[category_parenthesizer term_lang]
def term_lang.parenthesizer : CategoryParenthesizer := fun prec => do
  maybeParenthesize `term_lang false (fun stx => Unhygienic.run `(term_lang| ($(⟨stx⟩):term_lang))) prec <|
    parenthesizeCategoryCore `term_lang prec

def delabArgTL (n : Nat) : DelabM (TSyntax `term_lang) :=
  withNaryArg n do
    match ← delab with
    | `(⟪$x:term_lang⟫) =>
      let ann ← annotateTermInfoTL ⟨x.raw⟩
      pure ⟨ann.raw⟩
    | _ => failure

@[delab app.EXPR.embed]
def EXPR.delabEmbed : Delab :=
  whenPPOption (·.get pp.expr.name pp.expr.defValue) do
    let e ← getExpr
    guard $ e.isAppOfArity' `EXPR.embed 2
    match ← delab (e.getArg! 0), ← delab (e.getArg! 1) with
    | `($t:term), `($t':term) =>
      let f ← getPPOption (·.get pp.ident_type.name pp.ident_type.defValue)
      if f then
        `(⟪δ($t' : $t)⟫)
      else
        `(⟪δ($t')⟫)

@[delab app.EXPR.var]
def EXPR.delabVar : Delab :=
  whenPPOption (·.get pp.expr.name pp.expr.defValue) do
    let e ← getExpr
    guard $ e.isAppOfArity' `EXPR.var 3
    let f ← getPPOption (·.get pp.var.name pp.var.defValue)
    if f then
      let some nm := (e.getArg! 0).name? | failure
      let P := mkIdent nm
      `(⟪$P:ident⟫)
    else
      match ← delab (e.getArg! 1), ← delab (e.getArg! 2) with
      | `($n:num), `($m:num) =>
        `(⟪♯($n:num, $m:num)⟫)
      | _, _ => failure

@[delab app.EXPR.lam]
def EXPR.delabLam : Delab :=
  whenPPOption (·.get pp.expr.name pp.expr.defValue) do
    let e ← getExpr
    guard $ e.isAppOfArity' `EXPR.lam 3
    let f ← getPPOption (·.get pp.var.name pp.var.defValue)
    let f' ← getPPOption (·.get pp.ident_type.name pp.ident_type.defValue)
    if f then
      let some nm := (e.getArg! 0).name? | failure
      let P := mkIdent nm
      let x ← delabArgTL 2
      match ← delab (e.getArg! 1) with
      | `(⦃$t:type_lang⦄) =>
        if f' then
          `(⟪λ $P : $t:type_lang . $x:term_lang⟫)
        else
          `(⟪λ $P . $x:term_lang⟫)
      | _ => `(⟪λ $P . $x:term_lang⟫)
    else
      let x ← delabArgTL 2
      match ← delab (e.getArg! 1) with
      | `(⦃$t:type_lang⦄) =>
        if f' then
          `(⟪λ _ : $t:type_lang . $x:term_lang⟫)
        else
          `(⟪λ _ . $x:term_lang⟫)
      | _ => `(⟪λ _ . $x:term_lang⟫)

@[delab app.EXPR.app]
def EXPR.delabApp : Delab :=
  whenPPOption (·.get pp.expr.name pp.expr.defValue) do
    let e ← getExpr
    guard $ e.isAppOfArity' `EXPR.app 3
    let x ← delabArgTL 1
    let y ← delabArgTL 2
    `(⟪$x:term_lang $y:term_lang⟫)

@[delab app.EXPR.delay]
def EXPR.delabDelay : Delab :=
  whenPPOption (·.get pp.expr.name pp.expr.defValue) do
    let e ← getExpr
    guard $ e.isAppOfArity' `EXPR.delay 1
    let t ← delabArgTL 0
    `(⟪delay $t:term_lang⟫)

@[delab app.EXPR.embed_apply]
def EXPR.delabEmbedApply : Delab :=
  whenPPOption (·.get pp.expr.name pp.expr.defValue) do
    let e ← getExpr
    let f ← getPPOption (·.get pp.ident_type.name pp.ident_type.defValue)
    guard $ e.isAppOfArity' `EXPR.embed_apply 4
    let x ← delabArgTL 2
    let y ← delabArgTL 3
    match ← delab (e.getArg! 1) with
    | `($t:term) =>
      if f then `(⟪$x:term_lang ⊙{$t:term} $y:term_lang⟫)
      else `(⟪$x:term_lang ⊙ $y:term_lang⟫)

@[delab app.EXPR.pair]
def EXPR.delabPair : Delab :=
  whenPPOption (·.get pp.expr.name pp.expr.defValue) do
    let e ← getExpr
    guard $ e.isAppOfArity' `EXPR.pair 2
    let x ← delabArgTL 0
    let y ← delabArgTL 1
    `(⟪⟨$x:term_lang, $y:term_lang⟩⟫)

@[delab app.EXPR.inl]
def EXPR.delabInl : Delab :=
  whenPPOption (·.get pp.expr.name pp.expr.defValue) do
    let e ← getExpr
    guard $ e.isAppOfArity' `EXPR.inl 2
    let x ← delabArgTL 1
    `(⟪inl $x:term_lang⟫)

@[delab app.EXPR.inr]
def EXPR.delabInr : Delab :=
  whenPPOption (·.get pp.expr.name pp.expr.defValue) do
    let e ← getExpr
    guard $ e.isAppOfArity' `EXPR.inr 2
    let x ← delabArgTL 1
    `(⟪inr $x:term_lang⟫)

@[delab app.EXPR.case]
def EXPR.delabCase : Delab :=
  whenPPOption (·.get pp.expr.name pp.expr.defValue) do
    let e ← getExpr
    guard $ e.isAppOfArity' `EXPR.case 5
    let x ← delabArgTL 2
    let f ← delabArgTL 3
    let g ← delabArgTL 4
    `(⟪case $x:term_lang $f:term_lang $g:term_lang⟫)

@[delab app.EXPR.or]
def EXPR.delabOr : Delab :=
  whenPPOption (·.get pp.expr.name pp.expr.defValue) do
    let e ← getExpr
    guard $ e.isAppOfArity' `EXPR.or 2
    let x ← delabArgTL 0
    let y ← delabArgTL 1
    `(⟪$x:term_lang ∨ $y:term_lang⟫)

@[delab app.EXPR.and]
def EXPR.delabAnd : Delab :=
  whenPPOption (·.get pp.expr.name pp.expr.defValue) do
    let e ← getExpr
    guard $ e.isAppOfArity' `EXPR.and 2
    let x ← delabArgTL 0
    let y ← delabArgTL 1
    `(⟪$x:term_lang ∧ $y:term_lang⟫)

@[delab app.EXPR.impl]
def EXPR.delabImpl : Delab :=
  whenPPOption (·.get pp.expr.name pp.expr.defValue) do
    let e ← getExpr
    guard $ e.isAppOfArity' `EXPR.impl 2
    let x ← delabArgTL 0
    let y ← delabArgTL 1
    `(⟪$x:term_lang → $y:term_lang⟫)

@[delab app.EXPR.forall]
def EXPR.delabForall : Delab :=
  whenPPOption (·.get pp.expr.name pp.expr.defValue) do
    let e ← getExpr
    guard $ e.isAppOfArity' `EXPR.forall 3
    let f ← getPPOption (·.get pp.var.name pp.var.defValue)
    let f' ← getPPOption (·.get pp.ident_type.name pp.ident_type.defValue)
    if f then
      let some nm := (e.getArg! 0).name? | failure
      let P := mkIdent nm
      let x ← delabArgTL 2
      match ← delab (e.getArg! 1) with
      | `(⦃$t:type_lang⦄) =>
        if f' then
          `(⟪∀ $P : $t:type_lang . $x:term_lang⟫)
        else
          `(⟪∀ $P . $x:term_lang⟫)
      | _ => `(⟪∀ $P . $x:term_lang⟫)
    else
      let x ← delabArgTL 2
      match ← delab (e.getArg! 1) with
      | `(⦃$t:type_lang⦄) =>
        if f' then
          `(⟪∀ _ : $t:type_lang . $x:term_lang⟫)
        else
          `(⟪∀ _ . $x:term_lang⟫)
      | _ => `(⟪∀ _ . $x:term_lang⟫)

@[delab app.EXPR.exists]
def EXPR.delabExists : Delab :=
  whenPPOption (·.get pp.expr.name pp.expr.defValue) do
    let e ← getExpr
    guard $ e.isAppOfArity' `EXPR.exists 3
    let f ← getPPOption (·.get pp.var.name pp.var.defValue)
    let f' ← getPPOption (·.get pp.ident_type.name pp.ident_type.defValue)
    if f then
      let some nm := (e.getArg! 0).name? | failure
      let P := mkIdent nm
      let x ← delabArgTL 2
      match ← delab (e.getArg! 1) with
      | `(⦃$t:type_lang⦄) =>
        if f' then
          `(⟪∃ $P : $t:type_lang . $x:term_lang⟫)
        else
          `(⟪∃ $P . $x:term_lang⟫)
      | _ => `(⟪∃ $P . $x:term_lang⟫)
    else
      let x ← delabArgTL 2
      match ← delab (e.getArg! 1) with
      | `(⦃$t:type_lang⦄) =>
        if f' then
          `(⟪∃ _ : $t:type_lang . $x:term_lang⟫)
        else
          `(⟪∃ _ . $x:term_lang⟫)
      | _ => `(⟪∃ _ . $x:term_lang⟫)

@[delab app.EXPR.lift]
def EXPR.delabLift : Delab :=
  whenPPOption (·.get pp.expr.name pp.expr.defValue) do
    let e ← getExpr
    guard $ e.isAppOfArity' `EXPR.lift 1
    let t ← delabArgTL 0
    `(⟪lift $t:term_lang⟫)

@[delab app.EXPR.pure]
def EXPR.delabPure : Delab :=
  whenPPOption (·.get pp.expr.name pp.expr.defValue) do
    let e ← getExpr
    guard $ e.isAppOfArity' `EXPR.pure 1
    let t ← delabArgTL 0
    `(⟪⌜ $t:term_lang ⌝⟫)

@[delab app.EXPR.true]
def EXPR.delabTrue : Delab :=
  whenPPOption (·.get pp.expr.name pp.expr.defValue) do
    let e ← getExpr
    guard $ e.isAppOfArity' `EXPR.true 0
    withAnnotateTermInfo `(⟪ ⊤ ⟫)

@[delab app.EXPR.false]
def EXPR.delabFalse : Delab :=
  whenPPOption (·.get pp.expr.name pp.expr.defValue) do
    let e ← getExpr
    guard $ e.isAppOfArity' `EXPR.false 0
    `(⟪ ⊥ ⟫)

@[delab app.EXPR.eq]
def EXPR.delabEq : Delab :=
  whenPPOption (·.get pp.expr.name pp.expr.defValue) do
    let e ← getExpr
    guard $ e.isAppOfArity' `EXPR.eq 3
    let x ← delabArgTL 1
    let y ← delabArgTL 2
    `(⟪$x:term_lang = $y:term_lang⟫)

@[delab app.EXPR.proj]
def EXPR.delabProj : Delab :=
  whenPPOption (·.get pp.expr.name pp.expr.defValue) do
    let e ← getExpr
    guard $ e.isAppOfArity' `EXPR.proj 3
    let x ← delabArgTL 1
    match ← delab (e.getArg! 2) with
    | `(DIR.L) => `(⟪π₁ $x:term_lang⟫)
    | `(DIR.R) => `(⟪π₂ $x:term_lang⟫)
    | _ => failure

@[delab app.EXPR.adv]
def EXPR.delabAdv : Delab :=
  whenPPOption (·.get pp.expr.name pp.expr.defValue) do
    let e ← getExpr
    guard $ e.isAppOfArity' `EXPR.adv 2
    let x ← delabArgTL 1
    match ← Lean.Meta.getNatValue? (← Lean.Meta.reduce (e.getArg! 0)) with
    | some k => `(⟪adv $(Lean.Syntax.mkNatLit k):num $x:term_lang⟫)
    | none => failure

@[delab app.EXPR.fix]
def EXPR.delabFix : Delab :=
  whenPPOption (·.get pp.expr.name pp.expr.defValue) do
    let e ← getExpr
    guard $ e.isAppOfArity' `EXPR.fix 3
    let f ← getPPOption (·.get pp.var.name pp.var.defValue)
    let f' ← getPPOption (·.get pp.ident_type.name pp.ident_type.defValue)
    if f then
      let some nm := (e.getArg! 0).name? | failure
      let P := mkIdent nm
      let x ← delabArgTL 2
      match ← delab (e.getArg! 1) with
      | `(⦃$t:type_lang⦄) =>
        if f' then
          `(⟪fix $P : $t:type_lang . $x:term_lang⟫)
        else
          `(⟪fix $P . $x:term_lang⟫)
      | _ => `(⟪fix $P . $x:term_lang⟫)
    else
      let x ← delabArgTL 2
      match ← delab (e.getArg! 1) with
      | `(⦃$t:type_lang⦄) =>
        if f' then
          `(⟪fix _ : $t:type_lang . $x:term_lang⟫)
        else
          `(⟪fix _ . $x:term_lang⟫)
      | _ => `(⟪fix _ . $x:term_lang⟫)

@[delab app.EXPR.quote]
def EXPR.delabQuote : Delab :=
  whenPPOption (·.get pp.expr.name pp.expr.defValue) do
    let e ← getExpr
    guard $ e.isAppOfArity' `EXPR.quote 4
    let x ← withNaryArg 1 do
      match ← delab with
      | `($x:term) => annotateTermInfoTL x
    `(⟪[$x:term]ₛ⟫)

@[delab app.EXPR.ax]
def EXPR.delabAx : Delab :=
  whenPPOption (·.get pp.expr.name pp.expr.defValue) do
    let e ← getExpr
    guard $ e.isAppOfArity' `EXPR.ax 2
    let t ← withNaryArg 1 do
      match ← delab with
      | `($t:term) => annotateTermInfoTL t
    `(⦃ [$t:term]ₘ ⦄)

@[delab app.EXPR.annot]
def EXPR.delabAnnot : Delab :=
  whenPPOption (·.get pp.expr.name pp.expr.defValue) do
    let e ← getExpr
    guard $ e.isAppOfArity' `EXPR.annot 2
    match ← delab (e.getArg! 0), ← delab (e.getArg! 1) with
    | `(⟪$e:term_lang⟫), `(⦃$t:type_lang⦄) => `(⟪$e:term_lang : $t:type_lang⟫)
    | _, _ => failure

@[app_unexpander SYNT]
def unexpandSYNT : Unexpander
  | `($_ $x) => `($x)
  | _ => throw ()

@[app_unexpander SYNT.mk]
def unexpandSYNTmk : Unexpander
  | `($_ $x $_) => `($x)
  | _ => throw ()

@[app_unexpander weaken]
def unexpandWeaken : Unexpander
  | `($_ ⟪$e:term_lang⟫ $_) => `(⟪$e:term_lang⟫)
  | _ => throw ()

@[app_unexpander binds]
def unexpandBinds : Unexpander
  | `($_ $_ ⟪$e:term_lang⟫) => `(⟪$e:term_lang⟫)
  | _ => throw ()

end expr
