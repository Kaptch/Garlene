module

public meta import Lean
public meta import Qq

public import SynthDom.Syntax.Prf.Syntax
public meta import SynthDom.Syntax.Prf.Core
public meta import SynthDom.Syntax.Prf.Wrappers
public meta import SynthDom.Syntax.Expr.Delab
public meta import SynthDom.Config.Attr
public meta import SynthDom.Syntax.Utils

@[expose] public meta section

section prf

open Lean Meta PrettyPrinter Delaborator SubExpr Qq Syntax

def delabHypRow (nm : Name) : DelabM (TSyntax `local_hyp) := do
  let nmStx ← annotateTermInfoTL ⟨(mkIdent nm).raw⟩
  match ← delab with
  | `(⦃$t:type_lang⦄) =>
    let a : TSyntax `type_lang := ⟨(← annotateTermInfoTL ⟨t.raw⟩).raw⟩
    `(local_hyp| $nmStx:term : $a:type_lang)
  | `(⟪$x:term_lang⟫) =>
    let a : TSyntax `term_lang := ⟨(← annotateTermInfoTL ⟨x.raw⟩).raw⟩
    `(local_hyp| $nmStx:term : $a:term_lang)
  | d => `(local_hyp| $nmStx:term : $d:term)

def withReducedExpr (action : DelabM α) : DelabM α := do
  let subExpr ← readThe SubExpr
  let reduced ← reduce (← instantiateMVars subExpr.expr)
  guard (reduced != subExpr.expr)
  withTheReader SubExpr (fun current => { current with expr := reduced }) action

partial def delabHypsInFrame (names : List Name) : DelabM (Array (TSyntax `local_hyp)) := do
  let e ← getExpr
  if e.isAppOf ``intro_wrap' then
    withNaryArg 0 (delabHypsInFrame names)
  else if e.isAppOf ``List.cons then
    match names with
    | nm :: restNames =>
      if nm.isAnonymous then
        withNaryArg 2 (delabHypsInFrame restNames)
      else
        let row ← withNaryArg 1 (delabHypRow nm)
        let rest ← withNaryArg 2 (delabHypsInFrame restNames)
        pure (rest.push row)
    | [] => failure
  else if e.isAppOf ``List.nil && names.isEmpty then
    pure #[]
  else
    withReducedExpr (delabHypsInFrame names)

partial def delabHypFrames (names : ElabCtx) : DelabM (Array (Array (TSyntax `local_hyp))) := do
  let e ← getExpr
  if e.isAppOf ``intro_wrap then
    withNaryArg 0 (delabHypFrames names)
  else if e.isAppOf ``List.cons then
    match names with
    | names :: rest =>
      let hd ← withNaryArg 1 (delabHypsInFrame names)
      let tl ← withNaryArg 2 (delabHypFrames rest)
      pure (#[hd] ++ tl)
    | [] => failure
  else if e.isAppOf ``List.nil && names.isEmpty then
    pure #[]
  else
    withReducedExpr (delabHypFrames names)

@[delab app.GOAL]
def delabGOAL : Delab := do
  unless (← getPPOption (·.get pp.proof.name pp.proof.defValue)) do failure
  let expr ← instantiateMVars <| ← getExpr
  guard $ expr.isAppOfArity `GOAL 5
  let ctx := expr.getArg! 0
  let pctx := expr.getArg! 1
  let some varNames := elabCtxOfExpr? (← reduce ctx) | failure
  let some propNames := elabCtxOfExpr? (← reduce pctx) | failure
  let varFrames ← withNaryArg 2 (delabHypFrames varNames)
  let propFrames ← withNaryArg 3 (delabHypFrames propNames)

  let nFrames := max varFrames.size propFrames.size
  let mut lines : Array (TSyntax `ctx_line) := #[]
  for k in [0 : nFrames] do
    let i := nFrames - 1 - k
    if k > 0 then
      lines := lines.push (← `(ctx_line| ─────▷─────))
    for h in ((varFrames[i]?).getD #[]) ++ ((propFrames[i]?).getD #[]) do
      lines := lines.push (← `(ctx_line| $h:local_hyp))
  let t ← delabArgTL 4
  `(Guarded: $lines* ⊢ $t:term_lang)

end prf
