module

public meta import SynthDom.Syntax.Prf.Tactics.Normalize
public meta import SynthDom.Syntax.Prf.Tactics.RuleCursor
public meta import SynthDom.Syntax.Prf.Tactics.Matcher

@[expose] public meta section

section prf

open Lean Meta Elab Tactic Qq Syntax

partial def containsFalseConjunct (e : Expr) : MetaM Bool := do
  let e ← whnf (← instantiateMVars e)
  if e.isConstOf ``False then return true
  if e.isAppOf ``And then
    let args := e.getAppArgs
    if args.size == 2 then
      return (← containsFalseConjunct args[0]!) || (← containsFalseConjunct args[1]!)
  return false

def exact_core (h : TSyntax `ident) : TacticM Unit := do
  let n : Name := h.getId
  let ⟨u, goal⟩ ← matchGoal "gexact"
  let { PΓ, PΨ, Γ, Ψ } := goal.context
  let Φ := goal.Φ
  let projected ← goal.context.projectHyp "gexact" n
  have hprop : Q(EXPR.{u}) := projected.normalized.prop
  have hypN : Q(GOAL $PΓ $PΨ $Γ $Ψ $hprop) := projected.normalized.proof
  let ⟨ee, eq⟩ ← simplify Γ PΓ q(TYPE.prop) hprop
  let ⟨ee', eq'⟩ ← simplify Γ PΓ q(TYPE.prop) Φ
  let residual : Q($ee = $ee') ← mkFreshExprMVarQ q($ee = $ee')
  let proof : Q(GOAL $PΓ $PΨ $Γ $Ψ $Φ) := q(by
    apply (GOAL_simplify_prop (EQ.sym' $eq'))
    rw [<-$residual]
    apply (GOAL_simplify_prop $eq)
    exact $hypN
  )
  closeWith goal.mvarId proof [residual]
  let current :: rest ← getGoals | throwError "gexact: no goals"
  setGoals [current]
  gResidualSimp
  let remaining ← getGoals
  let mut mismatch := false
  for residual in remaining do
    if ← containsFalseConjunct (← residual.getType) then mismatch := true
  if mismatch then
    throwError "gexact: hypothesis {n} does not match the goal"
  setGoals (remaining ++ rest)

def assumption_core : TacticM Unit := focus do
  let ⟨_, goal⟩ ← matchGoal "gassumption"
  let pψ ← reduce goal.context.PΨ
  let some ctx := elabCtxOfExpr? pψ
    | throwError "gassumption: proof context did not reduce to a literal"
  let names := ctx.flatten.filter (!·.isAnonymous)
  for nm in names do
    let result ← observing? do
      exact_core (mkIdent nm)
      unless (← getGoals).isEmpty do throwError "gassumption: mismatch"
    if result.isSome then return
  throwError "gassumption: no hypothesis closes the goal"

def apply_core (hname : TSyntax `ident)
    (wargs : Array (TSyntax `term_lang)) : TacticM Unit := do
  let n : Name := hname.getId.eraseMacroScopes
  let ⟨u, view⟩ ← matchGoalCtx "gapply"
  let { goal, .. } := view
  let PΓ := goal.context.PΓ
  let Φ := goal.Φ
  let ruleCtx := goal.context
  let p ← ruleCtx.projectHyp "gapply" hname.getId
  have projRed : Q(EXPR.{u}) := p.normalized.prop
  let scanned ← scanRulePrefix u projRed .normSimpEach
  let defeqGoal (p : Q(EXPR.{u})) : TacticM Bool := do
    if ← isDefEq p Φ then pure true
    else (withTransparency .all (isDefEq p Φ) : MetaM Bool)
  let inferArgs : TacticM (Array Q(EXPR.{u})) := do
    let nvars := scanned.forallCount
    if nvars == 0 then return #[]
    have conclusion : Q(EXPR.{u}) := scanned.conclusion
    let some rootMatch ← matchPatternRoot u nvars conclusion Φ
      | throwError m!"gapply: cannot infer the instantiation of {n} by matching its conclusion \
          against the goal — supply it with `gapply {n} …`\n  conclusion: {conclusion}\n  goal: {Φ}"
    let some inferred := completeArguments? rootMatch
      | let missing := (List.range nvars).find? fun index =>
          rootMatch.holes[nvars - 1 - index]!.isNone
        throwError m!"gapply: the goal does not determine ∀-argument #{missing.getD 0 + 1} of {n} — \
          supply it with `gapply {n} …`"
    return inferred
  let isForallHead := match ← viewRuleHead u projRed with
    | .forallE _ _ _ => true
    | _ => false
  let argExprs : Array Q(EXPR.{u}) ←
    if wargs.isEmpty then
      if isForallHead then inferArgs else pure #[]
    else
      wargs.mapM (fun term => (elabTM u term).run PΓ)
  let mut cursor := RuleCursor.ofNormalizedProjected p
  let mut argumentIndex := 0
  let mut done := false
  let mut fuel := scanned.length + 1
  while !done && fuel > 0 do
    fuel := fuel - 1
    have prop : Q(EXPR.{u}) := cursor.prop
    if ← defeqGoal prop then
      done := true
    else
      match ← viewRuleHead u cursor.prop with
      | .forallE _ _ _ =>
        unless argumentIndex < argExprs.size do
          throwError m!"gapply: {n}'s conclusion is still ∀-headed ({prop}); provide an instantiation with `gapply {n} …`"
        let argument : Q(EXPR.{u}) := argExprs[argumentIndex]!
        let next ← try cursor.specializeForMatching "gapply" ruleCtx argument
          catch ex => throwError m!"gapply: argument #{argumentIndex + 1}: cannot instantiate {prop}\n{ex.toMessageData}"
        cursor := next
        argumentIndex := argumentIndex + 1
        if cursor.prop == prop then
          throwError "gapply: internal rule cursor made no progress while consuming a ∀-binder"
      | .implication _ _ =>
        let some next ← cursor.consumeImplication ruleCtx
          | throwError "gapply: internal implication cursor mismatch"
        cursor := next
        if cursor.prop == prop then
          throwError "gapply: internal rule cursor made no progress while consuming an implication"
      | .conclusion _ =>
        throwError m!"gapply: {n}'s conclusion {prop} does not match the goal {Φ}"
  unless done do
    throwError "gapply: internal rule cursor exhausted its prefix bound"
  unless argumentIndex == argExprs.size do
    throwError m!"gapply: too many `with`-arguments for {n} — {argExprs.size} given, {argumentIndex} consumed"
  let proof ← withTransparency .all <| mkExpectedTypeHint cursor.proof (← goal.mvarId.getType)
  goal.mvarId.assign proof
  replaceMainGoal cursor.premises.toList

def specialize_core (hI : Ident) (ts : Array (TSyntax `term_lang)) (asName? : Option Name) :
    TacticM Unit := withAssignableSyntheticOpaque $ do
  if ts.isEmpty then throwError "gspecialize: at least one argument required"
  let ⟨u, view⟩ ← matchGoalCtx "gspecialize"
  let { goal, .. } := view
  let { PΓ, PΨ, Γ, Ψ } := goal.context
  let sourceName := hI.getId
  let resultName := asName?.getD sourceName
  let guarded := goal.context
  let projected ← guarded.projectHyp "gspecialize" sourceName
  let mut cursor := RuleCursor.ofRawProjected projected
  for t in ts do
    let e ← (elabTM u t).run PΓ
    cursor ← cursor.specializeForStorage "gspecialize" guarded e
  have prop : Q(EXPR.{u}) := cursor.prop
  have proof : Q(GOAL.{u} $PΓ $PΨ $Γ $Ψ $prop) := cursor.proof
  if asName?.isSome then
    discard <| addDerived resultName { prop, proof }
  else
    replaceHyp projected.ref { prop, proof }
  gSubstSimp

end prf
