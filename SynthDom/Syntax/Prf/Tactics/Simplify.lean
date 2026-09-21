module

public meta import SynthDom.Syntax.Prf.Tactics.Normalize

@[expose] public meta section

section prf

open Lean Meta Elab Tactic Qq Syntax

def transformGoal (tacName : String) (transform : (u : Level) → EqRecurse u)
    (mustChange := false) : TacticM Bool := do
  let ⟨u, goal⟩ ← matchGoal tacName
  let { PΓ, PΨ, Γ, Ψ } := goal.context
  let Φ := goal.Φ
  let ⟨quoted, quoteEq⟩ ← simplify_quote Γ Φ
  let ⟨normalized, normalizedEq⟩ ← normSimp u quoted
  let ⟨transformed, transformEq⟩ ← transform u Γ PΓ q(TYPE.prop) normalized
  if mustChange &&
      (← instantiateMVars (transformed : Expr)) == (← instantiateMVars (normalized : Expr)) then
    throwError m!"{tacName}: the goal contains no fixpoint to unfold"
  let ⟨result, resultEq⟩ ← normSimp u transformed
  if (← instantiateMVars (result : Expr)) == (← instantiateMVars (Φ : Expr)) then
    return false
  have eq : Q(EQ $Γ TYPE.prop $Φ $result) := q(by
    rw [<-$resultEq]
    exact EQ.subst_l $transformEq (Eq.symm (Eq.trans $quoteEq $normalizedEq))
  )
  let next ← mkFreshExprMVarQ q(GOAL $PΓ $PΨ $Γ $Ψ $result)
  let proof : Q(GOAL.{u} $PΓ $PΨ $Γ $Ψ $Φ) := q(by
    exact GOAL_simplify_prop (EQ.sym' $eq) $next
  )
  goal.assign proof [next]
  return true

def simpStep : TacticM Bool :=
  transformGoal "gsimpl" (fun _ => simplify)

def simpl_core : TacticM Unit := do
  while (← simpStep) do
    pure ()

def fix_core : TacticM Unit := do
  discard <| transformGoal "gfix" (fun _ => simplify_fix) true
  simpl_core

end prf
