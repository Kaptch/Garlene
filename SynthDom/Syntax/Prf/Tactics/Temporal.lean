module

public meta import SynthDom.Syntax.Prf.Tactics.Normalize

@[expose] public meta section

section prf

open Lean Meta Elab Tactic Qq Syntax

def peelDelayEq : TacticM Unit := do
  discard <| observing? do
    let mvarId ← getMainGoal
    let goals ← mvarId.apply (← mkConstWithFreshMVarLevels ``GOAL_delay_eq)
    replaceMainGoal goals

def loeb_core (h : Ident) : TacticM Unit := do
  let n : Name := h.getId
  let ⟨u, frames⟩ ← matchGoalFrames "gloeb"
  let goal := frames.goal
  let { PΨ, Ψ, .. } := frames.current
  let { PΨ := PΨs, Ψ := Ψs, .. } := frames.past
  let { PΓ, Γ, .. } := goal.context
  let Φ := goal.Φ
  let next ← mkFreshExprMVarQ q(GOAL $PΓ (($n :: $PΨ) :: $PΨs) $Γ
    ((.lift (.delay (weaken $Φ (REN.global_shift 1 REN.id))) :: $Ψ) :: $Ψs) $Φ)
  let proof : Q(GOAL $PΓ ($PΨ :: $PΨs) $Γ ($Ψ :: $Ψs) $Φ) := q(GOAL_loeb $n $next)
  goal.assign proof [next]

def next_core : TacticM Unit := do
  let ⟨u, goal⟩ ← matchGoal "gnext"
  let { mvarId, Φ, .. } := goal
  let { PΓ, PΨ, Γ, Ψ } := goal.context
  match Φ with
  | ~q(EXPR.lift (EXPR.delay $body)) =>
    let next ← mkFreshExprMVarQ q(GOAL ([] :: $PΓ) ([] :: $PΨ) ([] :: $Γ) ([] :: $Ψ) $body)
    let positive : Q(0 < ($Γ).length) ← mkCtxPos u Γ
    let proof : Q(GOAL $PΓ $PΨ $Γ $Ψ (.lift (.delay $body))) :=
      q(GOAL_lift_intro $positive $next)
    closeWith mvarId proof [next]
  | _ => throwError "gnext: the goal is not a ▷-proposition"

end prf
