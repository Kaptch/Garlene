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

def adv_core : TacticM Unit := do
  let ⟨u, goal⟩ ← matchGoal "gadv"
  let { PΓ, PΨ, Γ, Ψ } := goal.context
  match goal.Φ with
  | ~q(EXPR.adv $nE $P) =>
    match ← (Lean.Meta.evalNat nE).run with
    | some 0 => throwError "gadv: `adv 0` is not a tick elimination"
    | some _ => pure ()
    | none => throwError m!"gadv: the goal's tick offset {nE} is not a literal"
    let N : Q(0 < $nE) ← mkDecideProof q(0 < $nE)
    let next ← mkFreshExprMVarQ
      q(GOAL (List.drop $nE $PΓ) (List.drop $nE $PΨ) (List.drop $nE $Γ) (List.drop $nE $Ψ) (.lift $P))
    let proof : Q(GOAL $PΓ $PΨ $Γ $Ψ (.adv $nE $P)) := q(GOAL_later_elim $nE $N $next)
    let PΓ' : Q(PP_CTX) ← whnf q(List.drop $nE $PΓ)
    let PΨ' : Q(PP_PCTX) ← whnf q(List.drop $nE $PΨ)
    let Γ' : Q(CTX.{u}) ← whnf q(List.drop $nE $Γ)
    let Ψ' : Q(PCTX.{u}) ← whnf q(List.drop $nE $Ψ)
    let shown ← mkFreshExprMVarQ q(GOAL $PΓ' $PΨ' $Γ' $Ψ' (.lift $P))
    next.mvarId!.assign shown
    goal.assign proof [shown]
  | _ => throwError "gadv: the goal is not of the form `adv n _`"

def adv_hyp_core (h : Ident) (newName : Name) : TacticM Unit := do
  let hn := h.getId
  let ⟨u, goal⟩ ← matchGoal "gadv"
  let { PΓ, PΨ, Γ, Ψ } := goal.context
  let slot ← findSlot PΨ hn "gadv" "hypothesis"
  let k := slot.frame
  if k == 0 then
    throwError m!"gadv: hypothesis {hn} lives in the current frame; it must come from an earlier \
      one (open the tick with `gnext` first)"
  have kQ : Q(Nat) := mkNatLit k
  let PΓd : Q(ElabCtx) ← whnf q(List.drop $kQ $PΓ)
  let PΨd : Q(ElabCtx) ← whnf q(List.drop $kQ $PΨ)
  let Γd : Q(CTX.{u}) ← whnf q(List.drop $kQ $Γ)
  let Ψd : Q(PCTX.{u}) ← whnf q(List.drop $kQ $Ψ)
  let cd : GuardedContext u := { PΓ := PΓd, PΨ := PΨd, Γ := Γd, Ψ := Ψd }
  let p ← cd.projectHyp "gadv" hn
  have P : Q(EXPR.{u}) := p.normalized.prop
  match P with
  | ~q(EXPR.lift (EXPR.delay $φ)) =>
    have proj : Q(GOAL (List.drop $kQ $PΓ) (List.drop $kQ $PΨ) (List.drop $kQ $Γ) (List.drop $kQ $Ψ)
      (EXPR.lift (EXPR.delay $φ))) := p.normalized.proof
    let Hk : Q(0 < $kQ) ← mkDecideProof q(0 < $kQ)
    let advG : Q(GOAL $PΓ $PΨ $Γ $Ψ (EXPR.adv $kQ (EXPR.delay $φ))) :=
      q(GOAL_later_elim $kQ $Hk $proj)
    let M : Q($kQ < ($Γ).length) ← mkDecideProof q($kQ < ($Γ).length)
    let Hφ ← mkTypedProp u q(([] : OCTX.{u}) :: $Γd) φ
    have Hφ' : Q(TYPED (([] : OCTX.{u}) :: List.drop $kQ $Γ) $φ TYPE.prop) := Hφ
    let rhs : Q(EXPR.{u}) :=
      q(weaken $φ (wk_delay (($Γ)[0]'(Nat.lt_trans $Hk $M)).length ($kQ - 1)))
    let eqβ : Q(EQ $Γ TYPE.prop (EXPR.adv $kQ (EXPR.delay $φ)) $rhs) :=
      q(EQ.beta_delay (Γ := $Γ) (e := $φ) (τ := TYPE.prop) $kQ $Hk $M $Hφ')
    let newG : Q(GOAL $PΓ $PΨ $Γ $Ψ $rhs) := q(GOAL_simplify_prop $eqβ $advG)
    let ⟨rhsN, eqN⟩ ← canon u Γ rhs
    let newGN : Q(GOAL $PΓ $PΨ $Γ $Ψ $rhsN) := q(GOAL_subst $newG (Eq.symm $eqN))
    discard <| addDerived newName { prop := rhsN, proof := newGN }
  | _ => throwError m!"gadv: hypothesis {hn} is not a ▷-proposition: {P}"

end prf
