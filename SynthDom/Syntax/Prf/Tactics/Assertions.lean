module

public meta import SynthDom.Syntax.Prf.Tactics.Normalize
public import SynthDom.Syntax.Prf.Tactics.Syntax

@[expose] public meta section

section prf

open Lean Meta Elab Tactic Qq Syntax

partial def matchHoleAgainst (pat goal : Expr) : TacticM Bool := do
  if ← withoutModifyingState (withAssignableSyntheticOpaque (isDefEq pat goal)) then
    discard <| withAssignableSyntheticOpaque (isDefEq pat goal)
    return true
  match goal with
  | .app .. =>
    for arg in goal.getAppArgs do
      if ← matchHoleAgainst pat arg then
        return true
    return false
  | _ => return false

partial def resolveAssertHoles (u : Level) (Γ : Q(CTX.{u})) (e Φ : Q(EXPR.{u})) :
    TacticM Q(EXPR.{u}) := do
  let e : Q(EXPR.{u}) ← instantiateMVars e
  let isGHole (m : MVarId) : TacticM Bool := return (← m.getDecl).userName == `ghole
  let gholes ← (← getMVars e).filterM isGHole
  if gholes.isEmpty then return e
  let sides : Array Q(EXPR.{u}) ← (do
    match e with
    | ~q(EXPR.eq $τ0 $l $r) => pure #[l, r]
    | _ => pure #[e] : TacticM _)
  for side in sides do
    let side : Q(EXPR.{u}) ← instantiateMVars side
    if ← (← getMVars side).anyM isGHole then
      unless ← matchHoleAgainst side Φ do
        throwError m!"gassert: could not match the hole pattern {side} against any goal subterm"
  for m in gholes do
    unless ← m.isAssigned do
      throwError m!"gassert: unresolved `_` holes in {← instantiateMVars (e : Expr)}"
  let e' : Q(EXPR.{u}) ← instantiateMVars e
  match e' with
  | ~q(EXPR.eq $τ $l $r) =>
    if (← instantiateMVars (τ : Expr)).hasExprMVar then
      try
        let ⟨τ', _⟩ ← infer u Γ l
        discard <| isDefEq (τ : Expr) (τ' : Expr)
      catch _ => pure ()
  | _ => pure ()
  instantiateMVars e'

def assert_core (h : Ident) (e : TSyntax `term_lang) : TacticM Unit := do
  let n : Name := h.getId
  let ⟨u_1, v⟩ ← matchGoalFrames "gassert"
  let { PΓ, Γ, .. } := v.goal.context
  let Φ := v.goal.Φ
  let eΓ : Q(ElabCtx) := q($PΓ)
  let e ← (elabTM u_1 e).run eΓ
  let e : Q(EXPR.{u_1}) ← resolveAssertHoles u_1 Γ e Φ
  let opened ← v.openAssertion n e
  replaceMainGoal [opened.premise.mvarId!, opened.continuation.mvarId!]

def poseWeakenEq (u : Level) (Γ : Q(CTX.{u})) (ΦL wprop : Q(EXPR.{u})) :
    TacticM Q($ΦL = $wprop) := do
  try
    let ⟨wN, eqW⟩ ← canon u Γ wprop
    let ⟨lN, eqL⟩ ← canon u Γ ΦL
    let ⟨_⟩ ← assertDefEqQ (α := q(EXPR.{u})) wN lN
    let eqW' : Q($wprop = $lN) ← mkExpectedTypeHint eqW q($wprop = $lN)
    mkExpectedTypeHint q(($eqL).trans ($eqW').symm) q($ΦL = $wprop)
  catch _ =>
    withTransparency .all <| mkExpectedTypeHint q(@Eq.refl EXPR.{u} $ΦL) q($ΦL = $wprop)

def pose_core (t : TSyntax `term) (h : Ident) : TacticM Unit := do
  let name : Name := h.getId
  let ⟨u, frames⟩ ← matchGoalFrames "gpose"
  let goal := frames.goal
  let { PΨ := PΨf, Γ0, Ψ := Ψf, .. } := frames.current
  let { PΨ := PΨs, Γ := Γs, Ψ := Ψs, .. } := frames.past
  let PΓ := goal.context.PΓ
  let Φ := goal.Φ
  let term ← Lean.Elab.Tactic.elabTerm t none
  let term ← instantiateMVars term
  let goalType ← instantiateMVars (← goal.mvarId.getType)
  let termType ← whnfR (← instantiateMVars (← inferType term))
  match goalType.getAppFn, termType.getAppFn with
  | .const ``GOAL (goalLevel :: _), .const ``GOAL (termLevel :: _) =>
    discard <| isLevelDefEq termLevel goalLevel
  | _, _ => pure ()
  let term ← instantiateMVars term
  match ← inferTypeQ termType with
  | ⟨1, ~q(Prop), ~q(GOAL.{u} $pgt $ppt ([[]] : CTX.{u}) ([[]] : PCTX.{u}) $ΦL)⟩ =>
    let source : Q(GOAL.{u} $pgt $ppt ([[]] : CTX.{u}) ([[]] : PCTX.{u}) $ΦL) := term
    let weakened : Q(EXPR.{u}) := q(_root_.weaken $ΦL (local_weaken_list ($Γ0).length REN.id))
    let lengthProof ← mkFreshExprMVarQ q(($Γ0 :: $Γs).length = ($Ψf :: $Ψs).length)
    let imported : Q(GOAL $PΓ ($PΨf :: $PΨs) ($Γ0 :: $Γs) ($Ψf :: $Ψs) $weakened) :=
      q(GOAL_import $source $lengthProof)
    let transport ← poseWeakenEq u q($Γ0 :: $Γs) ΦL weakened
    let premise : Q(GOAL $PΓ ($PΨf :: $PΨs) ($Γ0 :: $Γs) ($Ψf :: $Ψs) $ΦL) :=
      q(GOAL_subst $imported $transport)
    let continuation ← mkFreshExprMVarQ
      q(GOAL $PΓ (($name :: $PΨf) :: $PΨs) ($Γ0 :: $Γs) (($ΦL :: $Ψf) :: $Ψs) $Φ)
    let proof : Q(GOAL $PΓ ($PΨf :: $PΨs) ($Γ0 :: $Γs) ($Ψf :: $Ψs) $Φ) :=
      q(GOAL_assert $name $premise $continuation)
    goal.mvarId.assign proof
    unless ← lengthProof.mvarId!.isAssigned do
      try lengthProof.mvarId!.refl
      catch _ => throwError "gpose: the context and the hypothesis stack have different depths"
    replaceMainGoal [continuation.mvarId!]
  | _ => throwError "gpose: term does not prove a GOAL statement"

end prf
