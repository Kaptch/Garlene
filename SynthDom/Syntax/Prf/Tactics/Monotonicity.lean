module

public meta import SynthDom.Syntax.Prf.Tactics.Normalize

@[expose] public meta section

section prf

open Lean Meta Elab Tactic Qq Syntax

def monoFoldQ (u_1 : Level) : List Q(EXPR.{u_1}) → Option Q(EXPR.{u_1})
  | [] => none
  | [p] => some p
  | p :: rest =>
    match monoFoldQ u_1 rest with
    | some folded => some q(EXPR.and $p $folded)
    | none => none

def monoExtract (u_1 : Level) (PΓ PΨ : Q(ElabCtx)) (Γ : Q(CTX.{u_1})) (Ψ : Q(PCTX.{u_1}))
    (hn : Name) : TacticM (Q(EXPR.{u_1}) × Expr) := do
  let guarded : GuardedContext u_1 := { PΓ, PΨ, Γ, Ψ }
  let p ← guarded.projectHyp "mono" hn
  have prop : Q(EXPR.{u_1}) := p.normalized.prop
  match prop with
  | ~q(EXPR.lift.{u_1} (EXPR.delay.{u_1} $Pbody)) =>
    have hypN : Q(GOAL $PΓ $PΨ $Γ $Ψ (EXPR.lift.{u_1} (EXPR.delay.{u_1} $Pbody))) := p.normalized.proof
    let ⟨Pbody', eqPb⟩ ← simplify_quote q([] :: $Γ) Pbody
    let prem1 : Q(GOAL $PΓ $PΨ $Γ $Ψ (.lift (.delay $Pbody'))) := q($eqPb ▸ $hypN)
    return (Pbody', prem1)
  | _ => throwError m!"gmono: hypothesis {hn} is not a ▷-proposition"

def monoAssertStep (u_1 : Level) (PΓ PΨ : Q(ElabCtx)) (Γ : Q(CTX.{u_1})) (Ψ : Q(PCTX.{u_1}))
    (frameProps : List Q(EXPR.{u_1})) (frameNames : List Name)
    (conjE : Q(EXPR.{u_1})) (k : Nat) (nr : Nat) (takeL : Bool)
    (gn : Name) (newProp : Q(EXPR.{u_1})) : TacticM Expr := do
  let ΨfE : Q(List EXPR.{u_1}) ← mkListLit q(EXPR.{u_1}) frameProps
  let PΨfE : Q(List Name) ← mkListLit q(Name) (frameNames.map quoteName)
  have jE : Q(Nat) := (mkNatLit k)
  let ⟨M, N⟩ ← mkSlotBounds u_1 q($ΨfE :: $Ψ) q(0) jE
  let hyp : Q(GOAL ([] :: $PΓ) ($PΨfE :: $PΨ) ([] :: $Γ) ($ΨfE :: $Ψ)
      (weaken (((($ΨfE :: $Ψ))[0]'$M)[$jE]'$N) (REN.global_shift 0 REN.id)))
    ← mkProjHyp u_1 q([] :: $PΓ) q($PΨfE :: $PΨ) q([] :: $Γ) q($ΨfE :: $Ψ) q(0) jE M N
  let eq1 : Q(((($ΨfE :: $Ψ))[0]'$M)[$jE]'$N = $conjE) ← withTransparency .all <|
    mkExpectedTypeHint q(@Eq.refl EXPR.{u_1} (((($ΨfE :: $Ψ))[0]'$M)[$jE]'$N))
      q(((($ΨfE :: $Ψ))[0]'$M)[$jE]'$N = $conjE)
  let eqAll : Q(weaken (((($ΨfE :: $Ψ))[0]'$M)[$jE]'$N) (REN.global_shift 0 REN.id) = $conjE) :=
    q(Eq.trans (congrArg (fun x => weaken x (REN.global_shift 0 REN.id)) $eq1)
        (weaken_eq_self equiv_global_shift_zero_id $conjE))
  let curConj : Q(GOAL ([] :: $PΓ) ($PΨfE :: $PΨ) ([] :: $Γ) ($ΨfE :: $Ψ) $conjE) :=
    q($eqAll ▸ $hyp)

  let mut curG : Expr := curConj
  for _ in [0:nr] do
    curG ← mkAppM ``GOAL_and_elim_r #[curG]
  if takeL then
    curG ← mkAppM ``GOAL_and_elim_l #[curG]

  addDerived gn { prop := newProp, proof := curG }

def mono_core (hs gs : Array Ident) : TacticM Unit := do
    let hns : Array Name := hs.map (·.getId)
    let gns : Array Name := gs.map (·.getId)
    if hns.size != gns.size then
      throwError m!"gmono: {hns.size} hypotheses but {gns.size} new names"
    if hns.size == 0 then throwError "gmono: no hypotheses given"
    let n := hns.size
    let ⟨u_1, goal⟩ ← matchGoal "gmono"
    let { mvarId, .. } := goal
    let { PΓ, PΨ, Γ, Ψ } := goal.context
    match goal.Φ with
    | ~q(EXPR.lift (EXPR.delay $Q)) =>

      let pairs ← hns.mapM (monoExtract u_1 PΓ PΨ Γ Ψ)
      let HΓ : Q(0 < ($Γ).length) ← mkCtxPos u_1 Γ
      if n == 1 then

        have gn : Name := gns[0]!
        have Pbody' : Q(EXPR.{u_1}) := pairs[0]!.1
        have prem1 : Q(GOAL $PΓ $PΨ $Γ $Ψ (.lift (.delay $Pbody'))) := pairs[0]!.2
        let mvarId2 ← mkFreshExprMVarQ
          q(GOAL ([] :: $PΓ) (($gn :: []) :: $PΨ) ([] :: $Γ) ([$Pbody'] :: $Ψ) $Q)
        let tm : Q(GOAL $PΓ $PΨ $Γ $Ψ (.lift (.delay $Q))) :=
          q(GOAL_later_mono $HΓ $gn $prem1 $mvarId2)
        closeWith mvarId tm [mvarId2]
      else

        let comps : List Q(EXPR.{u_1}) := (pairs.map (·.1)).toList
        let some conjE := monoFoldQ u_1 comps
          | throwError "gmono: internal empty conjunction"
        let mut comb : Expr := pairs[n-1]!.2
        for k in [1:n] do
          let i := n-1-k
          comb ← mkAppM ``GOAL_later_and #[pairs[i]!.2, comb]
        let comb' : Q(GOAL $PΓ $PΨ $Γ $Ψ (EXPR.lift (EXPR.delay $conjE))) ←
          mkExpectedTypeHint comb q(GOAL $PΓ $PΨ $Γ $Ψ (EXPR.lift (EXPR.delay $conjE)))

        have anon : Name := Name.anonymous
        let mvar0 ← mkFreshExprMVarQ
          q(GOAL ([] :: $PΓ) (($anon :: []) :: $PΨ) ([] :: $Γ) ([$conjE] :: $Ψ) $Q)
        let tm : Q(GOAL $PΓ $PΨ $Γ $Ψ (.lift (.delay $Q))) :=
          q(GOAL_later_mono $HΓ $anon $comb' $mvar0)
        closeWith mvarId tm [mvar0]

        let compsArr := pairs.map (·.1)
        let mut frameProps : List Q(EXPR.{u_1}) := [conjE]
        let mut frameNames : List Name := [Name.anonymous]
        let mut curMVar : Expr := mvar0
        for k in [0:n] do
          let i := n-1-k
          curMVar ← monoAssertStep u_1 PΓ PΨ Γ Ψ frameProps frameNames conjE k
            i (i < n-1) gns[i]! compsArr[i]!
          frameProps := compsArr[i]! :: frameProps
          frameNames := gns[i]! :: frameNames
        replaceMainGoal [curMVar.mvarId!]
    | _ =>
      throwError "gmono: no matching proof-mode goal/hypothesis shape"

end prf
