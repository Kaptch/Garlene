module

public meta import Lean
public meta import Qq

public meta import SynthDom.Syntax.Prf.Tactics.Normalize

@[expose] public meta section

section prf

open Lean Meta Elab Tactic Qq Syntax

inductive RwDir where
  | ltr
  | rtl
deriving BEq, Repr

def typecheckReducing (u : Level) (Γ e τ : Expr) : TacticM Unit := do
  try
    discard <| typecheck u Γ e τ
  catch _ =>
    let er ← withTransparency .all (reduce e)
    discard <| typecheck u Γ er τ

def substMotiveEq (direction : RwDir) (u : Level)
    (lens motive motiveRaw motiveEq e target : Expr) : TacticM Expr := do
  have lens' : Q(List Nat) := lens
  have motive' : Q(EXPR.{u}) := motive
  have motiveRaw' : Q(EXPR.{u}) := motiveRaw
  have motiveEq' : Q($motiveRaw' = $motive') := motiveEq
  have e' : Q(EXPR.{u}) := e
  have target' : Q(EXPR.{u}) := target
  match direction with
  | .ltr =>
    let raw : Q(binds (single_subst $lens' $e') $motiveRaw' = $target') ←
      withTransparency .all <| mkExpectedTypeHint
        q(@Eq.refl EXPR.{u} (binds (single_subst $lens' $e') $motiveRaw'))
        q(binds (single_subst $lens' $e') $motiveRaw' = $target')
    let congruence : Q(binds (single_subst $lens' $e') $motive'
        = binds (single_subst $lens' $e') $motiveRaw') ← mkExpectedTypeHint
      q(@congrArg EXPR.{u} EXPR.{u} $motive' $motiveRaw'
        (fun m => binds (single_subst $lens' $e') m) (Eq.symm $motiveEq'))
      q(binds (single_subst $lens' $e') $motive' = binds (single_subst $lens' $e') $motiveRaw')
    pure q(Eq.trans $congruence $raw)
  | .rtl =>
    let raw : Q($target' = binds (single_subst $lens' $e') $motiveRaw') ←
      withTransparency .all <| mkExpectedTypeHint
        q(@Eq.refl EXPR.{u} $target')
        q($target' = binds (single_subst $lens' $e') $motiveRaw')
    let congruence : Q(binds (single_subst $lens' $e') $motiveRaw'
        = binds (single_subst $lens' $e') $motive') ← mkExpectedTypeHint
      q(@congrArg EXPR.{u} EXPR.{u} $motiveRaw' $motive'
        (fun m => binds (single_subst $lens' $e') m) $motiveEq')
      q(binds (single_subst $lens' $e') $motiveRaw' = binds (single_subst $lens' $e') $motive')
    pure q(Eq.trans $raw $congruence)

structure GuardedEquation where
  ty : Expr
  lhs : Expr
  rhs : Expr
  proof : Expr

structure MotiveTransport (u : Level) where
  motiveRaw : Q(EXPR.{u})
  equation : GuardedEquation
  source : GuardedFact
  target : Q(EXPR.{u})

def MotiveTransport.run (spec : MotiveTransport u) (view : GuardedCtxFrames u) :
    TacticM Expr := do
  let { goal, Γ0 := D, Γs := D' } := view
  let { PΓ, PΨ, Ψ, .. } := goal.context
  let motiveRaw := spec.motiveRaw
  have τa : Q(TYPE.{u}) := spec.equation.ty
  have lhs : Q(EXPR.{u}) := spec.equation.lhs
  have rhs : Q(EXPR.{u}) := spec.equation.rhs
  have source : Q(EXPR.{u}) := spec.source.prop
  let target := spec.target
  let ⟨motive, motiveEq⟩ ← normSimp u motiveRaw
  let ⟨_, ⟨⟨_⟩, Hmotive⟩⟩ ← typecheck u q(($τa :: $D) :: $D') motive q(TYPE.prop)
  let lens : Q(List Nat) := q(List.map List.length ($D :: $D'))
  let ⟨_, ⟨⟨_⟩, Hlhs⟩⟩ ← typecheck u q($D :: $D') lhs τa
  let ⟨_, ⟨⟨_⟩, Hrhs⟩⟩ ← typecheck u q($D :: $D') rhs τa
  have equation : Q(GOAL $PΓ $PΨ ($D :: $D') $Ψ (EXPR.eq $τa $lhs $rhs)) := spec.equation.proof
  have base : Q(GOAL $PΓ $PΨ ($D :: $D') $Ψ $source) := spec.source.proof
  let sourceEq' ← substMotiveEq .ltr u lens motive motiveRaw motiveEq lhs source
  have sourceEq : Q(binds (single_subst $lens $lhs) $motive = $source) := sourceEq'
  let plugged : Q(GOAL $PΓ $PΨ ($D :: $D') $Ψ (binds (single_subst $lens $lhs) $motive)) :=
    q(GOAL_subst $base $sourceEq)
  let stepped : Q(GOAL $PΓ $PΨ ($D :: $D') $Ψ (binds (single_subst $lens $rhs) $motive)) :=
    q(GOAL_eq_elim $Hmotive $Hlhs $Hrhs $equation $plugged)
  let targetEq' ← substMotiveEq .rtl u lens motive motiveRaw motiveEq rhs target
  have targetEq : Q($target = binds (single_subst $lens $rhs) $motive) := targetEq'
  let result : Q(GOAL $PΓ $PΨ ($D :: $D') $Ψ $target) := q(GOAL_subst $stepped $targetEq)
  pure result

structure EquationNormalization where
  prop : Expr
  equation? : Option GuardedEquation

def normalizeEquation (u : Level) (context : GuardedContext u)
    (fact : GuardedFact) : TacticM EquationNormalization := do
  let { PΓ, PΨ, Γ, Ψ } := context
  let prop0 := fact.prop
  let proof0 := fact.proof
  have prop0 : Q(EXPR.{u}) := prop0
  have proof0 : Q(GOAL $PΓ $PΨ $Γ $Ψ $prop0) := proof0
  let ⟨prop1, eq1⟩ ← simplify_quote Γ prop0
  let ⟨prop, eq2⟩ ← normSimp u prop1
  let eq : Q($prop0 = $prop) := q(($eq1).trans $eq2)
  let proof : Q(GOAL $PΓ $PΨ $Γ $Ψ $prop) := q($eq ▸ $proof0)
  match prop with
  | ~q(EXPR.eq $τ $e1 $e2) =>
    typecheckReducing u Γ e1 τ
    pure { prop, equation? := some { ty := τ, lhs := e1, rhs := e2, proof } }
  | _ =>
    pure { prop, equation? := none }

def GuardedEquation.symm (equation : GuardedEquation) (tacName : String) (u : Level)
    (context : GuardedContext u) : TacticM GuardedEquation := do
  let { PΓ, PΨ, Γ, Ψ } := context
  let ~q($Γ0 :: $Γs) := Γ
    | throwError "{tacName}: no matching proof-mode goal/hypothesis shape"
  have τ : Q(TYPE.{u}) := equation.ty
  have e1 : Q(EXPR.{u}) := equation.lhs
  have e2 : Q(EXPR.{u}) := equation.rhs
  let equationProof : Q(GOAL $PΓ $PΨ ($Γ0 :: $Γs) $Ψ (EXPR.eq $τ $e1 $e2)) ←
    pure equation.proof
  let proof : Q(GOAL $PΓ $PΨ ($Γ0 :: $Γs) $Ψ (EXPR.eq $τ $e2 $e1)) :=
    q(GOAL_eq_symm $equationProof)
  return { ty := equation.ty, lhs := equation.rhs, rhs := equation.lhs, proof }

def injection_core (h g : Ident) : TacticM Unit := do
  let hn : Name := h.getId
  let gn : Name := g.getId
  let ⟨u_1, v⟩ ← matchGoalFrames "ginjection"
  let goal := v.goal
  let { PΨ, Ψ, .. } := v.current
  let { PΨ := PΨs, Ψ := Ψs, .. } := v.past
  let { PΓ, Γ, .. } := goal.context
  let Φ := goal.Φ
  let p ← v.goal.context.projectHyp "ginjection" hn
  have prop : Q(EXPR.{u_1}) := p.normalized.prop
  let assertComp (prop' : Q(EXPR.{u_1})) (comp : Expr) : TacticM Unit := do
    discard <| addDerived gn { prop := prop', proof := comp }
  let closeDisjoint (proof : Expr) : TacticM Unit := do
    let falseG ← mkAppM ``GOAL_inl_inr_disj #[proof]
    let HΦ ← mkTypedProp u_1 Γ Φ
    closeWith goal.mvarId (← mkAppM ``GOAL_false_elim #[HΦ, falseG]) []
  match prop with
  | ~q(EXPR.eq.{u_1} (TYPE.sum.{u_1} $A $B) (EXPR.inl.{u_1} $B2 $a) (EXPR.inl.{u_1} $B3 $a')) =>
    let hypAB : Q(GOAL $PΓ ($PΨ :: $PΨs) $Γ ($Ψ :: $Ψs)
        (EXPR.eq.{u_1} (TYPE.sum.{u_1} $A $B) (EXPR.inl.{u_1} $B2 $a) (EXPR.inl.{u_1} $B3 $a'))) ←
      pure p.normalized.proof
    let comp ← mkAppM ``GOAL_inl_inj #[hypAB]
    assertComp q(EXPR.eq.{u_1} $A $a $a') comp
  | ~q(EXPR.eq.{u_1} (TYPE.sum.{u_1} $A $B) (EXPR.inr.{u_1} $A2 $b) (EXPR.inr.{u_1} $A3 $b')) =>
    let hypAB : Q(GOAL $PΓ ($PΨ :: $PΨs) $Γ ($Ψ :: $Ψs)
        (EXPR.eq.{u_1} (TYPE.sum.{u_1} $A $B) (EXPR.inr.{u_1} $A2 $b) (EXPR.inr.{u_1} $A3 $b'))) ←
      pure p.normalized.proof
    let comp ← mkAppM ``GOAL_inr_inj #[hypAB]
    assertComp q(EXPR.eq.{u_1} $B $b $b') comp
  | ~q(EXPR.eq.{u_1} (TYPE.sum.{u_1} $A $B) (EXPR.inl.{u_1} $B2 $a) (EXPR.inr.{u_1} $A2 $b)) =>
    let hypAB : Q(GOAL $PΓ ($PΨ :: $PΨs) $Γ ($Ψ :: $Ψs)
        (EXPR.eq.{u_1} (TYPE.sum.{u_1} $A $B) (EXPR.inl.{u_1} $B2 $a) (EXPR.inr.{u_1} $A2 $b))) ←
      pure p.normalized.proof
    closeDisjoint hypAB
  | ~q(EXPR.eq.{u_1} (TYPE.sum.{u_1} $A $B) (EXPR.inr.{u_1} $A2 $b) (EXPR.inl.{u_1} $B2 $a)) =>
    let proof : Q(GOAL $PΓ ($PΨ :: $PΨs) $Γ ($Ψ :: $Ψs)
        (EXPR.eq.{u_1} (TYPE.sum.{u_1} $A $B) (EXPR.inr.{u_1} $A2 $b) (EXPR.inl.{u_1} $B2 $a))) ←
      pure p.normalized.proof
    let equation : GuardedEquation := {
      ty := q(TYPE.sum $A $B)
      lhs := q(EXPR.inr $A2 $b)
      rhs := q(EXPR.inl $B2 $a)
      proof
    }
    closeDisjoint (← equation.symm "ginjection" u_1 goal.context).proof
  | _ => throwError m!"ginjection: hypothesis {hn} is not a sum-constructor equation"

end prf
