module

public meta import Lean
public meta import Qq

public meta import SynthDom.Syntax.Expr.Elab
public meta import SynthDom.Syntax.Expr.Typecheck
public import SynthDom.Syntax.Prf.Syntax
public meta import SynthDom.Syntax.Prf.Core
public meta import SynthDom.Syntax.Prf.Wrappers
public meta import SynthDom.Syntax.Prf.Tactics.Simp
public meta import SynthDom.Syntax.Prf.Tactics.State
public meta import SynthDom.Syntax.Prf.Tactics.Normalize
public meta import SynthDom.Config.Attr
public meta import SynthDom.Syntax.Utils
public import SynthDom.Syntax.Prf.Tactics.Syntax

public meta section

section prf

open Lean Meta Elab PrettyPrinter Delaborator Tactic SubExpr Qq Syntax

def split_core : TacticM Unit := do
  let ⟨u, goal⟩ ← matchGoal "gsplit"
  let { mvarId, Φ, .. } := goal
  let { PΓ, PΨ, Γ, Ψ } := goal.context
  match Φ with
  | ~q(EXPR.and $P $Q) =>
    let g1 ← mkFreshExprMVarQ q(GOAL $PΓ $PΨ $Γ $Ψ $P)
    let g2 ← mkFreshExprMVarQ q(GOAL $PΓ $PΨ $Γ $Ψ $Q)
    let tm : Q(GOAL $PΓ $PΨ $Γ $Ψ (.and $P $Q)) := q(GOAL_and_intro $g1 $g2)
    closeWith mvarId tm [g1, g2]
  | _ => throwError "gsplit: the goal is not a conjunction"

def left_core : TacticM Unit := do
  let ⟨u, goal⟩ ← matchGoal "gleft"
  let { mvarId, Φ, .. } := goal
  let { PΓ, PΨ, Γ, Ψ } := goal.context
  match Φ with
  | ~q(EXPR.or $P $Q) =>
    let g ← mkFreshExprMVarQ q(GOAL $PΓ $PΨ $Γ $Ψ $P)
    let HQ ← mkTypedProp u Γ Q
    let tm : Q(GOAL $PΓ $PΨ $Γ $Ψ (.or $P $Q)) := q(GOAL_or_intro_l $HQ $g)
    closeWith mvarId tm [g]
  | _ => throwError "gleft: the goal is not a disjunction"

def right_core : TacticM Unit := do
  let ⟨u, goal⟩ ← matchGoal "gright"
  let { mvarId, Φ, .. } := goal
  let { PΓ, PΨ, Γ, Ψ } := goal.context
  match Φ with
  | ~q(EXPR.or $P $Q) =>
    let g ← mkFreshExprMVarQ q(GOAL $PΓ $PΨ $Γ $Ψ $Q)
    let HP ← mkTypedProp u Γ P
    let tm : Q(GOAL $PΓ $PΨ $Γ $Ψ (.or $P $Q)) := q(GOAL_or_intro_r $HP $g)
    closeWith mvarId tm [g]
  | _ => throwError "gright: the goal is not a disjunction"

def exfalso_core : TacticM Unit := do
  let ⟨u, goal⟩ ← matchGoal "gexfalso"
  let { mvarId, Φ, .. } := goal
  let { PΓ, PΨ, Γ, Ψ } := goal.context
  let g ← mkFreshExprMVarQ q(GOAL $PΓ $PΨ $Γ $Ψ .false)
  let HP ← mkTypedProp u Γ Φ
  let tm : Q(GOAL $PΓ $PΨ $Γ $Ψ $Φ) := q(GOAL_false_elim $HP $g)
  closeWith mvarId tm [g]

def embed_core : TacticM Unit := do
  let ⟨u, goal⟩ ← matchGoal "gembed"
  let { mvarId, Φ, .. } := goal
  let { PΓ, PΨ, Γ, Ψ } := goal.context
  match Φ with
  | ~q(EXPR.pure (EXPR.embed Prop $P)) =>
    let mvarId' ← mkFreshExprMVarQ q($P)
    let Ht ← mkTypedProp u Γ q(.pure (.embed Prop $P))
    let Hl : Q(($Γ).length = ($Ψ).length) ← mkHlen u Γ Ψ
    let tm : Q(GOAL $PΓ $PΨ $Γ $Ψ (.pure (.embed Prop $P))) := q(GOAL_pure_intro $Ht $Hl $mvarId')
    closeWith mvarId tm [mvarId']
  | _ => throwError "gembed: the goal is not an embedded Lean proposition"

def exists_core (t : TSyntax `term_lang) : TacticM Unit := do
  let ⟨u, view⟩ ← matchGoalCtx "gexists"
  let { goal, Γ0, Γs } := view
  let { PΓ, PΨ, Ψ, .. } := goal.context
  match goal.Φ with
  | ~q(EXPR.exists $nm $τ $P) =>
    let eΓ : Q(ElabCtx) := q($PΓ)
    let tE ← (elabTM u t).run eΓ
    let ⟨_, ⟨⟨_⟩, Ht⟩⟩ ← typecheck u q($Γ0 :: $Γs) tE τ
    let HP ← mkTypedProp u q(($τ :: $Γ0) :: $Γs) P
    emitSubstGoal u PΓ PΨ Γ0 Γs Ψ tE P (fun prem => do
      have prem' : Q(GOAL $PΓ $PΨ ($Γ0 :: $Γs) $Ψ
          (binds (single_subst (List.map List.length ($Γ0 :: $Γs)) $tE) $P)) := prem
      let tm : Q(GOAL $PΓ $PΨ ($Γ0 :: $Γs) $Ψ (EXPR.exists $nm $τ $P)) :=
        q(GOAL_exists_intro $HP $Ht $prem')
      goal.mvarId.assign tm)
  | _ => throwError "gexists: the goal is not an existential"

def points_core (x : Name) : TacticM Unit := do
  let ⟨u, frames⟩ ← matchGoalFrames "gpoints"
  let goal := frames.goal
  let { PΓ := PΓ0, PΨ := PΨf, Γ0, Ψ := Ψf } := frames.current
  let { PΓ := PΓs, PΨ := PΨs, Γ := Γs, Ψ := Ψs } := frames.past
  let PΓ : Q(ElabCtx) := q($PΓ0 :: $PΓs)
  let PΨ : Q(ElabCtx) := q($PΨf :: $PΨs)
  let Ψ : Q(PCTX.{u}) := q($Ψf :: $Ψs)
  let Γ : Q(CTX.{u}) := q($Γ0 :: $Γs)
  let Φ := goal.Φ
  let emit (A Body : Expr) (mk : Expr → Expr) : TacticM Unit := do
    have A : Q(Type (imax u 0)) := A
    have Body : Q(EXPR.{u}) := Body
    let familyType : Q(Prop) := q(∀ a : $A, GOAL $PΓ $PΨ $Γ $Ψ
      (binds (single_subst (List.map List.length $Γ) (EXPR.embed $A a)) $Body))
    let familyExpr ← mkFreshExprSyntheticOpaqueMVar familyType
    have family : Q($familyType) := familyExpr
    goal.mvarId.assign (mk family)
    let (aId, next) ← familyExpr.mvarId!.intro x
    replaceMainGoal [next]
    withMainContext do
      have a : Q($A) := .fvar aId
      emitSubstGoal u PΓ PΨ Γ0 Γs Ψ q((EXPR.embed $A $a : EXPR.{u})) Body
        (fun premise => next.assign premise)
  match Φ with
  | ~q(EXPR.forall $name (TYPE.embed $A) $Body) =>
    let HΦ ← mkTypedProp u q((TYPE.embed $A :: $Γ0) :: $Γs) Body
    let Hlen : Q(($Γ).length = ($Ψ).length) ← mkHlen u Γ Ψ
    emit A Body (fun family => q(GOAL_forall_intro_points $name $HΦ $Hlen
      $(show Q(∀ a : $A, GOAL $PΓ $PΨ $Γ $Ψ
        (binds (single_subst (List.map List.length $Γ) (EXPR.embed $A a)) $Body)) from family)))
  | ~q(EXPR.forall' (TYPE.embed $A) $Body) =>
    let HΦ ← mkTypedProp u q((TYPE.embed $A :: $Γ0) :: $Γs) Body
    let Hlen : Q(($Γ).length = ($Ψ).length) ← mkHlen u Γ Ψ
    emit A Body (fun family => q(GOAL_forall_intro_points' $HΦ $Hlen
      $(show Q(∀ a : $A, GOAL $PΓ $PΨ $Γ $Ψ
        (binds (single_subst (List.map List.length $Γ) (EXPR.embed $A a)) $Body)) from family)))
  | _ => throwError "gpoints: the goal is not a ∀ over an embedded type"

def rfl_core : TacticM Unit := do
  let ⟨u, goal⟩ ← matchGoal "grfl"
  let { PΓ, PΨ, Γ, Ψ } := goal.context
  match goal.Φ with
  | ~q(EXPR.eq $τ $e1 $e2) =>
    let ⟨_, ⟨⟨_⟩, He⟩⟩ ← typecheck u Γ e1 τ
    let Hl : Q(($Γ).length = ($Ψ).length) ← mkHlen u Γ Ψ
    try
      let ⟨_⟩ ← try assertDefEqQ (α := q(EXPR.{u})) e1 e2
        catch _ =>
          liftM (m := MetaM) <|
            withTransparency .all (assertDefEqQ (α := q(EXPR.{u})) e1 e2)
      let tm : Q(GOAL $PΓ $PΨ $Γ $Ψ (.eq $τ $e1 $e2)) := q(GOAL_eq_refl $He $Hl)
      goal.assign tm []
    catch _ =>
      let ⟨e1n, pn1⟩ ← normSimp u e1
      let ⟨e2n, pn2⟩ ← normSimp u e2
      let ⟨e1q, pq1⟩ ← simplify_quote Γ e1n
      let ⟨e2q, pq2⟩ ← simplify_quote Γ e2n
      let hq : Q($e2q = $e1q) ← withTransparency .all <|
        mkExpectedTypeHint q(@Eq.refl EXPR.{u} $e2q) q($e2q = $e1q)
      let h : Q($e2 = $e1) :=
        q((($pn2).trans $pq2).trans (($hq).trans ((($pn1).trans $pq1).symm)))
      let tm : Q(GOAL $PΓ $PΨ $Γ $Ψ (.eq $τ $e1 $e2)) :=
        q(GOAL_subst (GOAL_eq_refl $He $Hl) (congrArg (fun z => EXPR.eq $τ $e1 z) $h))
      goal.assign tm []
    pure ()
  | _ =>
    throwError "grfl: no matching proof-mode goal/hypothesis shape"

def trivial_core : TacticM Unit := do
  let ⟨u, goal⟩ ← matchGoal "gtrivial"
  let { PΓ, PΨ, Γ, Ψ } := goal.context
  match goal.Φ with
  | ~q(EXPR.true) =>
    let HΓ : Q(0 < ($Γ).length) ← mkCtxPos u Γ
    let Hl : Q(($Γ).length = ($Ψ).length) ← mkHlen u Γ Ψ
    let tm : Q(GOAL $PΓ $PΨ $Γ $Ψ .true) := q(GOAL_true_intro $HΓ $Hl)
    goal.assign tm []
    pure ()
  | _ =>
    throwError "gtrivial: no matching proof-mode goal/hypothesis shape"

def intro_core (h : TSyntax `ident) : TacticM Unit := do
  intro_step h h.getId

  evalTactic (← `(tactic| try simp))
  where
    intro_step (_ref : TSyntax `ident) (_n : Name) : TacticM Unit := do
      let ⟨u, goal⟩ ← matchGoal "gintro"
      let context := goal.context
      match context.PΓ, context.PΨ, context.Γ, context.Ψ, goal.Φ with
      | _, ~q($PΨ :: $PΨs), _, ~q($Ψ :: $Ψs), ~q(EXPR.impl $P $Q) =>
        let PΓ := context.PΓ
        let Γ := context.Γ
        let mvarId' ← mkFreshExprMVarQ q(GOAL $PΓ (($_n :: $PΨ) :: $PΨs) $Γ (($P :: $Ψ) :: $Ψs) $Q)
        let HQ ← mkTypedProp u Γ P
        let tm : Q(GOAL $PΓ ($PΨ :: $PΨs) $Γ ($Ψ :: $Ψs) (.impl $P $Q)) := q(GOAL_impl_intro $_n $HQ $mvarId')
        goal.assign tm [mvarId']
      | ~q($PΓ :: $PΓs), _, ~q($Γ :: $Γs), _, ~q(EXPR.forall $m $T $P) =>
        let PΨ := context.PΨ
        let Ψ := context.Ψ
        let mvarId' ← mkFreshExprMVarQ q(GOAL (($_n :: $PΓ) :: $PΓs) $PΨ (($T :: $Γ) :: $Γs) (intro_wrap $Ψ) $P)
        let tm : Q(GOAL ($PΓ :: $PΓs) $PΨ ($Γ :: $Γs) $Ψ (.forall $m $T $P)) := q(GOAL_forall_intro $_n $mvarId')
        goal.assign tm [mvarId']
      | _ =>
        throwError "gintro: no matching proof-mode goal/hypothesis shape"

def unfoldQuoted (u : Level) (Γ : Q(CTX.{u})) (declName : Name) (e : Q(EXPR.{u})) :
    TacticM (Option (Σ' (result : Q(EXPR.{u})), Q($e = $result))) := do
  unless ((e : Expr).find? (·.isConstOf declName)).isSome do return none
  let quoteContext ← Lean.Elab.Tactic.mkSimpContext (← `(tactic| simp only [quote_synt])) false
  let exposed ← (Lean.Meta.simp e quoteContext.ctx : MetaM (Lean.Meta.Simp.Result × _))
  let unfoldedStep ← Lean.Meta.unfold exposed.1.expr declName
  let unfolded ← exposed.1.mkEqTrans unfoldedStep
  let simpContext ← Lean.Elab.Tactic.mkSimpContext (← `(tactic| simp)) false
  let simplified ← (Lean.Meta.simp unfolded.expr simpContext.ctx : MetaM (Lean.Meta.Simp.Result × _))
  let result ← unfolded.mkEqTrans simplified.1
  have resultExpr : Q(EXPR.{u}) := result.expr
  let resultProof : Q($e = $resultExpr) ← result.getProof
  let ⟨value, canonical⟩ ← canon u Γ resultExpr
  if value == e then return none
  let proof : Q($e = $value) := q(($resultProof).trans $canonical)
  pure (some ⟨value, proof⟩)

def unfold_at_hyp_impl (h : Ident) (target : Ident) : TacticM Unit := do
  let declName ← withoutExporting <| realizeGlobalConstNoOverloadWithInfo h
  let hn : Name := target.getId
  let ⟨u_1, v⟩ ← matchGoalFrames "gunfold"
  let { PΨ := PΨf, Ψ := Ψh, .. } := v.current
  let { PΨ := PΨs, Ψ := Ψs, .. } := v.past
  let { PΓ, Γ, .. } := v.goal.context
  let p ← v.goal.context.projectHyp "gunfold" hn
  have PH : Q(EXPR.{u_1}) := p.normalized.prop
  have hypN : Q(GOAL $PΓ ($PΨf :: $PΨs) $Γ ($Ψh :: $Ψs) $PH) := p.normalized.proof
  let some ⟨PH', eqT⟩ ← unfoldQuoted u_1 Γ declName PH
    | throwError m!"gunfold: nothing to unfold for {declName} in hypothesis {hn}"
  let newHyp : Q(GOAL $PΓ ($PΨf :: $PΨs) $Γ ($Ψh :: $Ψs) $PH') := q($eqT ▸ $hypN)
  replaceHyp p.ref { prop := PH', proof := newHyp }

def unfold_core (h : Ident) : TacticM Unit := do
  let declName ← withoutExporting <| realizeGlobalConstNoOverloadWithInfo h
  let ⟨u, goal⟩ ← matchGoal "gunfold"
  let { PΓ, PΨ, Γ, Ψ } := goal.context
  let Φ := goal.Φ
  let some ⟨Φ', eq⟩ ← unfoldQuoted u Γ declName Φ
    | throwError m!"gunfold: {declName} does not occur in the goal"
  let next ← mkFreshExprMVarQ q(GOAL $PΓ $PΨ $Γ $Ψ $Φ')
  let proof : Q(GOAL $PΓ $PΨ $Γ $Ψ $Φ) := q(GOAL_subst $next $eq)
  goal.assign proof [next]

end prf
