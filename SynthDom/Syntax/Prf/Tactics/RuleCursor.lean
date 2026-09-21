module

public meta import Lean
public meta import Qq

public meta import SynthDom.Syntax.Prf.Tactics.Normalize

@[expose] public meta section

section prf

open Lean Meta Elab Tactic Qq

structure RuleCursor extends GuardedFact where
  premises : Array MVarId := #[]

inductive RuleHead where
  | forallE (name type body : Expr)
  | implication (premise conclusion : Expr)
  | conclusion (value : Expr)

def viewRuleHead (u : Level) (e : Expr) : TacticM RuleHead := do
  have e : Q(EXPR.{u}) := e
  match e with
  | ~q(EXPR.forall $name $type $body) =>
    pure <| .forallE name type body
  | ~q(EXPR.impl $premise $conclusion) =>
    pure <| .implication premise conclusion
  | _ =>
    pure <| .conclusion e

def RuleCursor.ofNormalizedProjected (hyp : ProjectedHyp) : RuleCursor :=
  { prop := hyp.normalized.prop, proof := hyp.normalized.proof }

def RuleCursor.ofRawProjected (hyp : ProjectedHyp) : RuleCursor :=
  { prop := hyp.raw.prop, proof := hyp.raw.proof }

def RuleCursor.specializeForStorage (cursor : RuleCursor) (tacName : String)
    (guarded : GuardedContext u) (e : Expr) : TacticM RuleCursor := withAssignableSyntheticOpaque do
  let { PΓ, PΨ := PΨA, Γ, Ψ := ΨA } := guarded
  have prop : Q(EXPR.{u}) := cursor.prop
  match Γ with
  | ~q($Γ0 :: $Γs) =>
    have hyp : Q(GOAL $PΓ $PΨA ($Γ0 :: $Γs) $ΨA $prop) := cursor.proof
    have e : Q(EXPR.{u}) := e
    let ⟨ee'', eq''⟩ ← normSimp u prop
    let (nE, τE, pE) ← match ← viewRuleHead u ee'' with
      | .forallE n τ P => pure (n, τ, P)
      | _ => throwError "{tacName}: the hypothesis is not a ∀-proposition: {ee''}"
    have n : Q(Name) := nE
    have τ : Q(TYPE.{u}) := τE
    have P : Q(EXPR.{u}) := pE
    let e' : Q(EXPR.{u}) ← (do
      let foldedOk ← withoutModifyingState (do
        try let _ ← typecheck u Γ e τ; pure true
        catch _ => pure false)
      if foldedOk then pure e else reduce e)
    let ⟨_⟩ ← assertDefEqQ (α := q(EXPR.{u})) e' e
    let ⟨τ', ⟨⟨_⟩, HT⟩⟩ ← typecheck u Γ e' τ
    let τi : Q(TYPE.{u}) ← instantiateMVars τ'
    let Pi : Q(EXPR.{u}) ← instantiateMVars P
    let Γ0i : Q(OCTX.{u}) ← instantiateMVars Γ0
    let Γsi : Q(CTX.{u}) ← instantiateMVars Γs
    let ⟨Pq, PqEq⟩ ← canon u q(($τi :: $Γ0i) :: $Γsi) Pi
    let ⟨_, ⟨⟨_⟩, HPn⟩⟩ ← typecheck u q(($τi :: $Γ0i) :: $Γsi) Pq q(TYPE.prop)
    let HPraw : Q(TYPED (($τi :: $Γ0i) :: $Γsi) $Pi TYPE.prop) :=
      q(($PqEq).symm ▸ $HPn)
    let HP : Q(TYPED (($τ :: $Γ0) :: $Γs) $P TYPE.prop) ←
      mkExpectedTypeHint HPraw q(TYPED (($τ :: $Γ0) :: $Γs) $P TYPE.prop)
    have hyp'' : Q(GOAL.{u} $PΓ $PΨA $Γ $ΨA $ee'') := q(by
      rw [<-$eq'']
      exact $hyp)
    let hypForall : Q(GOAL.{u} $PΓ $PΨA $Γ $ΨA (EXPR.forall $n $τ $P)) ←
      withTransparency .all <| mkExpectedTypeHint hyp''
        q(GOAL.{u} $PΓ $PΨA $Γ $ΨA (EXPR.forall $n $τ $P))
    let EQ' ← singleSubstConsEq u PΓ Γ e
    let hyp' : Q(GOAL.{u} $PΓ $PΨA $Γ $ΨA
        (binds (SSUBST.cons (SSUBST.id' $PΓ) $e) $P)) := q(by
      rw [←$EQ']
      apply GOAL_forall_elim (nm := $n) (τ := $τ) $HP $hypForall $HT)
    let hasQuote := (Pi.find? (fun s => s.isConstOf ``EXPR.quote)).isSome
    let bindsP : Q(EXPR.{u}) := q(binds (SSUBST.cons (SSUBST.id' $PΓ) $e) $P)
    let (propStore, hypStore) ←
      if hasQuote then do
        let ⟨result, eq⟩ ← canon u Γ bindsP
        let proof : Q(GOAL.{u} $PΓ $PΨA $Γ $ΨA $result) :=
          q(GOAL_subst $hyp' (Eq.symm $eq))
        pure ((result : Expr), (proof : Expr))
      else
        pure ((bindsP : Expr), (hyp' : Expr))
    pure { cursor with prop := propStore, proof := hypStore }
  | _ => throwError "{tacName}: hypothesis is not a GOAL over a non-empty context"

def RuleCursor.specializeForMatching (cursor : RuleCursor) (tacName : String)
    (context : GuardedContext u) (e : Expr) : TacticM RuleCursor := do
  let { PΓ, PΨ, Γ, Ψ } := context
  let cursor ← cursor.specializeForStorage tacName context e
  have prop : Q(EXPR.{u}) := cursor.prop
  have proof : Q(GOAL $PΓ $PΨ $Γ $Ψ $prop) := cursor.proof
  let ⟨normalized, eq⟩ ← canon u Γ prop
  have normalizedProof : Q(GOAL $PΓ $PΨ $Γ $Ψ $normalized) :=
    q(GOAL_subst $proof (Eq.symm $eq))
  let result? ← observing? do
    let ⟨reduced, reduction⟩ ← simplify Γ PΓ q(TYPE.prop) normalized
    let ⟨result, resultEq⟩ ← canon u Γ reduced
    have resultProof : Q(GOAL $PΓ $PΨ $Γ $Ψ $result) :=
      q(GOAL_subst (GOAL_simplify_prop $reduction $normalizedProof) (Eq.symm $resultEq))
    pure { cursor with prop := result, proof := resultProof }
  pure <| result?.getD { cursor with prop := normalized, proof := normalizedProof }

def RuleCursor.consumeImplication (cursor : RuleCursor) (context : GuardedContext u) :
    TacticM (Option RuleCursor) := do
  let { PΓ, PΨ, Γ, Ψ } := context
  match ← viewRuleHead u cursor.prop with
  | .implication premise conclusion =>
    have premise : Q(EXPR.{u}) := premise
    have conclusion : Q(EXPR.{u}) := conclusion
    let side ← mkFreshExprMVarQ q(GOAL $PΓ $PΨ $Γ $Ψ $premise)
    have proof : Q(GOAL $PΓ $PΨ $Γ $Ψ (EXPR.impl $premise $conclusion)) := cursor.proof
    let next : Q(GOAL $PΓ $PΨ $Γ $Ψ $conclusion) := q(GOAL_impl_elim $proof $side)
    pure <| some
      { prop := conclusion, proof := next, premises := cursor.premises.push side.mvarId! }
  | _ => pure none

partial def RuleCursor.consumeImplications (cursor : RuleCursor) (context : GuardedContext u) :
    TacticM RuleCursor := do
  let some next ← cursor.consumeImplication context
    | return cursor
  next.consumeImplications context

structure RulePrefix where
  forallCount : Nat
  length : Nat
  conclusion : Expr

inductive PrefixNormalization where
  | raw
  | normSimpEach

partial def scanRulePrefix (u : Level) (e : Expr) (normalization : PrefixNormalization)
    (forallCount : Nat := 0) (length : Nat := 0) : TacticM RulePrefix := do
  have current : Q(EXPR.{u}) := e
  let current ← match normalization with
    | .normSimpEach =>
      let ⟨normalized, _⟩ ← normSimp u current
      pure normalized
    | .raw => pure current
  match ← viewRuleHead u current with
  | .forallE _ _ body =>
    scanRulePrefix u body normalization (forallCount + 1) (length + 1)
  | .implication _ conclusion =>
    scanRulePrefix u conclusion normalization forallCount (length + 1)
  | .conclusion value => pure { forallCount, length, conclusion := value }

end prf
