module

public meta import Lean
public meta import Qq

public meta import SynthDom.Syntax.Prf.Tactics.Simp
public meta import SynthDom.Syntax.Prf.Tactics.Normalize
public meta import SynthDom.Syntax.Prf.Tactics.Equality
public meta import SynthDom.Syntax.Prf.Tactics.RuleCursor
public meta import SynthDom.Syntax.Prf.Tactics.Matcher

@[expose] public meta section

section prf

open Lean Meta Elab PrettyPrinter Delaborator Tactic SubExpr Qq Syntax

partial def buildMotive (u : Level) (pat repl : Q(EXPR.{u})) (e : Q(EXPR.{u}))
    (depth : Nat := 0) (ρ : Q(REN) := q(octx_wk)) :
    MetaM (Q(EXPR.{u}) × Q(EXPR.{u}) × Bool) := do

  let e : Q(EXPR.{u}) ← instantiateMVars e
  let unchanged : Q(EXPR.{u}) × Q(EXPR.{u}) × Bool := (q(weaken $e $ρ), e, false)
  if e.getAppFn.isMVar then
    return unchanged
  if ← isDefEq e pat then
    return (q(EXPR.var' $depth 0), repl, true)
  else
    match e with
    | ~q(EXPR.delay $a) => do
        let (am, ac, r) ← buildMotive u pat repl a (depth + 1) q(REN.global_lift $ρ)
        if r then return (q(EXPR.delay $am), q(EXPR.delay $ac), true)
        else return unchanged
    | ~q(EXPR.adv $n $a) => do
        match ← Lean.Meta.getNatValue? n with
        | some nv =>
            if nv ≤ depth then do
              let (am, ac, r) ← buildMotive u pat repl a (depth - nv) q(cut_ren $ρ $n)
              if r then return (q(EXPR.adv (offset_ren $ρ $n) $am), q(EXPR.adv $n $ac), true)
              else return unchanged
            else return unchanged
        | none => return unchanged
    | _ =>
      let some view := exprNodeView? e | return unchanged
      unless view.structural do return unchanged
      let mut motiveChildren : Array Expr := #[]
      let mut cleanChildren : Array Expr := #[]
      let mut replaced := false
      for child in view.children do
        have childQ : Q(EXPR.{u}) := child
        let (motive, clean, changed) ← buildMotive u pat repl childQ depth ρ
        motiveChildren := motiveChildren.push motive
        cleanChildren := cleanChildren.push clean
        replaced := replaced || changed
      let some motive := view.rebuild e motiveChildren | return unchanged
      let some clean := view.rebuild e cleanChildren | return unchanged
      have motiveQ : Q(EXPR.{u}) := motive
      have cleanQ : Q(EXPR.{u}) := clean
      return (motiveQ, cleanQ, replaced)

partial def buildDiffMotive (u : Level) (l r : Q(EXPR.{u}))
    (depth : Nat := 0) (ρ : Q(REN) := q(octx_wk)) :
    StateRefT (Option (Q(EXPR.{u}) × Q(EXPR.{u}))) MetaM (Option Q(EXPR.{u})) := do
  if ← isDefEq l r then
    return some q(weaken $l $ρ)

  let mismatch : StateRefT (Option (Q(EXPR.{u}) × Q(EXPR.{u}))) MetaM (Option Q(EXPR.{u})) := do
    unless depth == 0 do return none
    match ← get with
    | none => set (some (l, r)); return some q(EXPR.var' 0 0)
    | some (a, b) =>
      if (← isDefEq l a) && (← isDefEq r b) then return some q(EXPR.var' 0 0)
      else return none

  let tick (a1 a2 : Q(EXPR.{u})) (d : Nat) (ρ' : Q(REN)) (k : Q(EXPR.{u}) → Q(EXPR.{u})) :
      StateRefT (Option (Q(EXPR.{u}) × Q(EXPR.{u}))) MetaM (Option Q(EXPR.{u})) := do
    let saved ← get
    match ← buildDiffMotive u a1 a2 d ρ' with
    | some m => return some (k m)
    | none => set saved; mismatch
  match l, r with
  | ~q(EXPR.delay $a1), ~q(EXPR.delay $a2) =>
    tick a1 a2 (depth + 1) q(REN.global_lift $ρ) (fun x => q(EXPR.delay $x))
  | ~q(EXPR.adv $n1 $a1), ~q(EXPR.adv $n2 $a2) =>
    if ← isDefEq n1 n2 then
      match ← Lean.Meta.getNatValue? n1 with
      | some nv =>
        if nv ≤ depth then
          tick a1 a2 (depth - nv) q(cut_ren $ρ $n1) (fun x => q(EXPR.adv (offset_ren $ρ $n1) $x))
        else mismatch
      | none => mismatch
    else mismatch
  | _, _ =>
    let some leftView := exprNodeView? l | mismatch
    let some rightView := exprNodeView? r | mismatch
    unless leftView.structural && rightView.structural do return ← mismatch
    unless leftView.head == rightView.head do return ← mismatch
    unless leftView.fixed.size == rightView.fixed.size do return ← mismatch
    unless leftView.children.size == rightView.children.size do return ← mismatch
    for i in [:leftView.fixed.size] do
      unless ← isDefEq leftView.fixed[i]! rightView.fixed[i]! do return ← mismatch
    let mut children : Array Expr := #[]
    for i in [:leftView.children.size] do
      have leftChild : Q(EXPR.{u}) := leftView.children[i]!
      have rightChild : Q(EXPR.{u}) := rightView.children[i]!
      let some child ← buildDiffMotive u leftChild rightChild depth ρ | return none
      children := children.push child
    let some result := leftView.rebuild l children | return none
    have resultQ : Q(EXPR.{u}) := result
    return some resultQ

def rewriteGoalCore (pe : GuardedEquation) : TacticM Unit := do
  let ⟨u, view⟩ ← matchGoalCtx "grewrite"
  let { goal, Γ0 := D, Γs := D' } := view
  let { PΓ, PΨ, Ψ, .. } := goal.context
  let Φ := goal.Φ
  have e1 : Q(EXPR.{u}) := pe.lhs
  have e2 : Q(EXPR.{u}) := pe.rhs
  let (motiveRaw, cleanGoal, didRep) ← buildMotive u e2 e1 Φ 0 q(octx_wk)
  unless didRep do
    throwError m!"grewrite: could not find {e2} in the goal"
  have cleanGoal' : Q(EXPR.{u}) := cleanGoal
  let ⟨cgN, ecg⟩ ← canon u q($D :: $D') cleanGoal'
  let next ← mkFreshExprMVarQ q(GOAL $PΓ $PΨ ($D :: $D') $Ψ $cgN)
  let base : Q(GOAL $PΓ $PΨ ($D :: $D') $Ψ $cleanGoal') := q(GOAL_subst $next $ecg)
  let proof ← MotiveTransport.run (u := u)
    { motiveRaw, equation := pe, source := { prop := cleanGoal', proof := base }, target := Φ } view
  goal.assign proof [next]

def rewriteHypCore (pe : GuardedEquation) (hn : Name) :
    TacticM Unit := do
  let ⟨u, view⟩ ← matchGoalCtx "grewrite"
  let { goal, Γ0 := D, Γs := D' } := view
  let { PΓ, PΨ, Ψ, .. } := goal.context
  have e1 : Q(EXPR.{u}) := pe.lhs
  have e2 : Q(EXPR.{u}) := pe.rhs
  let guarded := goal.context
  let pH ← guarded.projectHyp "grewrite" hn
  have PH : Q(EXPR.{u}) := pH.normalized.prop
  have hypNH : Q(GOAL $PΓ $PΨ ($D :: $D') $Ψ $PH) := pH.normalized.proof
  let (motiveRaw, cleanH, didRep) ← buildMotive u e1 e2 PH 0 q(octx_wk)
  unless didRep do
    throwError m!"grewrite: could not find {e1} in hypothesis {hn}"
  have cleanH' : Q(EXPR.{u}) := cleanH
  let rewritten ← MotiveTransport.run (u := u)
    { motiveRaw, equation := pe, source := { prop := PH, proof := hypNH }, target := cleanH' } view
  have final : Q(GOAL $PΓ $PΨ ($D :: $D') $Ψ $cleanH') := rewritten
  let ⟨chN, ech⟩ ← canon u q($D :: $D') cleanH'
  let finalN : Q(GOAL $PΓ $PΨ ($D :: $D') $Ψ $chN) := q(GOAL_subst $final (Eq.symm $ech))
  replaceHyp pH.ref { prop := chN, proof := finalN }

def eqSides (u : Level) (e : Expr) : TacticM (Option (Expr × Expr)) := do
  have eQ : Q(EXPR.{u}) := e
  match eQ with
  | ~q(EXPR.eq $_τ $l $r) => pure (some ((l : Expr), (r : Expr)))
  | _ => pure none

def grwInferAndSpecialize (u : Level) (guarded : GuardedContext u)
    (dir : RwDir) (ΦE : Expr) (tgt : Option Name)
    (cursor0 : RuleCursor) : TacticM (RuleCursor × Option Expr) := do
  let Γ := guarded.Γ
  let .forallE _ _ _ ← viewRuleHead u cursor0.prop | return (cursor0, none)
  let scanned ← scanRulePrefix u cursor0.prop .raw
  let nvars := scanned.forallCount
  let body := scanned.conclusion
  have bodyQ : Q(EXPR.{u}) := body

  let ⟨bodyN, _⟩ ← canon u Γ bodyQ
  let some (l, r) ← eqSides u bodyN
    | throwError m!"grewrite: the lemma does not reduce to an equation: {bodyN}"
  let pat := if dir == RwDir.ltr then l else r
  let target : Expr ← (do
    if let some hn := tgt then
      let pH ← guarded.projectHyp "grewrite" hn
      pure pH.normalized.prop
    else
      pure ΦE)
  let matchRes ← findMatchIn u nvars pat target
  let some result := matchRes
    | throwError m!"grewrite: cannot infer the instantiation by matching {pat} against \
        the target — supply the arguments explicitly"
  let mut cursor := cursor0
  for e in result.arguments do
    cursor ← cursor.consumeImplications guarded

    have eQ : Q(EXPR.{u}) := e
    let ⟨eN, _⟩ ← canon u Γ eQ
    cursor ← cursor.specializeForMatching "grewrite" guarded eN
  return (cursor, some result.occurrence)

def grwLemmaCore (dir : RwDir) (sn : Name)
    (args : Array (TSyntax `term_lang)) (tgt : Option Name) : TacticM Unit := do
  let ⟨u, view⟩ ← matchGoalCtx "grewrite"
  let { goal, Γ0 := D, Γs := D' } := view
  let { PΓ, PΨ, Ψ, .. } := goal.context
  let Φ := goal.Φ
  let ruleCtx := goal.context
  let p ← ruleCtx.projectHyp "grewrite" sn
  let mut cursor := RuleCursor.ofNormalizedProjected p
  for a in args do
    cursor ← cursor.consumeImplications ruleCtx
    let e ← (elabTM u a).run PΓ
    cursor ← cursor.specializeForMatching "grewrite" ruleCtx e
  cursor ← cursor.consumeImplications ruleCtx
  let (cursorI, matched?) ← grwInferAndSpecialize u ruleCtx dir (Φ : Expr) tgt cursor
  cursor := cursorI
  cursor ← cursor.consumeImplications ruleCtx
  let normalized ← normalizeEquation u ruleCtx { prop := cursor.prop, proof := cursor.proof }
  let some equation := normalized.equation?
    | throwError m!"grewrite: the specialized lemma is not an equation: {normalized.prop}"
  if let some hn := tgt then
    let pe ← if dir == RwDir.rtl then equation.symm "grewrite" u ruleCtx else pure equation
    let pe ← if let some occurrence := matched? then do
      have τe : Q(TYPE.{u}) := pe.ty
      have lhs : Q(EXPR.{u}) := occurrence
      have rhs : Q(EXPR.{u}) := pe.rhs
      let proof ← withTransparency .all <| mkExpectedTypeHint pe.proof
        q(GOAL $PΓ $PΨ ($D :: $D') $Ψ (EXPR.eq $τe $lhs $rhs))
      pure { pe with lhs := occurrence, proof }
    else pure pe
    rewriteHypCore pe hn
  else
    let pe ← if dir == RwDir.ltr then equation.symm "grewrite" u ruleCtx else pure equation
    rewriteGoalCore pe
  unless cursor.premises.isEmpty do
    setGoals (cursor.premises.toList ++ (← getGoals))

def congr_core : TacticM Unit := do
  let ⟨u, view⟩ ← matchGoalCtx "gcong"
  let { goal, Γ0 := D, Γs := D' } := view
  let { PΓ, PΨ, Ψ, .. } := goal.context
  let Φ := goal.Φ
  match Φ with
  | ~q(EXPR.eq $τ $L $R) =>
    let (motiveR?, pair?) ← (buildDiffMotive u L R).run none
    let some motiveR := motiveR?
      | throwError m!"gcong: the two sides do not share a constructor skeleton with a \
          single consistent differing subterm"
    let some (a, b) := pair?
      | throwError m!"gcong: the two sides are already definitionally equal — use `grfl`"

    if (motiveR : Expr).isAppOf ``EXPR.var' then
      throwError m!"gcong: the two sides have no shared head to peel — they differ at the \
        root (for `delay _ = delay _` use `gmono`/`gnext` to enter the tick first)"
    let ⟨τa, _⟩ ← infer u q($D :: $D') a
    let ⟨_, ⟨⟨_⟩, HL⟩⟩ ← typecheck u q($D :: $D') L τ
    let Hlen : Q(($D :: $D').length = ($Ψ).length) ← mkHlen u q($D :: $D') Ψ
    let reflL : Q(GOAL $PΓ $PΨ ($D :: $D') $Ψ (EXPR.eq $τ $L $L)) := q(GOAL_eq_refl $HL $Hlen)
    let sub ← mkFreshExprMVarQ q(GOAL $PΓ $PΨ ($D :: $D') $Ψ (EXPR.eq $τa $a $b))
    let equation : GuardedEquation := { ty := τa, lhs := a, rhs := b, proof := sub }
    let proof ← MotiveTransport.run (u := u)
      { motiveRaw := q(EXPR.eq $τ (weaken $L octx_wk) $motiveR)
        equation
        source := { prop := q(EXPR.eq $τ $L $L), proof := reflL }
        target := q(EXPR.eq $τ $L $R) } view
    goal.assign proof [sub]
  | _ => throwError "gcong: the goal is not an equation"

end prf
