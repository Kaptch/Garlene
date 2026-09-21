module

public meta import Lean
public meta import Qq

public import SynthDom.Syntax.Prf.Syntax
public meta import SynthDom.Syntax.Prf.Wrappers
public meta import SynthDom.Syntax.Prf.Tactics.Simp
public meta import SynthDom.Syntax.Utils

@[expose] public meta section

section prf

open Lean Meta Elab Tactic Qq Syntax

structure GuardedContext (u : Level) where
  PΓ : Q(ElabCtx)
  PΨ : Q(ElabCtx)
  Γ : Q(CTX.{u})
  Ψ : Q(PCTX.{u})

structure GuardedGoal (u : Level) where
  mvarId : MVarId
  context : GuardedContext u
  Φ : Q(EXPR.{u})

def matchGoal (tacName : String) : TacticM ((u : Level) × GuardedGoal u) := do
  let mvarId ← getMainGoal
  match ← inferTypeQ (← mvarId.getType) with
  | ⟨1, ~q(Prop), ~q(GOAL $PΓ $PΨ $Γ $Ψ $Φ)⟩ =>
    return ⟨u_1, { mvarId, context := { PΓ, PΨ, Γ, Ψ }, Φ }⟩
  | _ => throwError m!"{tacName}: no matching proof-mode goal/hypothesis shape"

structure GuardedCtxFrames (u : Level) where
  goal : GuardedGoal u
  Γ0 : Q(OCTX.{u})
  Γs : Q(CTX.{u})

def matchGoalCtx (tacName : String) : TacticM ((u : Level) × GuardedCtxFrames u) := do
  let ⟨u, goal⟩ ← matchGoal tacName
  match goal.context.Γ with
  | ~q($Γ0 :: $Γs) => return ⟨u, { goal, Γ0, Γs }⟩
  | _ => throwError m!"{tacName}: no matching proof-mode goal/hypothesis shape"

structure GuardedFrame (u : Level) where
  PΓ : Q(List Name)
  PΨ : Q(List Name)
  Γ0 : Q(OCTX.{u})
  Ψ : Q(POCTX.{u})

structure GuardedFrames (u : Level) where
  goal : GuardedGoal u
  current : GuardedFrame u
  past : GuardedContext u

def matchGoalFrames (tacName : String) : TacticM ((u : Level) × GuardedFrames u) := do
  let ⟨u_1, view⟩ ← matchGoalCtx tacName
  let { goal, Γ0, Γs } := view
  match goal.context.PΓ, goal.context.PΨ, goal.context.Ψ with
  | ~q($PΓ0 :: $PΓs), ~q($PΨf :: $PΨs), ~q($Ψf :: $Ψs) =>
    return ⟨u_1, {
      goal
      current := { PΓ := PΓ0, PΨ := PΨf, Γ0, Ψ := Ψf }
      past := { PΓ := PΓs, PΨ := PΨs, Γ := Γs, Ψ := Ψs }
    }⟩
  | _ => throwError m!"{tacName}: no matching proof-mode goal/hypothesis shape"

def closeWith (mvarId : MVarId) (tm : Expr) (goals : List Expr) : TacticM Unit := do
  mvarId.assign tm
  replaceMainGoal (goals.map (·.mvarId!))

def GuardedGoal.assign (goal : GuardedGoal u)
    (proof : Q(GOAL $(goal.context.PΓ) $(goal.context.PΨ)
      $(goal.context.Γ) $(goal.context.Ψ) $(goal.Φ)))
    (goals : List Expr) : TacticM Unit := do
  closeWith goal.mvarId proof goals

def mkCtxPos (u : Level) (Γ : Q(CTX.{u})) : MetaM Q(0 < ($Γ).length) :=
  mkDecideProof q(0 < ($Γ).length)

def mkHlen (u : Level) (Γ : Q(CTX.{u})) (Ψ : Q(PCTX.{u})) :
    MetaM Q(($Γ).length = ($Ψ).length) :=
  mkDecideProof q(($Γ).length = ($Ψ).length)

def mkSlotBounds (u : Level) (Ψ : Q(PCTX.{u})) (i j : Q(Nat)) :
    MetaM ((M : Q($i < ($Ψ).length)) × Q($j < (($Ψ).get (Fin.mk $i $M)).length)) := do
  let M : Q($i < ($Ψ).length) ← mkDecideProof q($i < ($Ψ).length)
  let N : Q($j < (($Ψ).get (Fin.mk $i $M)).length)
    ← mkDecideProof q($j < (($Ψ).get (Fin.mk $i $M)).length)
  pure ⟨M, N⟩

def mkTypedProp (u : Level) (Γ : Q(CTX.{u})) (P : Q(EXPR.{u})) :
    MetaM Q(TYPED $Γ $P TYPE.prop) := do
  let ⟨_, ⟨_, proof⟩⟩ ← typecheck u Γ P q(TYPE.prop)
  mkExpectedTypeHint proof q(TYPED $Γ $P TYPE.prop)

def mkProjHyp (u : Level) (PΓ PΨ : Q(ElabCtx)) (Γ : Q(CTX.{u})) (Ψ : Q(PCTX.{u}))
    (i j : Q(Nat)) (M : Q($i < ($Ψ).length))
    (N : Q($j < (($Ψ).get (Fin.mk $i $M)).length)) :
    TacticM Q(GOAL $PΓ $PΨ $Γ $Ψ (weaken ((($Ψ)[$i]'$M)[$j]'$N) (REN.global_shift $i REN.id))) := do
  let Hlen : Q(($Γ).length = ($Ψ).length) ← mkDecideProof q(($Γ).length = ($Ψ).length)
  let HiΓ : Q($i < ($Γ).length) ← mkDecideProof q($i < ($Γ).length)
  let dctx : Q(CTX.{u}) ← reduce q(($Γ).drop $i)
  let hyp : Q(EXPR.{u}) := q((($Ψ)[$i]'$M)[$j]'$N)
  let hyp0 : Q(EXPR.{u}) ← reduce hyp
  let ⟨hypN0, eqP0⟩ ← normSimpW u hyp0
  let ⟨hypN, eqP1⟩ ← normSimp u hypN0
  let eqP : Q($hyp0 = $hypN) := q(($eqP0).trans $eqP1)
  let ⟨_, ⟨_, HΦn⟩⟩ ← typecheck u dctx hypN q(TYPE.prop)
  let HΦn : Q(TYPED $dctx $hypN TYPE.prop) ← mkExpectedTypeHint HΦn q(TYPED $dctx $hypN TYPE.prop)
  let HΦ0 : Q(TYPED $dctx $hyp0 TYPE.prop) := q($eqP ▸ $HΦn)
  let HΦ : Q(TYPED (($Γ).drop $i) $hyp TYPE.prop) ←
    mkExpectedTypeHint HΦ0 q(TYPED (($Γ).drop $i) $hyp TYPE.prop)
  let Htyped : Q(TYPED $Γ (weaken ((($Ψ)[$i]'$M)[$j]'$N) (REN.global_shift $i REN.id)) TYPE.prop) :=
    q(weaken_typing $HΦ (global_shift_id_typing $Γ $i $HiΓ))
  return q(projectHypLater $M $N $Htyped $Hlen)

structure HypSlot where
  frame : Nat
  index : Nat
deriving BEq, Repr

def HypSlot.frameQ (slot : HypSlot) : Q(Nat) := Lean.mkNatLit slot.frame

def HypSlot.indexQ (slot : HypSlot) : Q(Nat) := Lean.mkNatLit slot.index

def findSlot (ctx : Q(ElabCtx)) (name : Name) (tacName kind : String) : TacticM HypSlot := do
  let ctxR ← reduce (← instantiateMVars ctx)
  let some ctxV := elabCtxOfExpr? ctxR
    | throwError m!"{tacName}: proof context did not reduce to a literal"
  let some (frame, index) := getIdx! ctxV name
    | throwError m!"{tacName}: {kind} {name} not found"
  pure { frame, index }

structure HypRef where
  name : Name
  slot : HypSlot

structure GuardedFact where
  prop : Expr
  proof : Expr

structure ProjectedHyp where
  ref : HypRef
  raw : GuardedFact
  normalized : GuardedFact

def GuardedContext.projectHyp (guarded : GuardedContext u)
    (tacName : String) (hn : Name) : TacticM ProjectedHyp := do
  let { PΓ, PΨ, Γ, Ψ } := guarded
  let slot ← findSlot PΨ hn tacName "hypothesis"
  have i : Q(Nat) := slot.frameQ
  have j : Q(Nat) := slot.indexQ
  let ⟨M, N⟩ ← mkSlotBounds u Ψ i j
  let hyp : Q(GOAL $PΓ $PΨ $Γ $Ψ
      (weaken ((($Ψ)[$i]'$M)[$j]'$N) (REN.global_shift $i REN.id)))
    ← mkProjHyp u PΓ PΨ Γ Ψ i j M N
  let elemE : Q(EXPR.{u}) ← whnf q((($Ψ)[$i]'$M)[$j]'$N)
  let eqElem : Q(((($Ψ)[$i]'$M)[$j]'$N) = $elemE) ← withTransparency .all <|
    mkExpectedTypeHint q(@Eq.refl EXPR.{u} ((($Ψ)[$i]'$M)[$j]'$N))
      q(((($Ψ)[$i]'$M)[$j]'$N) = $elemE)
  let ⟨ee, eq''⟩ ← normSimp u q(weaken $elemE (REN.global_shift $i REN.id))
  let eqFull : Q(weaken ((($Ψ)[$i]'$M)[$j]'$N) (REN.global_shift $i REN.id) = $ee) :=
    q(Eq.trans (congrArg (fun z => weaken z (REN.global_shift $i REN.id)) $eqElem) $eq'')
  let hypN : Q(GOAL $PΓ $PΨ $Γ $Ψ $ee) := q($eqFull ▸ $hyp)
  return {
    ref := { name := hn, slot }
    raw := {
      prop := q(weaken ((($Ψ)[$i]'$M)[$j]'$N) (REN.global_shift $i REN.id))
      proof := hyp
    }
    normalized := { prop := ee, proof := hypN }
  }

structure OpenedAssertion where
  premise : Expr
  continuation : Expr

def GuardedFrames.openAssertion (frames : GuardedFrames u)
    (nm : Name) (prop : Expr) : TacticM OpenedAssertion := do
  let goal := frames.goal
  let PΨ := frames.current.PΨ
  let PΨs := frames.past.PΨ
  let Ψ := frames.current.Ψ
  let Ψs := frames.past.Ψ
  let PΓ := goal.context.PΓ
  let Γ := goal.context.Γ
  let Φ := goal.Φ
  have prop' : Q(EXPR.{u}) := prop
  let side ← mkFreshExprMVarQ q(GOAL $PΓ ($PΨ :: $PΨs) $Γ ($Ψ :: $Ψs) $prop')
  let next ← mkFreshExprMVarQ
    q(GOAL $PΓ (($nm :: $PΨ) :: $PΨs) $Γ (($prop' :: $Ψ) :: $Ψs) $Φ)
  let tm : Q(GOAL $PΓ ($PΨ :: $PΨs) $Γ ($Ψ :: $Ψs) $Φ) := q(GOAL_assert $nm $side $next)
  goal.mvarId.assign tm
  return { premise := side, continuation := next }

def openAssertion (tacName : String) (nm : Name) (prop : Expr) : TacticM OpenedAssertion := do
  let ⟨_, frames⟩ ← matchGoalFrames tacName
  frames.openAssertion nm prop

def addDerived (nm : Name) (fact : GuardedFact) : TacticM Expr := do
  let opened ← openAssertion "addDerived" nm fact.prop
  opened.premise.mvarId!.assign fact.proof
  replaceMainGoal [opened.continuation.mvarId!]
  return opened.continuation

namespace ListLiteral

def spineWhnf (l : Expr) : MetaM Expr :=
  if l.isAppOfArity ``List.cons 3 || l.isAppOfArity ``List.nil 1 then pure l else whnf l

partial def drop? (l : Expr) (n : Nat) : Option Expr :=
  if n = 0 then some l
  else if l.isAppOfArity ``List.cons 3 then drop? l.getAppArgs[2]! (n - 1)
  else none

end ListLiteral

def weakenIntoCurrentFrame (e : Expr) : MetaM Expr := do
  let weakening ← mkConstWithFreshMVarLevels ``octx_wk
  mkAppM ``weaken #[e, weakening]

partial def frameDropSurgery (frame : Expr) (index : Nat) : MetaM (Option (Expr × Expr)) := do
  if frame.isAppOfArity ``List.cons 3 then
    let args := frame.getAppArgs
    if index = 0 then return some (args[1]!, args[2]!)
    let some (removed, tail) ← frameDropSurgery args[2]! (index - 1) | return none
    return some (removed, mkApp3 frame.getAppFn args[0]! args[1]! tail)
  if frame.isAppOfArity ``intro_wrap' 1 then
    let some (removed, inner) ← frameDropSurgery frame.getAppArgs[0]! index | return none
    return some (← weakenIntoCurrentFrame removed, mkApp frame.getAppFn inner)
  let exposed ← ListLiteral.spineWhnf frame
  if exposed == frame then return none else frameDropSurgery exposed index

partial def pctxDropSurgery (Ψ : Expr) (frameIndex hypIndex : Nat) :
    MetaM (Option (Expr × Expr)) := do
  if Ψ.isAppOfArity ``List.cons 3 then
    let args := Ψ.getAppArgs
    if frameIndex = 0 then
      let some (removed, frame) ← frameDropSurgery args[1]! hypIndex | return none
      return some (removed, mkApp3 Ψ.getAppFn args[0]! frame args[2]!)
    let some (removed, tail) ← pctxDropSurgery args[2]! (frameIndex - 1) hypIndex
      | return none
    return some (removed, mkApp3 Ψ.getAppFn args[0]! args[1]! tail)
  if Ψ.isAppOfArity ``intro_wrap 1 then
    let some (removed, inner) ← pctxDropSurgery Ψ.getAppArgs[0]! frameIndex hypIndex
      | return none
    let removed ← if frameIndex = 0 then weakenIntoCurrentFrame removed else pure removed
    return some (removed, mkApp Ψ.getAppFn inner)
  let exposed ← ListLiteral.spineWhnf Ψ
  if exposed == Ψ then return none else pctxDropSurgery exposed frameIndex hypIndex

def renameHypAt (goal : GuardedGoal u) (slot : HypSlot) (newName : Name) : TacticM Unit := do
  let { PΓ, PΨ, Γ, Ψ } := goal.context
  have i : Q(Nat) := slot.frameQ
  have j : Q(Nat) := slot.indexQ
  let PΨ' : Q(ElabCtx) ← reduce
    q(($PΨ).modify $i (fun frame => List.modify frame $j (Function.const _ $newName)))
  let next ← mkFreshExprMVarQ q(GOAL $PΓ $PΨ' $Γ $Ψ $(goal.Φ))
  let proof : Q(GOAL $PΓ $PΨ $Γ $Ψ $(goal.Φ)) :=
    q(swap_PP_PCTX $PΨ' $next)
  goal.assign proof [next]

def renameHyp (tacName : String) (name newName : Name) : TacticM Unit := do
  let ⟨_, goal⟩ ← matchGoal tacName
  let slot ← findSlot goal.context.PΨ name tacName "hypothesis"
  renameHypAt goal slot newName

def GuardedGoal.dropHypAt (goal : GuardedGoal u) (tacName : String)
    (slot : HypSlot) : TacticM Unit := do
  let { PΓ, PΨ, Γ, Ψ } := goal.context
  have i : Q(Nat) := slot.frameQ
  have j : Q(Nat) := slot.indexQ
  let ΨValue ← instantiateMVars Ψ
  let surgery ← pctxDropSurgery ΨValue slot.frame slot.index
  let some (propExpr, ΨExpr) := surgery
    | throwError m!"{tacName}: malformed proof-mode hypothesis context{indentExpr ΨValue}"
  have prop : Q(EXPR.{u}) := propExpr
  have Ψ' : Q(PCTX.{u}) := ΨExpr
  let PΨ' : Q(ElabCtx) ← reduce q(($PΨ).modify $i (fun frame => frame.eraseIdx $j))
  let eq : Q($Ψ = pctx_ins $Ψ' $i $j $prop) ← withTransparency .all <|
    mkExpectedTypeHint (← mkEqRefl (Ψ : Expr)) q($Ψ = pctx_ins $Ψ' $i $j $prop)
  let next ← mkFreshExprMVarQ q(GOAL $PΓ $PΨ' $Γ $Ψ' $(goal.Φ))
  let proof : Q(GOAL $PΓ $PΨ $Γ $Ψ $(goal.Φ)) :=
    q(GOAL_drop $i $j $eq $next)
  goal.assign proof [next]

def clearHyp (tacName : String) (name : Name) : TacticM Unit := do
  let ⟨_, goal⟩ ← matchGoal tacName
  let slot ← findSlot goal.context.PΨ name tacName "hypothesis"
  goal.dropHypAt tacName slot

def replaceHyp (ref : HypRef) (fact : GuardedFact) : TacticM Unit := do
  let opened ← openAssertion "replaceHyp" ref.name fact.prop
  opened.premise.mvarId!.assign fact.proof
  replaceMainGoal [opened.continuation.mvarId!]
  let ⟨_, goal⟩ ← matchGoal "replaceHyp"
  let slot := if ref.slot.frame = 0 then
    { ref.slot with index := ref.slot.index + 1 }
  else
    ref.slot
  goal.dropHypAt "replaceHyp" slot

end prf
