module

public meta import Lean
public meta import Qq

public meta import SynthDom.Syntax.Expr.View

@[expose] public meta section

section prf

open Lean Meta Elab Tactic Qq Syntax

partial def exprVarFree (e : Expr) : Bool :=
  match e.getAppFn.constName? with
  | some n =>
    if n == ``EXPR.var || n == ``EXPR.var' then false
    else if n == ``EXPR.quote then true
    else e.getAppArgs.all exprVarFree
  | none => !e.isApp

def namedWrappers : List Name :=
  [``EXPR.var, ``EXPR.lam, ``EXPR.forall, ``EXPR.exists, ``EXPR.fix, ``EXPR.annot]

def unfoldNamedWrappers (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun sub => do
    let some n := sub.getAppFn.constName? | return .continue
    unless namedWrappers.contains n do return .continue
    let some sub' ← withTransparency .all (unfoldDefinition? sub) | return .continue
    return .visit sub')

partial def stripWeaken (e : Expr) : Expr :=
  if e.isAppOfArity ``weaken 2 then stripWeaken (e.getArg! 0) else e

def allRetryAllowed (a b : Expr) : MetaM Bool := do
  let a := stripWeaken (← instantiateMVars a)
  let b := stripWeaken (← instantiateMVars b)
  let qa := a.isAppOfArity ``EXPR.quote 4
  let qb := b.isAppOfArity ``EXPR.quote 4
  if qa && qb then return a.getArg! 1 == b.getArg! 1
  return qa || qb

partial def matchPatternCore (u : Level) (nvars : Nat) (pat tgt : Q(EXPR.{u}))
    (frames : List Nat := [0]) :
    StateRefT (Array (Option Q(EXPR.{u}))) MetaM Bool := do
  let isDefEqA (a b : Expr) : MetaM Bool := do
    if ← isDefEq a b then return true
    if ← isDefEq (← unfoldNamedWrappers a) (← unfoldNamedWrappers b) then return true
    if ← allRetryAllowed a b then withTransparency .all (isDefEq a b) else return false
  let matchVar (j k : Q(Nat)) : StateRefT (Array (Option Q(EXPR.{u}))) MetaM Bool := do
    let some jv ← liftM ((Lean.Meta.evalNat j).run : MetaM (Option Nat))
      | return (← isDefEqA pat tgt)
    let some kv ← liftM ((Lean.Meta.evalNat k).run : MetaM (Option Nat))
      | return (← isDefEqA pat tgt)
    let base := frames.length - 1
    let locals := frames[jv]?.getD 0
    if kv < locals then
      let jl : Q(Nat) := mkNatLit jv
      let kl : Q(Nat) := mkNatLit kv
      return (← isDefEqA tgt (q(EXPR.var' $jl $kl) : Q(EXPR.{u})))
    else if jv == base then
      let kv' := kv - locals
      if kv' < nvars then
        if (jv != 0 || locals != 0) && !exprVarFree tgt then return false
        match (← get)[kv']! with
        | none => modify (·.set! kv' (some tgt)); return true
        | some prev => return (← isDefEqA prev tgt)
      else
        let jl : Q(Nat) := mkNatLit jv
        let klit : Q(Nat) := mkNatLit (kv - nvars)
        return (← isDefEqA tgt (q(EXPR.var' $jl $klit) : Q(EXPR.{u})))
    else
      return (← isDefEqA pat tgt)
  if let some binder1 := exprBinderView? pat then
    let some binder2 := exprBinderView? tgt | return false
    unless binder1.kind == binder2.kind do return false
    unless ← isDefEqA binder1.type binder2.type do return false
    have b1' : Q(EXPR.{u}) := binder1.body
    have b2' : Q(EXPR.{u}) := binder2.body
    return ← matchPatternCore u nvars b1' b2' ((frames.headD 0 + 1) :: frames.tail)
  match pat with
  | ~q(EXPR.var' $j $k) => matchVar j k
  | ~q(EXPR.var $_nm $j $k) => matchVar j k
  | ~q(@EXPR.quote $_ty1 $s1 $_k1 $_m1) =>
    match tgt with
    | ~q(@EXPR.quote $_ty2 $s2 $_k2 $_m2) => return (← isDefEqA s1 s2)
    | _ => return (← isDefEqA pat tgt)
  | ~q(EXPR.delay $a1) =>
    match tgt with
    | ~q(EXPR.delay $a2) => matchPatternCore u nvars a1 a2 (0 :: frames)
    | _ => return false
  | ~q(EXPR.adv $n1 $a1) =>
    match tgt with
    | ~q(EXPR.adv $n2 $a2) =>
      let some nv ← liftM ((Lean.Meta.evalNat n1).run : MetaM (Option Nat))
        | return (← isDefEqA pat tgt)
      unless ← isDefEqA n1 n2 do return false
      if nv < frames.length then
        matchPatternCore u nvars a1 a2 (frames.drop nv)
      else
        return (← isDefEqA pat tgt)
    | _ => return false
  | _ =>
    let some patView := exprNodeView? pat | return (← isDefEqA pat tgt)
    unless patView.structural do return (← isDefEqA pat tgt)
    let some targetView := exprNodeView? tgt | return false
    unless patView.head == targetView.head do return false
    unless patView.fixed.size == targetView.fixed.size do return false
    unless patView.children.size == targetView.children.size do return false
    for i in [:patView.fixed.size] do
      unless ← isDefEqA patView.fixed[i]! targetView.fixed[i]! do return false
    for i in [:patView.children.size] do
      have patChild : Q(EXPR.{u}) := patView.children[i]!
      have targetChild : Q(EXPR.{u}) := targetView.children[i]!
      unless ← matchPatternCore u nvars patChild targetChild frames do return false
    return true

structure RootPatternMatch where
  holes : Array (Option Expr)

def matchPatternRootRaw (u : Level) (nvars : Nat) (pat target : Expr) :
    MetaM (Option RootPatternMatch) := do
  have pat : Q(EXPR.{u}) := pat
  have target : Q(EXPR.{u}) := target
  let (ok, holes) ← (matchPatternCore u nvars pat target).run (Array.replicate nvars none)
  if ok then
    return some { holes := holes.map (fun hole => hole.map (fun e => (e : Expr))) }
  return none

def matchPatternRoot (u : Level) (nvars : Nat) (pat target : Expr) :
    MetaM (Option RootPatternMatch) := withoutModifyingState do
  let some result ← matchPatternRootRaw u nvars pat target | return none
  let holes ← result.holes.mapM fun
    | some value => do
      let value ← instantiateMVars value
      pure (some value)
    | none => pure none
  return some { holes }

def exprSearchChildren (e : Expr) : Array Expr :=
  (exprNodeView? e).map (fun view => view.children) |>.getD #[]

structure PatternMatch where
  arguments : Array Expr
  occurrence : Expr

def completeArguments? (root : RootPatternMatch) : Option (Array Expr) :=
  if root.holes.all (·.isSome) then
    some <| (root.holes.toList.reverse.map fun hole => hole.get!).toArray
  else
    none

partial def findMatchIn (u : Level) (nvars : Nat) (pat target : Expr) :
    MetaM (Option PatternMatch) := do
  let rootResult ← withoutModifyingState do
    let some rootMatch ← matchPatternRootRaw u nvars pat target | return none
    let some arguments := completeArguments? rootMatch | return none
    let arguments ← arguments.mapM instantiateMVars
    let occurrence ← instantiateMVars target
    return some { arguments, occurrence }
  if let some result := rootResult then return some result
  for child in exprSearchChildren target do
    if let some result ← findMatchIn u nvars pat child then
      return some result
  return none

end prf
