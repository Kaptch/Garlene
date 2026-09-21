module

public meta import Lean
public meta import Qq
public meta import SynthDom.Syntax.Expr.Core

@[expose] public meta section

open Lean Meta Qq
open CategoryTheory
open MonoidalCategory

inductive ExprAxView (u : Level) (source : Q(EXPR.{u})) where
  | mk (type : Q(TYPE.{u})) (value : Q(𝟙_ ℐ.{u} ⟶ interp_ty $type))
      (proof : Q($source = EXPR.ax $type $value))

def exprAxView? (e : Q(EXPR.{i})) : MetaM (Option (ExprAxView i e)) := do
  let (head, args) := e.getAppFnArgs
  unless head == ``EXPR.ax && args.size == 2 do return none
  have type : Q(TYPE.{i}) := args[0]!
  have value : Q(𝟙_ ℐ.{i} ⟶ interp_ty $type) := args[1]!
  let proof : Q($e = EXPR.ax $type $value) ← withTransparency .reducible do
    have refl : Q($e = $e) := ← mkEqRefl e
    mkExpectedTypeHint refl q($e = EXPR.ax $type $value)
  return some (.mk type value proof)

inductive ExprQuoteView (u : Level) (source : Q(EXPR.{u})) where
  | mk {type : Q(TYPE.{u})} (term : Q(SYNT $type)) (offset : Q(Nat))
      (localOffset : Q(Option Nat))
      (proof : Q($source = EXPR.quote $term $offset $localOffset))

def exprQuoteView? (e : Q(EXPR.{i})) : MetaM (Option (ExprQuoteView i e)) := do
  let (head, args) := e.getAppFnArgs
  unless head == ``EXPR.quote && args.size == 4 do return none
  have type : Q(TYPE.{i}) := args[0]!
  have term : Q(SYNT.{i} $type) := args[1]!
  have offset : Q(Nat) := args[2]!
  have localOffset : Q(Option Nat) := args[3]!
  let proof : Q($e = EXPR.quote $term $offset $localOffset) ←
    withTransparency .reducible do
      have refl : Q($e = $e) := ← mkEqRefl e
      mkExpectedTypeHint refl q($e = EXPR.quote $term $offset $localOffset)
  return some (.mk term offset localOffset proof)

inductive SyntExprView (u : Level) (source : Q(EXPR.{u})) where
  | mk {type : Q(TYPE.{u})} (term : Q(SYNT $type))
      (proof : Q($source = @SYNT.expr $type $term))

def syntExprView? (e : Q(EXPR.{i})) : MetaM (Option (SyntExprView i e)) := do
  let (head, args) := e.getAppFnArgs
  let projection? : Option (Expr × Expr) ← match e with
    | .proj ``SYNT 0 term => do
      let (typeHead, typeArgs) := (← inferType term).getAppFnArgs
      if typeHead == ``SYNT && typeArgs.size == 1 then
        pure (some (typeArgs[0]!, term))
      else
        pure none
    | _ =>
      if head == ``SYNT.expr && args.size == 2 then
        pure (some (args[0]!, args[1]!))
      else
        pure none
  let some (typeExpr, termExpr) := projection? | return none
  have type : Q(TYPE.{i}) := typeExpr
  have term : Q(SYNT.{i} $type) := termExpr
  have projection : Q(EXPR.{i}) := q(@SYNT.expr $type $term)
  let projectionEq : Q($e = @SYNT.expr $type $term) ←
    if e == projection then
      mkEqRefl e
    else withTransparency .reducible do
      have refl : Q($e = $e) := ← mkEqRefl e
      mkExpectedTypeHint refl q($e = @SYNT.expr $type $term)
  return some (.mk term projectionEq)

inductive ExprBinderKind where
  | lam
  | forallE
  | existsE
  | fix
deriving BEq

structure ExprBinderView where
  kind : ExprBinderKind
  type : Expr
  body : Expr
  bodyIndex : Nat

def exprBinderView? (e : Expr) : Option ExprBinderView := do
  let head ← e.getAppFn.constName?
  let args := e.getAppArgs
  let named (kind : ExprBinderKind) : Option ExprBinderView :=
    if args.size == 3 then some { kind, type := args[1]!, body := args[2]!, bodyIndex := 2 }
    else none
  let anonymous (kind : ExprBinderKind) : Option ExprBinderView :=
    if args.size == 2 then some { kind, type := args[0]!, body := args[1]!, bodyIndex := 1 }
    else none
  if head == ``EXPR.lam then named .lam
  else if head == ``EXPR.lam' then anonymous .lam
  else if head == ``EXPR.forall then named .forallE
  else if head == ``EXPR.forall' then anonymous .forallE
  else if head == ``EXPR.exists then named .existsE
  else if head == ``EXPR.exists' then anonymous .existsE
  else if head == ``EXPR.fix then named .fix
  else if head == ``EXPR.fix' then anonymous .fix
  else none

structure ExprNodeView where
  head : Name
  fixed : Array Expr
  children : Array Expr
  childIndices : Array Nat
  structural : Bool

def ExprNodeView.rebuild (view : ExprNodeView) (source : Expr)
    (children : Array Expr) : Option Expr := do
  guard (children.size == view.childIndices.size)
  let args := (view.childIndices.zip children).foldl
    (fun args (index, child) => args.set! index child) source.getAppArgs
  pure (mkAppN source.getAppFn args)

def exprNodeView? (e : Expr) : Option ExprNodeView := do
  let head ← e.getAppFn.constName?
  let args := e.getAppArgs
  let pick (indices : List Nat) := indices.toArray.mapM (args[·]?)
  let node (fixed childIndices : List Nat) (structural := true) : Option ExprNodeView := do
    return {
      head
      fixed := ← pick fixed
      children := ← pick childIndices
      childIndices := childIndices.toArray
      structural
    }
  if head == ``EXPR.and || head == ``EXPR.or || head == ``EXPR.impl ||
      head == ``EXPR.pair then
    node [] [0, 1]
  else if head == ``EXPR.eq || head == ``EXPR.app then
    node [0] [1, 2]
  else if head == ``EXPR.embed_apply then
    node [0, 1] [2, 3]
  else if head == ``EXPR.proj then
    node [0, 2] [1]
  else if head == ``EXPR.inl || head == ``EXPR.inr then
    node [0] [1]
  else if head == ``EXPR.pure || head == ``EXPR.lift then
    node [] [0]
  else if head == ``EXPR.case then
    node [0, 1] [2, 3, 4]
  else if head == ``EXPR.annot then
    node [] [0] false
  else if head == ``EXPR.delay then
    node [] [0] false
  else if head == ``EXPR.adv then
    node [0] [1] false
  else
    none
