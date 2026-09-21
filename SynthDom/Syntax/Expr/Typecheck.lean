module

public meta import Lean
public meta import Qq

public meta import SynthDom.Syntax.Expr.Core
public meta import SynthDom.Syntax.Expr.View
public import SynthDom.Syntax.Expr.Syntax
public meta import SynthDom.Config.Options
public meta import SynthDom.Config.Attr
public meta import SynthDom.Syntax.Utils

public meta import SynthDom.Syntax.Ty.Elab
public meta import SynthDom.Syntax.Expr.Elab
public meta import SynthDom.Syntax.Prf.WeakenCore

@[expose] public meta section

section expr

open Lean Elab Meta PrettyPrinter Delaborator SubExpr Qq

open CategoryTheory
open CartesianMonoidalCategory
open MonoidalCategory

inductive QuoteTowerView (u : Level) (source : Q(EXPR.{u})) where
  | mk {type : Q(TYPE.{u})} (term : Q(SYNT $type)) (offset : Q(Nat))
      (localOffset : Q(Option Nat))
      (proof : Q($source = EXPR.quote $term $offset $localOffset))

partial def quoteTowerView? (e : Q(EXPR.{i})) : MetaM (Option (QuoteTowerView i e)) := do
  if let some (.mk term offset localOffset proof) ← exprQuoteView? e then
    return some (.mk term offset localOffset proof)
  if let some (.mk term projectionEq) ← syntExprView? e then
    return some (.mk term q(0) q(none)
      q(($projectionEq).trans (quote_eq_expr $term 0 none).symm))
  match e with
  | ~q(weaken $inner $σ) =>
    match ← quoteTowerView? inner with
    | some (.mk term offset localOffset proof) =>
      return some (.mk term offset localOffset
        q((congrArg (fun source => weaken source $σ) $proof).trans
          (weaken_quote $term $offset $localOffset $σ)))
    | none => return none
  | _ => return none

partial def ctxUnconsReduce (i : Level) (ctx : Q(CTX.{i})) :
    MetaM (Σ' (D : Q(OCTX.{i})) (D' : Q(CTX.{i})), Q($ctx = $D :: $D')) := do
  let ctx' : Q(CTX.{i}) ← reduce ctx
  match ctx' with
  | ~q($D :: $D') => do
    let ⟨_⟩ ← assertDefEqQ (α := q(CTX.{i})) ctx q($D :: $D')
    pure ⟨D, D', q(rfl)⟩
  | _ => throwError m!"context is neither [] nor a cons after reduction: {ctx}"

mutual
  partial def typecheck (i : Level)
    (ctx : Q(CTX.{i})) (e : Q(EXPR.{i})) (τ : Q(TYPE.{i}))
    : MetaM (Σ' (τ' : Q(TYPE.{i})), PLift (@QuotedDefEq (i.succ.succ) q(TYPE.{i}) τ τ') × Q(TYPED.{i} $ctx $e $τ')) :=
    match e with
    | ~q(EXPR.lam $id $A $e') => do
      let α1 ← Qq.mkFreshExprMVarQ (q(TYPE.{i})) (userName := `α₁)
      let α2 ← Qq.mkFreshExprMVarQ (q(TYPE.{i})) (userName := `α₂)
      let ⟨eq'⟩ ← assertDefEqQ τ q(TYPE.arr $α1 $α2)
      let ⟨_⟩ ← assertDefEqQ (u := i.succ.succ) A α1
      match ctx with
      | ~q([]) => throwError "Empty context!"
      | ~q($D :: $D') => do
        let ⟨_, ⟨⟨_⟩, H⟩⟩ ← typecheck i q(($A :: $D) :: $D') e' α2
        pure ⟨q(TYPE.arr $α1 $α2), ⟨PLift.up eq', q(by
          apply TYPED.lam $H
        )⟩⟩
      | _ => do
        let ⟨D, D', eqc⟩ ← ctxUnconsReduce i ctx
        let ⟨_, ⟨⟨_⟩, H⟩⟩ ← typecheck i q(($A :: $D) :: $D') e' α2
        pure ⟨q(TYPE.arr $α1 $α2), ⟨PLift.up eq', q($eqc ▸ (TYPED.lam $H))⟩⟩
    | e => do
      let ⟨τ', H⟩ ← infer i ctx e
      try
        let τ' ← instantiateMVars τ'
        let ⟨eq⟩ ← assertDefEqQ (u := i.succ.succ) τ τ'
        eq.check
        pure ⟨τ', ⟨PLift.up eq, H⟩⟩
      catch _ =>
        throwError "{e} has type {← reduce τ'}, while expected to be of type {τ}."

  partial def infer (i : Level)
    (ctx : Q(CTX.{i})) (e : Q(EXPR.{i}))
    : MetaM (Σ' (τ : Q(TYPE.{i})), Q(TYPED.{i} $ctx $e $τ)) := do
    if let some (.mk type value proof) ← exprAxView? e then
      let N : Q(0 < ($ctx).length) ← mkDecideProof q(0 < ($ctx).length)
      return ⟨type, q(TYPED.reexpr $proof (TYPED.ax $type $value $N))⟩
    if let some (.mk (type := ty) s k m quoteEq) ← quoteTowerView? e then
      let N : Q(0 < ($ctx).length) ← mkDecideProof q(0 < ($ctx).length)
      return ⟨ty, q(TYPED.reexpr
        (($quoteEq).trans
          (quote_reoffset $s $k $m ($ctx).length (($ctx).getLast?.map List.length)))
        (TYPED.quote $ctx $N $s))⟩
    match e with
    | ~q(EXPR.annot $e' $t) => do
      let ⟨t', ⟨_, H⟩⟩ ← typecheck i ctx e' t
      pure ⟨t', H⟩
    | ~q(EXPR.embed $A _) => do
      let N : Q(0 < ($ctx).length) ← mkDecideProof q(0 < ($ctx).length)
      pure ⟨q(TYPE.embed $A), q(TYPED.embed $N)⟩
    | ~q(EXPR.embed_apply $A $B $f $x) => do
      let ⟨_, ⟨⟨_⟩, H1⟩⟩ ← typecheck i ctx f q(TYPE.embed ($A → $B))
      let ⟨_, ⟨⟨_⟩, H2⟩⟩ ← typecheck i ctx x q(TYPE.embed $A)
      pure ⟨q(TYPE.embed $B), q(TYPED.embed_apply $H1 $H2)⟩
    | ~q(EXPR.pure $e) => do
      let ⟨_, ⟨⟨_⟩, H⟩⟩ ← typecheck i ctx e q(TYPE.embed Prop)
      pure ⟨q(TYPE.prop), q(TYPED.pure $H)⟩
    | ~q(@EXPR.var $id $n $n') => do
      try
        let N' : Q($n < ($ctx).length) ← mkDecideProof q($n < ($ctx).length)
        let N : Q($n' < ((($ctx).get (Fin.mk $n $N'))).length) ← mkDecideProof q($n' < (($ctx).get (Fin.mk $n $N')).length)
        let ⟨_⟩ ← assertDefEqQ (u := i) q(EXPR.var $id ↑((Fin.mk $n $N')) ↑(Fin.mk $n' $N)) e
        pure ⟨q(((($ctx).get (Fin.mk $n $N'))).get (Fin.mk $n' $N)), q((@TYPED.var_explicit $ctx $id (Fin.mk $n $N') (Fin.mk $n' $N)))⟩
      catch _ =>
        throwError m!"{← reduce id} is not accessible in the current context {← reduce ctx}."
    | ~q(@EXPR.var' $n $n') => do
      try
        let N' : Q($n < ($ctx).length) ← mkDecideProof q($n < ($ctx).length)
        let N : Q($n' < ((($ctx).get (Fin.mk $n $N'))).length) ← mkDecideProof q($n' < (($ctx).get (Fin.mk $n $N')).length)
        let ⟨_⟩ ← assertDefEqQ (u := i) q(EXPR.var' ↑((Fin.mk $n $N')) ↑(Fin.mk $n' $N)) e
        pure ⟨q(((($ctx).get (Fin.mk $n $N'))).get (Fin.mk $n' $N)), q((@TYPED.var'_explicit $ctx (Fin.mk $n $N') (Fin.mk $n' $N)))⟩
      catch _ =>
        throwError m!"({← reduce n}, {← reduce n'}) is not accessible in the current context {← reduce ctx}."
    | ~q(EXPR.lam $id $A $e) => do
      match ctx with
      | ~q([]) => throwError "Empty context!"
      | ~q($D :: $D') => do
        let ⟨t, H⟩ ← infer i q(($A :: $D) :: $D') e
        pure ⟨q(TYPE.arr $A $t), q(TYPED.lam $H)⟩
      | _ => do
        let ⟨D, D', eqc⟩ ← ctxUnconsReduce i ctx
        let ⟨t, H⟩ ← infer i q(($A :: $D) :: $D') e
        pure ⟨q(TYPE.arr $A $t), q($eqc ▸ (TYPED.lam $H))⟩
    | ~q(EXPR.app $α1 $e1 $e2) => do
      let α2 ← Qq.mkFreshExprMVarQ (q(TYPE.{i})) (userName := `α₂)
      let ⟨t, H1⟩ ← infer i ctx e1
      let ⟨_⟩ ←
        try assertDefEqQ (u := i) t q(TYPE.arr $α1 $α2)
        catch _ =>
          throwError (m!"Couldn't ensure that {e1} is a function").compose
            (Lean.indentD m!"{← reduce t} is not a function type")
      let ⟨_, ⟨⟨_⟩, H2⟩⟩ ← typecheck i ctx e2 α1
      pure ⟨α2, q(TYPED.app $H1 $H2)⟩
    | ~q(EXPR.delay $e) => do
      let N : Q(0 < ($ctx).length) ← mkDecideProof q(0 < ($ctx).length)
      let ⟨t, H⟩ ← infer i q([] :: ($ctx)) e
      pure ⟨q(TYPE.later $t), q(TYPED.delay $N $H)⟩
    | ~q(EXPR.adv $n $e') => do
      try
          let α ← Qq.mkFreshExprMVarQ (q(TYPE.{i})) (userName := `α)
          let N' : Q(0 < $n) ← mkDecideProof q(0 < $n)
          let ⟨_, ⟨⟨_⟩, H⟩⟩ ← typecheck i q(($ctx).drop $n) e' q(TYPE.later $α)
          pure ⟨α, q(@TYPED.adv $n $ctx $e' $α $N' $H)⟩
      catch e =>
        throwError (m!"Couldn't advance {e'} by {n} in the current context {ctx}.").compose
          (Lean.indentD e.toMessageData)
    | ~q(EXPR.fix $id $α $e') => do
      let β ← Qq.mkFreshExprMVarQ (q(TYPE.{i})) (userName := `β)
      let ⟨_⟩ ← assertDefEqQ (u := i) α q(TYPE.later $β)
      match ctx with
      | ~q([]) => throwError "Empty context!"
      | ~q($D :: $D') => do
        let ⟨t, ⟨⟨_⟩, H⟩⟩ ← typecheck i q((TYPE.later $β :: $D) :: $D') e' β
        pure ⟨q($t), q(TYPED.fix $H)⟩
      | _ => do
        let ⟨D, D', eqc⟩ ← ctxUnconsReduce i ctx
        let ⟨t, ⟨⟨_⟩, H⟩⟩ ← typecheck i q((TYPE.later $β :: $D) :: $D') e' β
        pure ⟨q($t), q($eqc ▸ (TYPED.fix $H))⟩
    | ~q(EXPR.pair $e1 $e2) => do
      let ⟨t1, H1⟩ ← infer i ctx e1
      let ⟨t2, H2⟩ ← infer i ctx e2
      pure ⟨q(TYPE.prod $t1 $t2), q(TYPED.pair $H1 $H2)⟩
    | ~q(EXPR.proj $α $e' $d) => do
      match d with
      | ~q(DIR.L) =>
        let α' ← Qq.mkFreshExprMVarQ (q(TYPE.{i})) (userName := `α)
        let ⟨_, ⟨⟨_⟩, H⟩⟩ ← typecheck i ctx e' q(TYPE.prod $α' $α)
        pure ⟨α', q(TYPED.projL $H)⟩
      | ~q(DIR.R) =>
        let α' ← Qq.mkFreshExprMVarQ (q(TYPE.{i})) (userName := `α)
        let ⟨_, ⟨⟨_⟩, H⟩⟩ ← typecheck i ctx e' q(TYPE.prod $α $α')
        pure ⟨α', q(TYPED.projR $H)⟩
    | ~q(EXPR.inl $B $e') => do
      let ⟨t1, H⟩ ← infer i ctx e'
      pure ⟨q(TYPE.sum $t1 $B), q(TYPED.inl $H)⟩
    | ~q(EXPR.inr $A $e') => do
      let ⟨t2, H⟩ ← infer i ctx e'
      pure ⟨q(TYPE.sum $A $t2), q(TYPED.inr $H)⟩
    | ~q(EXPR.case $A $B $e' $f $g) => do
      let ⟨_, ⟨⟨_⟩, He⟩⟩ ← typecheck i ctx e' q(TYPE.sum $A $B)
      let C ← Qq.mkFreshExprMVarQ (q(TYPE.{i})) (userName := `C)
      let ⟨_, ⟨⟨_⟩, Hf⟩⟩ ← typecheck i ctx f q(TYPE.arr $A $C)
      let ⟨_, ⟨⟨_⟩, Hg⟩⟩ ← typecheck i ctx g q(TYPE.arr $B $C)
      pure ⟨C, q(TYPED.case $He $Hf $Hg)⟩
    | ~q(EXPR.or $e1 $e2) => do
      let ⟨_, ⟨⟨_⟩, H1⟩⟩ ← typecheck i ctx e1 q(TYPE.prop)
      let ⟨_, ⟨⟨_⟩, H2⟩⟩ ← typecheck i ctx e2 q(TYPE.prop)
      pure ⟨q(TYPE.prop), q(TYPED.or $H1 $H2)⟩
    | ~q(EXPR.and $e1 $e2) => do
      let ⟨_, ⟨⟨_⟩, H1⟩⟩ ← typecheck i ctx e1 q(TYPE.prop)
      let ⟨_, ⟨⟨_⟩, H2⟩⟩ ← typecheck i ctx e2 q(TYPE.prop)
      pure ⟨q(TYPE.prop), q(TYPED.and $H1 $H2)⟩
    | ~q(EXPR.impl $e1 $e2) => do
      let ⟨_, ⟨⟨_⟩, H1⟩⟩ ← typecheck i ctx e1 q(TYPE.prop)
      let ⟨_, ⟨⟨_⟩, H2⟩⟩ ← typecheck i ctx e2 q(TYPE.prop)
      pure ⟨q(TYPE.prop), q(TYPED.impl $H1 $H2)⟩
    | ~q(EXPR.forall $id $A $e) => do
      match ctx with
      | ~q([]) => throwError "Empty context!"
      | ~q($D :: $D') => do
        let ⟨_, ⟨⟨_⟩, H⟩⟩ ← typecheck i q(($A :: $D) :: $D') e q(TYPE.prop)
        pure ⟨q(TYPE.prop), q(TYPED.forall $H)⟩
      | _ => do
        let ⟨D, D', eqc⟩ ← ctxUnconsReduce i ctx
        let ⟨_, ⟨⟨_⟩, H⟩⟩ ← typecheck i q(($A :: $D) :: $D') e q(TYPE.prop)
        pure ⟨q(TYPE.prop), q($eqc ▸ (TYPED.forall $H))⟩
    | ~q(EXPR.exists $id $A $e) => do
      match ctx with
      | ~q([]) => throwError "Empty context!"
      | ~q($D :: $D') => do
        let ⟨_, ⟨⟨_⟩, H⟩⟩ ← typecheck i q(($A :: $D) :: $D') e q(TYPE.prop)
        pure ⟨q(TYPE.prop), q(TYPED.exists $H)⟩
      | _ => do
        let ⟨D, D', eqc⟩ ← ctxUnconsReduce i ctx
        let ⟨_, ⟨⟨_⟩, H⟩⟩ ← typecheck i q(($A :: $D) :: $D') e q(TYPE.prop)
        pure ⟨q(TYPE.prop), q($eqc ▸ (TYPED.exists $H))⟩
    | ~q(EXPR.lift $e) => do
      let ⟨_, ⟨⟨_⟩, H⟩⟩ ← typecheck i ctx e q(TYPE.later TYPE.prop)
      pure ⟨q(TYPE.prop), q(TYPED.lift $H)⟩
    | ~q(EXPR.true) => do
      let N : Q(0 < ($ctx).length) ← mkDecideProof q(0 < ($ctx).length)
      pure ⟨q(TYPE.prop), q(TYPED.true $N)⟩
    | ~q(EXPR.false) => do
      let N : Q(0 < ($ctx).length) ← mkDecideProof q(0 < ($ctx).length)
      pure ⟨q(TYPE.prop), q(TYPED.false $N)⟩
    | ~q(EXPR.eq $A $e1 $e2) => do
      let ⟨_, ⟨⟨_⟩, H1⟩⟩ ← typecheck i ctx e1 A
      let ⟨_, ⟨⟨_⟩, H2⟩⟩ ← typecheck i ctx e2 A
      pure ⟨q(TYPE.prop), q(TYPED.eq $H1 $H2)⟩
    | e => do
      throwError f!"Type inference failed for {e} in context {ctx}"
end

elab_rules : term
  | `(⟪ $t:term_lang ⟫) => do
    let u ← mkFreshLevelMVar
    let e ← elabTM u t |>.run q([[]])
    let e : Q(EXPR.{u}) ← instantiateMVars e
    try discard <| infer u q([[]]) e catch _ => pure ()
    instantiateMVars e

elab "box(" t:term_lang ")" : term => do
  let u ← mkFreshLevelMVar
  let t ← elabTM u t |>.run q([[]])
  let t : Q(EXPR.{u}) ← instantiateMVars t
  try
    let p ← infer u q([[]]) t
    let B := p.fst
    let B' : Q(TYPE.{u}) ← reduce B
    let A := p.snd
    let A' : Q(TYPED.{u} [[]] $t $B') ← reduce A
    pure q(SYNT.mk.{u} $t $A')
  catch e =>
    throwError m!"Couldn't typecheck {t}".compose (Lean.indentD e.toMessageData)

partial def toplevel (id : TSyntax `ident) (bs : TSyntaxArray ``Lean.Parser.Term.bracketedBinder)
  (r : Option (TSyntax `type_lang)) (e : TSyntax `term_lang) : TermElabM Declaration := do
  let name : Name := id.getId
  Term.elabBinders bs fun xs => do
  let u ← mkFreshLevelMVar
  let e : Q(EXPR.{u}) ← elabTM u e |>.run q([[]])
  let e : Q(EXPR.{u}) ← instantiateMVars e
  match r with
  | some r =>
    let r ← (elabTYPE u r).run
    let p ← typecheck u q([[]]) e r
    let B : Q(TYPE.{u}) ← reduce p.fst
    let A : Q(TYPED.{u} [[]] $e $B) ← reduce (skipProofs := false) p.snd.snd
    let A : Q(TYPED.{u} [[]] $e $B) ← instantiateMVars A
    let mut type : Expr := q(SYNT.{u} $B)
    let mut value := q(SYNT.mk.{u} $e $A)
    value ← instantiateMVars value
    type ← mkForallFVars xs type
    value ← mkLambdaFVars xs value
    let univ := collectLevelMVars {} value |>.result
    let univ_ty := collectLevelMVars {} type |>.result
    let levelParams ← (univ_ty ++ univ).filterMapM fun x => do
      if (← getLevelMVarAssignment? x).isNone then
        let ut_name ← mkFreshUserName `ut
        assignLevelMVar x (.param ut_name)
        pure ut_name
      else pure none
    value ← instantiateMVars value
    type ← instantiateMVars type
    let fDecl := Declaration.defnDecl
      { name
      , type
      , value
      , safety := .safe
      , hints := .regular 0
      , levelParams := levelParams.toList
      }
    guardedAttrExt.add name
    pure fDecl
  | none =>
    let p ← infer u q([[]]) e
    let B := p.fst
    let B' : Q(TYPE.{u}) ← reduce B
    let A : Q(TYPED.{u} [[]] $e $B') ← reduce (skipProofs := false) p.snd
    let A : Q(TYPED.{u} [[]] $e $B') ← instantiateMVars A
    let mut value := q(SYNT.mk.{u} $e $A)
    let mut type := q(SYNT.{u} $B')
    value ← instantiateMVars value
    type ← mkForallFVars xs type
    value ← mkLambdaFVars xs value
    let univ := collectLevelMVars {} value |>.result
    let univ_ty := collectLevelMVars {} type |>.result
    let levelParams ← (univ_ty ++ univ).filterMapM fun x => do
      if (← getLevelMVarAssignment? x).isNone then
        let ut_name ← mkFreshUserName `ut
        assignLevelMVar x (.param ut_name)
        pure ut_name
      else pure none
    value ← instantiateMVars value
    type ← instantiateMVars type
    let fDecl := .defnDecl
      { name
      , type
      , value
      , safety := .safe
      , hints := .regular 0
      , levelParams := levelParams.toList
      }
    guardedAttrExt.add name
    pure fDecl

syntax "gdef" ident (ppSpace bracketedBinder)* (" : " type_lang)? " := " term_lang : command
elab_rules : command | `(gdef $id $bs:bracketedBinder* $[: $r]? := $e) => do
  let fDecl ← Command.runTermElabM $ fun _ => do
    toplevel id bs r e
  Command.liftCoreM (do addDecl fDecl (forceExpose := true); compileDecl fDecl)
  Command.elabCommand (← `(command| attribute [irreducible] $id))

end expr
