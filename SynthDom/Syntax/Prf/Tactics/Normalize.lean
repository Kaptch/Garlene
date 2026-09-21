module

public meta import Lean
public meta import Qq

public meta import SynthDom.Syntax.Expr.Elab
public meta import SynthDom.Syntax.Expr.Typecheck
public meta import SynthDom.Syntax.Expr.View
public import SynthDom.Syntax.Prf.Syntax
public meta import SynthDom.Syntax.Prf.Core
public meta import SynthDom.Syntax.Prf.Wrappers
public meta import SynthDom.Syntax.Prf.Tactics.Simp
public meta import SynthDom.Syntax.Prf.Tactics.State
public meta import SynthDom.Config.Attr
public meta import SynthDom.Syntax.Utils

@[expose] public meta section

section prf

open Lean Meta Elab PrettyPrinter Delaborator Tactic SubExpr Qq Syntax

def rebuildWithCongr (source : Expr) (childIndices : Array Nat)
    (children : Array (Expr × Expr)) : MetaM (Option (Expr × Expr)) := do
  unless childIndices.size == children.size do return none
  let args := source.getAppArgs
  if childIndices.any (· ≥ args.size) then return none
  let childAt (index : Nat) : Option (Expr × Expr) :=
    (childIndices.findIdx? (· == index)).map (children[·]!)
  if childIndices.zipIdx.all fun (index, position) => args[index]! == children[position]!.1 then
    return none
  let mut rebuilt := args
  for (index, position) in childIndices.zipIdx do
    rebuilt := rebuilt.set! index children[position]!.1
  let mut proof ← mkEqRefl source.getAppFn
  for index in [:args.size] do
    match childAt index with
    | some (_, childProof) => proof ← mkCongr proof childProof
    | none => proof ← mkCongrFun proof args[index]!
  pure (some (mkAppN source.getAppFn rebuilt, proof))

partial def simplify_quote (Γ : Q(CTX.{i})) (e : Q(EXPR.{i}))
  : MetaM (Σ' (e' : Q(EXPR.{i})), Q($e = $e')) := do
  let extendCtx : Q(TYPE.{i}) → MetaM (Q(CTX.{i})) := fun τ => do
    match Γ with
    | ~q([]) => throwError "Empty context!"
    | ~q($D :: $D') => pure q(($τ :: $D) :: $D')
    | _ => pure q(($τ :: (($Γ).headD ([] : OCTX.{i}))) :: ($Γ).tail)
  let unchanged : MetaM (Σ' (e' : Q(EXPR.{i})), Q($e = $e')) := pure ⟨e, q(Eq.refl _)⟩
  let descend (childIndices : Array Nat) (children : Array (Expr × Q(CTX.{i}))) :
      MetaM (Σ' (e' : Q(EXPR.{i})), Q($e = $e')) := do
    let results ← children.mapM fun (child, childCtx) => do
      have childQ : Q(EXPR.{i}) := child
      let ⟨value, proof⟩ ← simplify_quote childCtx childQ
      pure ((value : Expr), (proof : Expr))
    let some (rebuilt, proof) ← rebuildWithCongr e childIndices results | unchanged
    have rebuiltQ : Q(EXPR.{i}) := rebuilt
    have proofQ : Q($e = $rebuiltQ) := proof
    pure ⟨rebuiltQ, proofQ⟩
  if let some (.mk s k m proof) ← quoteTowerView? e then
    return ⟨q(EXPR.quote $s ($Γ).length ((($Γ).getLast?).map List.length))
      , q(($proof).trans
          (quote_reoffset $s $k $m ($Γ).length ((($Γ).getLast?).map List.length)))⟩
  match e with
  | ~q(weaken $e1 $σ) => do
    match e1 with
    | ~q(weaken $e2 $δ1) => do
      let ⟨eq⟩ ← assertDefEqQ (α := q(EXPR.{i})) e q(weaken $e2 (REN.comp $δ1 $σ))
      pure ⟨q(weaken $e2 (REN.comp $δ1 $σ)), q($eq)⟩
    | _ => unchanged
  | ~q(binds $δ2 (binds $δ1 $e')) => do
    let ⟨eq⟩ ← assertDefEqQ (α := q(EXPR.{i})) e q(binds (SSUBST.comp $δ1 $δ2) $e')
    pure ⟨q(binds (SSUBST.comp $δ1 $δ2) $e'), q($eq)⟩
  | ~q(binds $σ (EXPR.quote $e' $n $m)) =>
    pure ⟨q(EXPR.quote $e' ($Γ).length ((($Γ).getLast?).map List.length))
        , q((binds_quote $e' $n $m $σ).trans
            (quote_reoffset $e' $n $m ($Γ).length ((($Γ).getLast?).map List.length)))⟩
  | ~q(binds $σb $inner) => do
    match ← quoteTowerView? inner with
    | some (.mk s k m proof) =>
      pure ⟨q(EXPR.quote $s ($Γ).length ((($Γ).getLast?).map List.length))
          , q(((congrArg (fun z => binds $σb z) $proof).trans (binds_quote $s $k $m $σb)).trans
              (quote_reoffset $s $k $m ($Γ).length ((($Γ).getLast?).map List.length)))⟩
    | none => unchanged
  | ~q(EXPR.delay $body) => descend #[0] #[((body : Expr), q([] :: $Γ))]
  | ~q(EXPR.adv $n $body) => descend #[1] #[((body : Expr), q(($Γ).drop $n))]
  | _ =>
    if let some binder := exprBinderView? e then
      descend #[binder.bodyIndex] #[(binder.body, ← extendCtx binder.type)]
    else
      let some view := exprNodeView? e | unchanged
      unless view.structural do return ← unchanged
      descend view.childIndices (view.children.map (·, Γ))

def canon (u : Level) (Γ : Q(CTX.{u})) (e : Q(EXPR.{u})) :
    TacticM (Σ' (e' : Q(EXPR.{u})), Q($e = $e')) := do
  let ⟨e1, eq1⟩ ← normSimp u e
  let ⟨e2, eq2⟩ ← simplify_quote Γ e1
  let ⟨e3, eq3⟩ ← normSimp u e2
  pure ⟨e3, q(($eq1).trans (($eq2).trans $eq3))⟩

abbrev EqResult (Γ : Q(CTX.{i})) (τ : Q(TYPE.{i})) (e : Q(EXPR.{i})) :=
  Σ' (e' : Q(EXPR.{i})), Q(EQ $Γ $τ $e $e')

abbrev EqRecurse (i : Level) :=
  (Γ : Q(CTX.{i})) → (PΓ : Q(PP_CTX)) → (τ : Q(TYPE.{i})) →
    (e : Q(EXPR.{i})) → MetaM (EqResult Γ τ e)

def singleSubstConsEq (u : Level) (PΓ : Q(PP_CTX)) (Γ : Q(CTX.{u})) (e : Q(EXPR.{u})) :
    MetaM Q(single_subst (List.map List.length $Γ) $e =
      SSUBST.cons (SSUBST.id' $PΓ) $e) := do
  let ⟨lengths⟩ ← assertDefEqQ (α := q(List Nat))
    q(List.map List.length $Γ) q(List.map List.length $PΓ)
  pure q(by
    simp only [single_subst]
    rw [SSUBST.id_eq]
    rw [←$lengths])

def descendEq (name : String) (recurse : EqRecurse i) (Γ : Q(CTX.{i}))
    (PΓ : Q(PP_CTX)) (τ : Q(TYPE.{i})) (e : Q(EXPR.{i})) :
    MetaM (Option (EqResult Γ τ e)) := do
  match e with
  | ~q(.app $τ' $e1 $e2) => do
    let ⟨e1', eq1⟩ ← recurse Γ PΓ q(TYPE.arr $τ' $τ) e1
    let ⟨e2', eq2⟩ ← recurse Γ PΓ τ' e2
    pure <| some ⟨q(.app $τ' $e1' $e2'), q(EQ.cong_app $eq1 $eq2)⟩
  | ~q(.eq $τ' $e1 $e2) => do
    let ⟨_⟩ ← assertDefEqQ (α := q(TYPE.{i})) q(TYPE.prop) τ
    let ⟨e1', eq1⟩ ← recurse Γ PΓ τ' e1
    let ⟨e2', eq2⟩ ← recurse Γ PΓ τ' e2
    pure <| some ⟨q(.eq $τ' $e1' $e2'), q(EQ.cong_eq $eq1 $eq2)⟩
  | ~q(.embed_apply $A $B $e1 $e2) => do
    let ⟨_⟩ ← assertDefEqQ (α := q(TYPE.{i})) q(TYPE.embed $B) τ
    let ⟨e1', eq1⟩ ← recurse Γ PΓ q(TYPE.embed ($A → $B)) e1
    let ⟨e2', eq2⟩ ← recurse Γ PΓ q(TYPE.embed $A) e2
    pure <| some ⟨q(.embed_apply $A $B $e1' $e2'), q(EQ.cong_embed_apply $eq1 $eq2)⟩
  | ~q(.pair $e1 $e2) => do
    let α1 ← Qq.mkFreshExprMVarQ (q(TYPE.{i})) (userName := `α₁)
    let α2 ← Qq.mkFreshExprMVarQ (q(TYPE.{i})) (userName := `α₂)
    let ⟨_⟩ ← assertDefEqQ (α := q(TYPE.{i})) q(TYPE.prod $α1 $α2) τ
    let ⟨e1', eq1⟩ ← recurse Γ PΓ α1 e1
    let ⟨e2', eq2⟩ ← recurse Γ PΓ α2 e2
    pure <| some ⟨q(.pair $e1' $e2'), q(EQ.cong_pair $eq1 $eq2)⟩
  | ~q(.proj $σ $e' $d) => do
    match d with
    | ~q(DIR.L) => do
      let ⟨e'', eqe⟩ ← recurse Γ PΓ q(TYPE.prod $τ $σ) e'
      pure <| some ⟨q(.proj $σ $e'' DIR.L), q(EQ.cong_proj1 $eqe)⟩
    | ~q(DIR.R) => do
      let ⟨e'', eqe⟩ ← recurse Γ PΓ q(TYPE.prod $σ $τ) e'
      pure <| some ⟨q(.proj $σ $e'' DIR.R), q(EQ.cong_proj2 $eqe)⟩
    | _ => do
      let ⟨_, ⟨_⟩, H⟩ ← typecheck i Γ q(.proj $σ $e' $d) τ
      pure <| some ⟨q(.proj $σ $e' $d), q(EQ.rfl $H)⟩
  | ~q(.inl $B $e1) => do
    let α ← Qq.mkFreshExprMVarQ (q(TYPE.{i})) (userName := `α)
    let ⟨_⟩ ← assertDefEqQ (α := q(TYPE.{i})) q(TYPE.sum $α $B) τ
    let ⟨e1', eq1⟩ ← recurse Γ PΓ α e1
    pure <| some ⟨q(.inl $B $e1'), q(EQ.cong_inl $eq1)⟩
  | ~q(.inr $A $e1) => do
    let β ← Qq.mkFreshExprMVarQ (q(TYPE.{i})) (userName := `β)
    let ⟨_⟩ ← assertDefEqQ (α := q(TYPE.{i})) q(TYPE.sum $A $β) τ
    let ⟨e1', eq1⟩ ← recurse Γ PΓ β e1
    pure <| some ⟨q(.inr $A $e1'), q(EQ.cong_inr $eq1)⟩
  | ~q(.case $A $B $e' $f $g) => do
    let ⟨e'', eqe⟩ ← recurse Γ PΓ q(TYPE.sum $A $B) e'
    let ⟨f', eqf⟩ ← recurse Γ PΓ q(TYPE.arr $A $τ) f
    let ⟨g', eqg⟩ ← recurse Γ PΓ q(TYPE.arr $B $τ) g
    pure <| some ⟨q(.case $A $B $e'' $f' $g'), q(EQ.cong_case $eqe $eqf $eqg)⟩
  | ~q(.lift $e1) => do
    let ⟨_⟩ ← assertDefEqQ (α := q(TYPE.{i})) q(TYPE.prop) τ
    let ⟨e2, eq⟩ ← recurse Γ PΓ q(TYPE.later TYPE.prop) e1
    pure <| some ⟨q(.lift $e2), q(EQ.cong_lift $eq)⟩
  | ~q(.pure $e1) => do
    let ⟨_⟩ ← assertDefEqQ (α := q(TYPE.{i})) q(TYPE.prop) τ
    let ⟨e1', eq1⟩ ← recurse Γ PΓ q(TYPE.embed Prop) e1
    pure <| some ⟨q(.pure $e1'), q(EQ.cong_pure $eq1)⟩
  | ~q(.and $e1 $e2) => do
    let ⟨_⟩ ← assertDefEqQ (α := q(TYPE.{i})) q(TYPE.prop) τ
    let ⟨e1', eq1⟩ ← recurse Γ PΓ q(TYPE.prop) e1
    let ⟨e2', eq2⟩ ← recurse Γ PΓ q(TYPE.prop) e2
    pure <| some ⟨q(.and $e1' $e2'), q(EQ.cong_and $eq1 $eq2)⟩
  | ~q(.or $e1 $e2) => do
    let ⟨_⟩ ← assertDefEqQ (α := q(TYPE.{i})) q(TYPE.prop) τ
    let ⟨e1', eq1⟩ ← recurse Γ PΓ q(TYPE.prop) e1
    let ⟨e2', eq2⟩ ← recurse Γ PΓ q(TYPE.prop) e2
    pure <| some ⟨q(.or $e1' $e2'), q(EQ.cong_or $eq1 $eq2)⟩
  | ~q(.impl $e1 $e2) => do
    let ⟨_⟩ ← assertDefEqQ (α := q(TYPE.{i})) q(TYPE.prop) τ
    let ⟨e1', eq1⟩ ← recurse Γ PΓ q(TYPE.prop) e1
    let ⟨e2', eq2⟩ ← recurse Γ PΓ q(TYPE.prop) e2
    pure <| some ⟨q(.impl $e1' $e2'), q(EQ.cong_impl $eq1 $eq2)⟩
  | ~q(.lam $x $A $body) => do
    match Γ, PΓ with
    | ~q($D :: $D'), ~q($PD :: $PD') => do
      let β ← Qq.mkFreshExprMVarQ (q(TYPE.{i})) (userName := `β)
      let ⟨_⟩ ← assertDefEqQ (α := q(TYPE.{i})) q(TYPE.arr $A $β) τ
      let ⟨body', eq⟩ ← recurse q(($A :: $D) :: $D') q(($x :: $PD) :: $PD') β body
      pure <| some ⟨q(.lam $x $A $body'), q(EQ.cong_lam $eq)⟩
    | _, _ => throwError m!"{name}: lambda in an empty context"
  | ~q(.lam' $A $body) => do
    match Γ, PΓ with
    | ~q($D :: $D'), ~q($PD :: $PD') => do
      let β ← Qq.mkFreshExprMVarQ (q(TYPE.{i})) (userName := `β)
      let ⟨_⟩ ← assertDefEqQ (α := q(TYPE.{i})) q(TYPE.arr $A $β) τ
      let ⟨body', eq⟩ ← recurse q(($A :: $D) :: $D')
        q((Name.anonymous :: $PD) :: $PD') β body
      pure <| some ⟨q(.lam' $A $body'), q(EQ.cong_lam' $eq)⟩
    | _, _ => throwError m!"{name}: lambda in an empty context"
  | ~q(.forall $x $A $body) => do
    match Γ, PΓ with
    | ~q($D :: $D'), ~q($PD :: $PD') => do
      let ⟨_⟩ ← assertDefEqQ (α := q(TYPE.{i})) q(TYPE.prop) τ
      let ⟨body', eq⟩ ← recurse q(($A :: $D) :: $D') q(($x :: $PD) :: $PD') q(TYPE.prop) body
      pure <| some ⟨q(.forall $x $A $body'), q(EQ.cong_forall $eq)⟩
    | _, _ => throwError m!"{name}: ∀ in an empty context"
  | ~q(.forall' $A $body) => do
    match Γ, PΓ with
    | ~q($D :: $D'), ~q($PD :: $PD') => do
      let ⟨_⟩ ← assertDefEqQ (α := q(TYPE.{i})) q(TYPE.prop) τ
      let ⟨body', eq⟩ ← recurse q(($A :: $D) :: $D')
        q((Name.anonymous :: $PD) :: $PD') q(TYPE.prop) body
      pure <| some ⟨q(.forall' $A $body'), q(EQ.cong_forall' $eq)⟩
    | _, _ => throwError m!"{name}: ∀ in an empty context"
  | ~q(.exists $x $A $body) => do
    match Γ, PΓ with
    | ~q($D :: $D'), ~q($PD :: $PD') => do
      let ⟨_⟩ ← assertDefEqQ (α := q(TYPE.{i})) q(TYPE.prop) τ
      let ⟨body', eq⟩ ← recurse q(($A :: $D) :: $D') q(($x :: $PD) :: $PD') q(TYPE.prop) body
      pure <| some ⟨q(.exists $x $A $body'), q(EQ.cong_exists $eq)⟩
    | _, _ => throwError m!"{name}: ∃ in an empty context"
  | ~q(.exists' $A $body) => do
    match Γ, PΓ with
    | ~q($D :: $D'), ~q($PD :: $PD') => do
      let ⟨_⟩ ← assertDefEqQ (α := q(TYPE.{i})) q(TYPE.prop) τ
      let ⟨body', eq⟩ ← recurse q(($A :: $D) :: $D')
        q((Name.anonymous :: $PD) :: $PD') q(TYPE.prop) body
      pure <| some ⟨q(.exists' $A $body'), q(EQ.cong_exists' $eq)⟩
    | _, _ => throwError m!"{name}: ∃ in an empty context"
  | _ => pure none

def mkTypedAfterReduceAll (u : Level) (Γ : Q(CTX.{u})) (e : Q(EXPR.{u}))
    (τ : Q(TYPE.{u})) : MetaM Q(TYPED $Γ $e $τ) := do
  try
    let ⟨_, ⟨_, proof⟩⟩ ← typecheck u Γ e τ
    mkExpectedTypeHint proof q(TYPED $Γ $e $τ)
  catch _ =>
    let reduced : Q(EXPR.{u}) ← reduceAll e
    let ⟨_⟩ ← assertDefEqQ (α := q(EXPR.{u})) reduced e
    let ⟨_, ⟨_, proof⟩⟩ ← typecheck u Γ reduced τ
    mkExpectedTypeHint proof q(TYPED $Γ $e $τ)

partial def simplify (Γ : Q(CTX.{i})) (PΓ : Q(PP_CTX)) (τ : Q(TYPE.{i})) (e : Q(EXPR.{i}))
  : MetaM (Σ' (e' : Q(EXPR.{i})), Q(EQ $Γ $τ $e $e')) :=
  match e with
  | ~q(.app $τ1 (.lam $x $τ2 $e') $t) => do
    let ⟨_⟩ ← assertDefEqQ (α := q(TYPE.{i})) τ1 τ2
    match Γ with
    | ~q([]) => throwError "Empty context!"
    | ~q($D :: $D') => do
      let t' : Q(EXPR.{i}) ← reduceAll t
      let ⟨_⟩ ← assertDefEqQ (α := q(EXPR.{i})) t' t
      let ⟨_, ⟨_⟩, H1⟩ ← typecheck i q($D :: $D') t' τ2
      let EQ' ← singleSubstConsEq i PΓ q($D :: $D') t
      let H2 ← mkTypedAfterReduceAll i q(($τ2 :: $D) :: $D') e' τ
      pure ⟨q(binds (SSUBST.cons (SSUBST.id' $PΓ) $t) $e')
          , q(by
            rw [←$EQ']
            exact @EQ.beta_lam $D $D' $t _ _ _ $x $H1 $H2)⟩
  | ~q(.adv $n (.delay $e')) => do
    let N : Q(0 < $n) ← mkDecideProof q(0 < $n)
    let M : Q($n < ($Γ).length) ← mkDecideProof q($n < ($Γ).length)
    let H ← mkTypedAfterReduceAll i q([] :: List.drop $n $Γ) e' τ
    pure ⟨q(weaken $e' (wk_delay (($Γ)[0]'(Nat.lt_trans $N $M)).length ($n - 1)))
        , q(@EQ.beta_delay $Γ $e' _ $n $N $M $H)⟩
  | ~q(.app $τ' $e1 $e2) => do
    let lam? ← do
      match ← quoteTowerView? e1 with
      | some (.mk s k m proof) => do
        let lit : Q(EXPR.{i}) ← whnf q(SYNT.expr $s)
        match lit with
        | ~q(.lam $_x $_τ $_b) => do
          let ⟨eqLit⟩ ← assertDefEqQ (α := q(EXPR.{i})) q(SYNT.expr $s) lit
          let eqFn : Q($e1 = $lit) :=
            q(($proof).trans ((quote_eq_expr $s $k $m).trans $eqLit))
          pure (some (⟨lit, eqFn⟩ : Σ' (l : Q(EXPR.{i})), Q($e1 = $l)))
        | _ => pure none
      | none => pure none
    match lam? with
    | some p => do
      let lit : Q(EXPR.{i}) := p.fst
      let eqFn : Q($e1 = $lit) := p.snd
      let ⟨out, eqOut⟩ ← simplify Γ PΓ τ q(.app $τ' $lit $e2)
      pure ⟨out, q(EQ.subst_l $eqOut
        (congrArg (fun z => EXPR.app $τ' z $e2) (Eq.symm $eqFn)))⟩
    | none => do
      let some result ← descendEq "simplify" simplify Γ PΓ τ e
        | throwError "simplify: application descent failed"
      pure result
  | ~q(.embed_apply $A $B $e1 $e2) => do
    let ⟨_⟩ ← assertDefEqQ (α := q(TYPE.{i})) q(TYPE.embed $B) τ
    let ⟨e1', eq1⟩ ← simplify Γ PΓ q(TYPE.embed ($A → $B)) e1
    let ⟨e2', eq2⟩ ← simplify Γ PΓ q(TYPE.embed $A) e2
    let cong : Q(EQ $Γ (TYPE.embed $B) (.embed_apply $A $B $e1 $e2) (.embed_apply $A $B $e1' $e2')) :=
      q(EQ.cong_embed_apply $eq1 $eq2)
    match e1', e2' with
    | ~q(EXPR.embed $_FT $f), ~q(EXPR.embed $_XT $x) => do
      have f' : Q($A → $B) := f
      have x' : Q($A) := x
      let N ← mkCtxPos i Γ
      let beta : Q(EQ $Γ (TYPE.embed $B) (.embed_apply $A $B $e1' $e2') (.embed $B ($f' $x'))) ←
        withTransparency .all <| mkExpectedTypeHint
          q(EQ.beta_embed_apply (Γ := $Γ) $f' $x' $N)
          q(EQ $Γ (TYPE.embed $B) (.embed_apply $A $B $e1' $e2') (.embed $B ($f' $x')))
      pure ⟨q(.embed $B ($f' $x')), q(EQ.tran $cong $beta)⟩
    | _, _ => pure ⟨q(.embed_apply $A $B $e1' $e2'), cong⟩
  | ~q(.proj $σ $e' $d) => do
    match e' with
    | ~q(.pair $a $b) => do
      match d with
      | ~q(DIR.L) => do
        let ⟨_, ⟨_⟩, Ha⟩ ← typecheck i Γ a τ
        let ⟨_, ⟨_⟩, Hb⟩ ← typecheck i Γ b σ
        let ⟨out, eqOut⟩ ← simplify Γ PΓ τ a
        pure ⟨out, q(EQ.tran (EQ.beta_prod_l $Ha $Hb) $eqOut)⟩
      | ~q(DIR.R) => do
        let ⟨_, ⟨_⟩, Ha⟩ ← typecheck i Γ a σ
        let ⟨_, ⟨_⟩, Hb⟩ ← typecheck i Γ b τ
        let ⟨out, eqOut⟩ ← simplify Γ PΓ τ b
        pure ⟨out, q(EQ.tran (EQ.beta_prod_r $Ha $Hb) $eqOut)⟩
      | _ => do
        let ⟨_, ⟨_⟩, H⟩ ← typecheck i Γ q(.proj $σ $e' $d) τ
        pure ⟨q(.proj $σ $e' $d), q(EQ.rfl $H)⟩
    | _ => do
      match d with
      | ~q(DIR.L) => do
        let ⟨e'', eqe⟩ ← simplify Γ PΓ q(TYPE.prod $τ $σ) e'
        pure ⟨q(.proj $σ $e'' DIR.L), q(EQ.cong_proj1 $eqe)⟩
      | ~q(DIR.R) => do
        let ⟨e'', eqe⟩ ← simplify Γ PΓ q(TYPE.prod $σ $τ) e'
        pure ⟨q(.proj $σ $e'' DIR.R), q(EQ.cong_proj2 $eqe)⟩
      | _ => do
        let ⟨_, ⟨_⟩, H⟩ ← typecheck i Γ q(.proj $σ $e' $d) τ
        pure ⟨q(.proj $σ $e' $d), q(EQ.rfl $H)⟩
  | ~q(.case $A $B $e' $f $g) => do
    match e' with
    | ~q(.inl $B' $a) => do
      let ⟨_⟩ ← assertDefEqQ (α := q(TYPE.{i})) B' B
      let ⟨_, ⟨_⟩, Ha⟩ ← typecheck i Γ a A
      let ⟨_, ⟨_⟩, Hf⟩ ← typecheck i Γ f q(TYPE.arr $A $τ)
      let ⟨_, ⟨_⟩, Hg⟩ ← typecheck i Γ g q(TYPE.arr $B $τ)
      let ⟨out, eqOut⟩ ← simplify Γ PΓ τ q(.app $A $f $a)
      pure ⟨out, q(EQ.tran (EQ.beta_case_inl $Ha $Hf $Hg) $eqOut)⟩
    | ~q(.inr $A' $b) => do
      let ⟨_⟩ ← assertDefEqQ (α := q(TYPE.{i})) A' A
      let ⟨_, ⟨_⟩, Hb⟩ ← typecheck i Γ b B
      let ⟨_, ⟨_⟩, Hf⟩ ← typecheck i Γ f q(TYPE.arr $A $τ)
      let ⟨_, ⟨_⟩, Hg⟩ ← typecheck i Γ g q(TYPE.arr $B $τ)
      let ⟨out, eqOut⟩ ← simplify Γ PΓ τ q(.app $B $g $b)
      pure ⟨out, q(EQ.tran (EQ.beta_case_inr $Hb $Hf $Hg) $eqOut)⟩
    | _ => do
      let ⟨e'', eqe⟩ ← simplify Γ PΓ q(TYPE.sum $A $B) e'
      let ⟨f', eqf⟩ ← simplify Γ PΓ q(TYPE.arr $A $τ) f
      let ⟨g', eqg⟩ ← simplify Γ PΓ q(TYPE.arr $B $τ) g
      pure ⟨q(.case $A $B $e'' $f' $g'), q(EQ.cong_case $eqe $eqf $eqg)⟩
  | ~q(.delay $e1) => do
    let N ← mkCtxPos i Γ
    let α1 ← Qq.mkFreshExprMVarQ (q(TYPE.{i})) (userName := `α₁)
    let ⟨_⟩ ← assertDefEqQ (α := q(TYPE.{i})) q(TYPE.later $α1) τ
    let ⟨e2, eq⟩ ← simplify q([] :: $Γ) q([] :: $PΓ) α1 e1
    pure ⟨q(.delay $e2), q(EQ.cong_delay $N $eq)⟩
  | ~q(.adv $n $e1) => do

    let advRfl : MetaM (Σ' (r : Q(EXPR.{i})), Q(EQ $Γ $τ (.adv $n $e1) $r)) := do
      let ⟨_, ⟨_⟩, H⟩ ← typecheck i Γ q(.adv $n $e1) τ
      pure ⟨q(.adv $n $e1), q(EQ.rfl $H)⟩
    let some nv ← (Lean.Meta.evalNat (n : Expr)).run | advRfl
    match ListLiteral.drop? (← instantiateMVars Γ) nv,
        ListLiteral.drop? (← instantiateMVars PΓ) nv with
    | some Γd, some PΓd => do
      have Γd' : Q(CTX.{i}) := Γd
      have PΓd' : Q(PP_CTX) := PΓd
      let N : Q(0 < $n) ← mkDecideProof q(0 < $n)
      let ⟨e2, eq⟩ ← simplify Γd' PΓd' q(TYPE.later $τ) e1
      let eq' : Q(EQ (List.drop $n $Γ) (TYPE.later $τ) $e1 $e2) ←
        mkExpectedTypeHint eq q(EQ (List.drop $n $Γ) (TYPE.later $τ) $e1 $e2)
      pure ⟨q(.adv $n $e2), q(EQ.cong_adv $n $eq' $N)⟩
    | _, _ => advRfl
  | e' => do
    match ← descendEq "simplify" simplify Γ PΓ τ e' with
    | some result => pure result
    | none => do
      let fallback : MetaM (Σ' (r : Q(EXPR.{i})), Q(EQ $Γ $τ $e' $r)) := do
        let e'' : Q(EXPR.{i}) ← reduceAll e'
        let ⟨_⟩ ← assertDefEqQ (α := q(EXPR.{i})) e'' e'
        let ⟨_, ⟨_⟩, H⟩ ← typecheck i Γ e'' τ
        pure ⟨q($e'), q(EQ.rfl $H)⟩
      match ← quoteTowerView? e' with
      | some (.mk s k m proof) => do
        let qc : Q(EXPR.{i}) := q(EXPR.quote $s ($Γ).length ((($Γ).getLast?).map List.length))
        let eqc : Q($e' = $qc) :=
          q(($proof).trans (quote_reoffset $s $k $m ($Γ).length ((($Γ).getLast?).map List.length)))
        let ⟨_, ⟨_⟩, H⟩ ← typecheck i Γ qc τ
        pure ⟨qc, q(EQ.subst_l (EQ.rfl $H) (Eq.symm $eqc))⟩
      | none => fallback

partial def simplify_fix (Γ : Q(CTX.{i})) (PΓ : Q(PP_CTX)) (τ : Q(TYPE.{i})) (e : Q(EXPR.{i})) : MetaM (Σ' (e' : Q(EXPR.{i})), Q(EQ $Γ $τ $e $e')) :=
  match e with
  | ~q(.fix $nm $τ' $e') => do
    match Γ with
    | ~q([]) => throwError "Empty context!"
    | ~q($D :: $D') => do
      let ⟨_⟩ ← assertDefEqQ (α := q(TYPE.{i})) q(TYPE.later $τ) τ'
      let ⟨_, ⟨_⟩, H1⟩ ← typecheck i q((TYPE.later $τ :: $D) :: $D') e' τ
      let unfolded : Q(EXPR.{i}) :=
        q(.delay (weaken (.fix $nm (TYPE.later $τ) $e') (REN.global_shift 1 REN.id)))
      let EQ' ← singleSubstConsEq i PΓ q($D :: $D') unfolded
      pure ⟨q(binds (SSUBST.cons (SSUBST.id' $PΓ) (.delay (weaken (.fix $nm (TYPE.later $τ) $e') (REN.global_shift 1 REN.id)))) $e')
          , q(by
            rw [←$EQ']
            exact @EQ.unfold _ $D $D' $e' $nm $H1)⟩
  | ~q(.fix' $τ' $e') => do
    match Γ with
    | ~q([]) => throwError "Empty context!"
    | ~q($D :: $D') => do
      let ⟨_⟩ ← assertDefEqQ (α := q(TYPE.{i})) q(TYPE.later $τ) τ'
      let ⟨_, ⟨_⟩, H1⟩ ← typecheck i q((TYPE.later $τ :: $D) :: $D') e' τ
      let unfolded : Q(EXPR.{i}) :=
        q(.delay (weaken (.fix' (TYPE.later $τ) $e') (REN.global_shift 1 REN.id)))
      let EQ' ← singleSubstConsEq i PΓ q($D :: $D') unfolded
      pure ⟨q(binds (SSUBST.cons (SSUBST.id' $PΓ) (.delay (weaken (.fix' (TYPE.later $τ) $e') (REN.global_shift 1 REN.id)))) $e')
          , q(by
            rw [←$EQ']
            exact @EQ.unfold' _ $D $D' $e' $H1)⟩
  | e' => do
    match ← descendEq "simplify_fix" simplify_fix Γ PΓ τ e' with
    | some result => pure result
    | none => do
      let ⟨_, ⟨_⟩, H⟩ ← typecheck i Γ e' τ
      pure ⟨q($e'), q(EQ.rfl $H)⟩

def gResidualSimp : TacticM Unit := do
  evalTactic (← `(tactic| try simp))
  evalTactic (← `(tactic| try simp only [quote_eq_expr, weaken_synt_expr, binds_synt_expr,
    var_ghost, and_true, true_and]))

def gSubstSimp : TacticM Unit := do
  evalTactic (← `(tactic| simp (config := { failIfUnchanged := false }) only [expr_simp]))

def emitSubstGoal (u : Level) (PΓ PΨ Γ0 Γs Ψ tE P : Expr)
    (k : Expr → TacticM Unit) : TacticM Unit := do
  have PΓ' : Q(ElabCtx) := PΓ
  have PΨ' : Q(ElabCtx) := PΨ
  have Γ0' : Q(OCTX.{u}) := Γ0
  have Γs' : Q(CTX.{u}) := Γs
  have Ψ' : Q(PCTX.{u}) := Ψ
  have tE' : Q(EXPR.{u}) := tE
  have P' : Q(EXPR.{u}) := P
  let EQ' ← singleSubstConsEq u PΓ' q($Γ0' :: $Γs') tE'
  let goalE : Q(EXPR.{u}) := q(binds (SSUBST.cons (SSUBST.id' $PΓ') $tE') $P')
  let mvar' ← mkFreshExprMVarQ q(GOAL $PΓ' $PΨ' ($Γ0' :: $Γs') $Ψ' $goalE)
  let prem : Q(GOAL $PΓ' $PΨ' ($Γ0' :: $Γs') $Ψ'
      (binds (single_subst (List.map List.length ($Γ0' :: $Γs')) $tE') $P')) :=
    q(GOAL_subst $mvar' (congrArg (fun s => binds s $P') $EQ'))
  k prem
  replaceMainGoal [mvar'.mvarId!]
  gSubstSimp

end prf
