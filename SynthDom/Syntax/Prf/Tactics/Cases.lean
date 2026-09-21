module

public meta import SynthDom.Syntax.Prf.Tactics.Structural

@[expose] public meta section

section prf

open Lean Meta Elab Tactic Qq Syntax

def obtain_core (projected : ProjectedHyp) (x hx : Ident) : TacticM Unit := do
  let hn := projected.ref.name
  let vn : Name := x.getId
  let hxn : Name := hx.getId
  let ⟨u_1, v⟩ ← matchGoalFrames "gobtain"
  let goal := v.goal
  let { PΓ := PΓ0, PΨ := PΨf, Γ0, Ψ := Ψf } := v.current
  let { PΓ := PΓs, PΨ := PΨs, Γ := Γs, Ψ := Ψs } := v.past
  let Q := goal.Φ
  have prop : Q(EXPR.{u_1}) := projected.normalized.prop
  match prop with
  | ~q(EXPR.exists.{u_1} $nm $τ $P) =>
    have prem1 : Q(GOAL ($PΓ0 :: $PΓs) ($PΨf :: $PΨs) ($Γ0 :: $Γs) ($Ψf :: $Ψs)
        (EXPR.exists $nm $τ $P)) := projected.normalized.proof
    let HQty ← mkTypedProp u_1 q($Γ0 :: $Γs) Q
    let ⟨gN, eqG⟩ ← canon u_1 q(($τ :: $Γ0) :: $Γs) q(weaken $Q octx_wk)
    let mvar2 ← mkFreshExprMVarQ
      q(GOAL (($vn :: $PΓ0) :: $PΓs) (($hxn :: $PΨf) :: $PΨs) (($τ :: $Γ0) :: $Γs)
        (($P :: intro_wrap' $Ψf) :: $Ψs) $gN)
    let prem2 : Q(GOAL (($vn :: $PΓ0) :: $PΓs) (($hxn :: $PΨf) :: $PΨs) (($τ :: $Γ0) :: $Γs)
        (($P :: intro_wrap' $Ψf) :: $Ψs) (weaken $Q octx_wk)) := q(GOAL_subst $mvar2 $eqG)
    let tm : Q(GOAL ($PΓ0 :: $PΓs) ($PΨf :: $PΨs) ($Γ0 :: $Γs) ($Ψf :: $Ψs) $Q) :=
      q(GOAL_exists_elim $vn $hxn $HQty $prem1 $prem2)
    goal.assign tm [mvar2]
  | _ => throwError m!"gcases: hypothesis {hn} is not an existential"

def case_split_core (e : TSyntax `term_lang) (nv₁ nh₁ nv₂ nh₂ : Name) :
    TacticM Unit := do
  let ⟨u_1, v⟩ ← matchGoalFrames "gcases"
  let goal := v.goal
  let { PΓ := PΓ0, PΨ, Γ0, Ψ } := v.current
  let { PΓ := PΓs, PΨ := PΨs, Γ := Γs, Ψ := Ψs } := v.past
  let Φ := goal.Φ
  let eΓ : Q(ElabCtx) := q($PΓ0 :: $PΓs)
  let e ← (elabTM u_1 e).run eΓ
  let A ← Qq.mkFreshExprMVarQ (q(TYPE.{u_1}))
  let B ← Qq.mkFreshExprMVarQ (q(TYPE.{u_1}))
  let ⟨_, ⟨⟨_⟩, He⟩⟩ ← typecheck u_1 q($Γ0 :: $Γs) e q(TYPE.sum $A $B)
  let ⟨_, ⟨⟨_⟩, HΦ⟩⟩ ← typecheck u_1 q($Γ0 :: $Γs) Φ q(TYPE.prop)
  let ⟨goalNorm, eqG⟩ ← canon u_1 q(($A :: $Γ0) :: $Γs) q(weaken $Φ octx_wk)
  let ⟨eNorm, eqE⟩ ← canon u_1 q(($A :: $Γ0) :: $Γs) q(weaken $e octx_wk)
  let hypInlNorm : Q(EXPR.{u_1}) :=
    q(EXPR.eq (TYPE.sum $A $B) $eNorm (EXPR.inl $B (EXPR.var $nv₁ 0 0)))
  let hypInrNorm : Q(EXPR.{u_1}) :=
    q(EXPR.eq (TYPE.sum $A $B) $eNorm (EXPR.inr $A (EXPR.var $nv₂ 0 0)))
  let hypInlEq : Q(EXPR.eq (TYPE.sum $A $B) (weaken $e octx_wk) (EXPR.inl $B (EXPR.var' 0 0))
      = $hypInlNorm) :=
    q((congrArg (fun z => EXPR.eq (TYPE.sum $A $B) z (EXPR.inl $B (EXPR.var' 0 0))) $eqE).trans
      (congrArg (fun z => EXPR.eq (TYPE.sum $A $B) $eNorm (EXPR.inl $B z))
        (var_ghost $nv₁ 0 0).symm))
  let hypInrEq : Q(EXPR.eq (TYPE.sum $A $B) (weaken $e octx_wk) (EXPR.inr $A (EXPR.var' 0 0))
      = $hypInrNorm) :=
    q((congrArg (fun z => EXPR.eq (TYPE.sum $A $B) z (EXPR.inr $A (EXPR.var' 0 0))) $eqE).trans
      (congrArg (fun z => EXPR.eq (TYPE.sum $A $B) $eNorm (EXPR.inr $A z))
        (var_ghost $nv₂ 0 0).symm))
  let g1 ← mkFreshExprMVarQ q(GOAL (($nv₁ :: $PΓ0) :: $PΓs) (($nh₁ :: $PΨ) :: $PΨs) (($A :: $Γ0) :: $Γs)
    (($hypInlNorm :: intro_wrap' $Ψ) :: $Ψs) $goalNorm)
  let g2 ← mkFreshExprMVarQ q(GOAL (($nv₂ :: $PΓ0) :: $PΓs) (($nh₂ :: $PΨ) :: $PΨs) (($B :: $Γ0) :: $Γs)
    (($hypInrNorm :: intro_wrap' $Ψ) :: $Ψs) $goalNorm)
  let mkBranch (nv nh : Name) (ΓX : Q(CTX.{u_1})) (hypNorm : Q(EXPR.{u_1}))
      (hypEq : Expr) (g : Expr) : TacticM Expr := do
    let mkGoalTy (hyp prop : Q(EXPR.{u_1})) : Q(Prop) :=
      q(GOAL (($nv :: $PΓ0) :: $PΓs) (($nh :: $PΨ) :: $PΨs) $ΓX
        (($hyp :: intro_wrap' $Ψ) :: $Ψs) $prop)
    let f1 ← withLocalDeclD `z q(EXPR.{u_1}) fun z =>
      mkLambdaFVars #[z] (mkGoalTy z q(weaken $Φ octx_wk))
    let f2 ← withLocalDeclD `z q(EXPR.{u_1}) fun z =>
      mkLambdaFVars #[z] (mkGoalTy hypNorm z)
    let tyEq ← mkEqTrans (← mkCongrArg f1 hypEq) (← mkCongrArg f2 eqG)
    mkEqMPR tyEq g
  let br1 : Q(GOAL (($nv₁ :: $PΓ0) :: $PΓs) (($nh₁ :: $PΨ) :: $PΨs) (($A :: $Γ0) :: $Γs)
      ((EXPR.eq (TYPE.sum $A $B) (weaken $e octx_wk) (EXPR.inl $B (EXPR.var' 0 0)) :: intro_wrap' $Ψ) :: $Ψs)
      (weaken $Φ octx_wk)) ←
    mkBranch nv₁ nh₁ q(($A :: $Γ0) :: $Γs) hypInlNorm hypInlEq g1
  let br2 : Q(GOAL (($nv₂ :: $PΓ0) :: $PΓs) (($nh₂ :: $PΨ) :: $PΨs) (($B :: $Γ0) :: $Γs)
      ((EXPR.eq (TYPE.sum $A $B) (weaken $e octx_wk) (EXPR.inr $A (EXPR.var' 0 0)) :: intro_wrap' $Ψ) :: $Ψs)
      (weaken $Φ octx_wk)) ←
    mkBranch nv₂ nh₂ q(($B :: $Γ0) :: $Γs) hypInrNorm hypInrEq g2
  let tm : Q(GOAL ($PΓ0 :: $PΓs) ($PΨ :: $PΨs) ($Γ0 :: $Γs) ($Ψ :: $Ψs) $Φ) :=
    q(GOAL_sum_elim $nv₁ $nh₁ $nv₂ $nh₂ $e $HΦ $He $br1 $br2)
  goal.assign tm [g1, g2]
  pure ()

def pair_split_core (e : TSyntax `term_lang) (nx ny : Name) : TacticM Unit := do
  let ⟨u, frames⟩ ← matchGoalFrames "gcase_split"
  let goal := frames.goal
  let { PΨ, Γ0, Ψ, .. } := frames.current
  let { PΨ := PΨs, Γ := Γs, Ψ := Ψs, .. } := frames.past
  let PΓ := goal.context.PΓ
  let eΓ : Q(ElabCtx) := q($PΓ)
  let eE ← (elabTM u e).run eΓ
  let A ← Qq.mkFreshExprMVarQ (q(TYPE.{u}))
  let B ← Qq.mkFreshExprMVarQ (q(TYPE.{u}))
  let ⟨_, ⟨⟨_⟩, He⟩⟩ ← typecheck u q($Γ0 :: $Γs) eE q(TYPE.prod $A $B)
  have He : Q(TYPED ($Γ0 :: $Γs) $eE (TYPE.prod $A $B)) := He
  let ⟨eN, _⟩ ← canon u q(($B :: $A :: $Γ0) :: $Γs)
    q(weaken (weaken $eE octx_wk) octx_wk)
  let P : Q(EXPR.{u}) :=
    q(EXPR.exists $nx $A (EXPR.exists $ny $B
      (EXPR.eq (TYPE.prod $A $B)
        $eN
        (EXPR.pair (EXPR.var $nx 0 1) (EXPR.var $ny 0 0)))))
  let scratch : Name := Name.mkSimple "_gps"
  let opened ← openAssertion "gcase_split" scratch P
  replaceMainGoal [opened.premise.mvarId!]
  withMainContext <| exists_core (← `(term_lang| π₁ $e))
  withMainContext <| exists_core (← `(term_lang| π₂ $e))
  let gl ← getMainGoal
  let glTy ← instantiateMVars (← gl.getType)
  let Hlen : Q((($Γ0 :: $Γs)).length = (($Ψ :: $Ψs)).length) ←
    mkHlen u q($Γ0 :: $Γs) q($Ψ :: $Ψs)
  let core : Expr :=
    q((⟨PROVES.eq_def (EQ.eta_prod $He) (Hlen := $Hlen)⟩ :
      GOAL $PΓ ($PΨ :: $PΨs) ($Γ0 :: $Γs) ($Ψ :: $Ψs)
        (EXPR.eq (TYPE.prod $A $B) $eE
          (EXPR.pair (EXPR.proj $B $eE DIR.L) (EXPR.proj $A $eE DIR.R)))))
  let prf ← withTransparency .all <| mkExpectedTypeHint core glTy
  closeWith gl prf [opened.continuation]

def cases_or_core (h h' : Ident) : TacticM Unit := do
  let n : Name := h.getId
  let n' : Name := h'.getId
  let ⟨u_1, v⟩ ← matchGoalFrames "gcases"
  let goal := v.goal
  let { PΨ, Ψ, .. } := v.current
  let { PΨ := PΨs, Ψ := Ψs, .. } := v.past
  let { PΓ, Γ, .. } := goal.context
  let Φ := goal.Φ
  let p ← v.goal.context.projectHyp "cases" n
  have prop : Q(EXPR.{u_1}) := p.normalized.prop
  match prop with
  | ~q(EXPR.or.{u_1} $A $B) =>
    have hypN : Q(GOAL $PΓ ($PΨ :: $PΨs) $Γ ($Ψ :: $Ψs) (EXPR.or $A $B)) := p.normalized.proof
    let mvarId1 ← mkFreshExprMVarQ q(GOAL $PΓ (($n' :: $PΨ) :: $PΨs) $Γ (($A :: $Ψ) :: $Ψs) $Φ)
    let mvarId2 ← mkFreshExprMVarQ q(GOAL $PΓ (($n' :: $PΨ) :: $PΨs) $Γ (($B :: $Ψ) :: $Ψs) $Φ)
    let tm : Q(GOAL $PΓ ($PΨ :: $PΨs) $Γ ($Ψ :: $Ψs) $Φ) :=
      q(GOAL_or_elim $n' $n' $mvarId1 $mvarId2 $hypN)
    goal.assign tm [mvarId1, mvarId2]
    pure ()
  | _ =>
    throwError m!"gcases: hypothesis {n} is not a disjunction"
def casesAndStep (takeL : Bool) (projected : ProjectedHyp) (nm : Name) : TacticM Unit := do
  let ⟨u_1, v⟩ ← matchGoalFrames "gcases"
  let hn := projected.ref.name
  let { PΨ, Ψ, .. } := v.current
  let { PΨ := PΨs, Ψ := Ψs, .. } := v.past
  let { PΓ, Γ, .. } := v.goal.context
  have prop : Q(EXPR.{u_1}) := projected.normalized.prop
  match prop with
  | ~q(EXPR.and.{u_1} $A $B) =>
    let hypAB : Q(GOAL $PΓ ($PΨ :: $PΨs) $Γ ($Ψ :: $Ψs) (EXPR.and $A $B)) ←
      pure projected.normalized.proof
    if takeL then
      let comp : Q(GOAL $PΓ ($PΨ :: $PΨs) $Γ ($Ψ :: $Ψs) $A) := q(GOAL_and_elim_l $hypAB)
      discard <| addDerived nm { prop := A, proof := comp }
    else
      let comp : Q(GOAL $PΓ ($PΨ :: $PΨs) $Γ ($Ψ :: $Ψs) $B) := q(GOAL_and_elim_r $hypAB)
      discard <| addDerived nm { prop := B, proof := comp }
  | _ => throwError m!"gcases: hypothesis {hn} is not a conjunction"

def cases_and_core (projected : ProjectedHyp) (h1 h2 : Ident) : TacticM Unit := do
  casesAndStep true projected h1.getId
  let ⟨_, goal⟩ ← matchGoal "gcases"
  let projected ← goal.context.projectHyp "cases" projected.ref.name
  casesAndStep false projected h2.getId
def gcasesLeafName (pat : TSyntax `gcases_pat) (path : String) : Name × Bool :=
  match pat with
  | `(gcases_pat| $x:ident) => (x.getId, false)
  | _ => (Name.mkSimple ("_gc" ++ path), true)

partial def gcasesGo (hn : Name) (pat : TSyntax `gcases_pat) (path : String) : TacticM Unit := focus do
  match pat with
  | `(gcases_pat| $x:ident) =>
    if x.getId != hn then
      withMainContext (renameHyp "grename" hn x.getId)
  | `(gcases_pat| _) =>
    withMainContext (clearHyp "gclear" hn)
  | `(gcases_pat| ⟨$p1:gcases_pat, $p2:gcases_pat⟩) =>
    let (n1, r1) := gcasesLeafName p1 (path ++ "l")
    let (n2, r2) := gcasesLeafName p2 (path ++ "r")
    let i1 := mkIdent n1
    let i2 := mkIdent n2
    let projected ← withMainContext do
      let ⟨_, view⟩ ← matchGoal "gcases"
      view.context.projectHyp "gcases" hn
    if projected.normalized.prop.isAppOf ``EXPR.exists then
      if r1 then throwError "gcases: the ∃-witness pattern must be an identifier"
      withMainContext (obtain_core projected i1 i2)
      withMainContext (clearHyp "gclear" hn)
      if r2 then gcasesGo n2 p2 (path ++ "r")
    else
      withMainContext (cases_and_core projected i1 i2)
      withMainContext (clearHyp "gclear" hn)
      if r1 then gcasesGo n1 p1 (path ++ "l")
      if r2 then gcasesGo n2 p2 (path ++ "r")
  | `(gcases_pat| ⟨$p1:gcases_pat, $p2:gcases_pat, $p3:gcases_pat⟩) =>
    gcasesGo hn (← `(gcases_pat| ⟨$p1:gcases_pat, ⟨$p2:gcases_pat, $p3:gcases_pat⟩⟩)) path
  | `(gcases_pat| ($p1:gcases_pat | $p2:gcases_pat)) =>
    let name := Name.mkSimple ("_gc" ++ path)
    withMainContext (cases_or_core (mkIdent hn) (mkIdent name))
    match ← getGoals with
    | [left, right] =>
      setGoals [left]
      gcasesGo name p1 (path ++ "l")
      let leftGoals ← getGoals
      setGoals [right]
      gcasesGo name p2 (path ++ "r")
      setGoals (leftGoals ++ (← getGoals))
    | _ => throwError "gcases: the ∨-split did not produce exactly two goals"
  | _ => throwError "gcases: unsupported pattern"

def gcasesSumLeaf (pat : TSyntax `gcases_pat) : TacticM (Name × Option Name) :=
  match pat with
  | `(gcases_pat| ⟨$v:ident, $h:ident⟩) => pure (v.getId, some h.getId)
  | `(gcases_pat| $v:ident) => pure (v.getId, none)
  | _ => throwError "gcases: a sum branch pattern must be ⟨value, equation⟩ or an identifier"

def gcasesTerm (e : TSyntax `term_lang) (pat : TSyntax `gcases_pat) : TacticM Unit := focus do
  match pat with
  | `(gcases_pat| ($p1:gcases_pat | $p2:gcases_pat)) =>
    let (nv₁, nh₁?) ← gcasesSumLeaf p1
    let (nv₂, nh₂?) ← gcasesSumLeaf p2
    let scratch := Name.mkSimple "_gch"
    withMainContext <| case_split_core e nv₁ (nh₁?.getD scratch) nv₂ (nh₂?.getD scratch)
    match ← getGoals with
    | [left, right] =>
      setGoals [left]
      if nh₁?.isNone then
        withMainContext (clearHyp "gclear" scratch)
      let leftGoals ← getGoals
      setGoals [right]
      if nh₂?.isNone then
        withMainContext (clearHyp "gclear" scratch)
      setGoals (leftGoals ++ (← getGoals))
    | _ => throwError "gcases: the sum split did not produce exactly two goals"
  | `(gcases_pat| ⟨$x:ident, $y:ident, $h:ident⟩) =>
    withMainContext (pair_split_core e x.getId y.getId)
    gcasesGo (Name.mkSimple "_gps") (← `(gcases_pat| ⟨$x:ident, ⟨$y:ident, $h:ident⟩⟩)) ""
  | _ => throwError "gcases: a term scrutinee takes (⟨v, h⟩ | ⟨v, h⟩) for sums or ⟨x, y, h⟩ for products"

end prf
