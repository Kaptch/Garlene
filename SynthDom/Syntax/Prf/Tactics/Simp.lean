module

public meta import Lean
public meta import Qq

public meta import SynthDom.Config.Attr
public meta import SynthDom.Syntax.Expr.Elab
public meta import SynthDom.Syntax.Expr.Typecheck
public meta import SynthDom.Syntax.Prf.Core
public meta import SynthDom.Syntax.Prf.Wrappers
public meta import SynthDom.Syntax.Prf.Weaken
public meta import SynthDom.Syntax.Utils

@[expose] public meta section

section prf

open Lean Meta Elab PrettyPrinter Delaborator Tactic SubExpr Qq Syntax

attribute [expr_simp]
  offset_ren offset_ren_zero offset_ren_pos offset_ren_pos_iff weaken_var'
  cut_ren cut_ren_zero local_weaken_list weaken weaken_var weaken_lam
  weaken_forall weaken_exists weaken_fix SUBST.sr_compose SUBST.drop SUBST.ext'
  SUBST.ext SUBST.id SSUBST.id offset_ssubst offset_ssubst_zero offset_ssubst_pos
  cut_ssubst cut_ssubst_zero SSUBST.sr_compose SSUBST.drop SSUBST.ext' SSUBST.ext
  REN.local_n_weak REN.global_n_weak subst_var ssubst_var delay_subst adv_subst
  app_subst embed_subst embed_apply_subst pure_subst pair_subst proj_subst
  and_subst or_subst impl_subst true_subst false_subst lift_subst
  inl_subst inr_subst case_subst
  eq_subst ax_subst var_subst1 var_subst2 var_subst3 var_subst4
  var_subst5 var_subst6 var_subst7 var_subst8 var_subst7' var_subst8'
  var_subst9 var_subst10 var_subst11 var_subst12 var_subst13 lam_subst
  forall_subst exists_subst fix_subst SSUBST.cons quote_synt weaken_quote_cons_global_shift_zero
  weaken_synt_expr binds_synt_expr binds_quote
  SUBST.id' SSUBST.id' single_subst octx_wk wk_delay intro_wrap' intro_wrap
  intro_wrap_length
  List.getElem_cons_zero List.getElem_cons_succ List.get_eq_getElem
  List.getElem?_cons_zero List.getElem?_cons_succ
  List.length_cons List.length_nil List.length_singleton
  List.drop_zero List.drop_succ_cons List.drop_nil
  List.getLast?_singleton List.getLast?_cons_cons
  List.map_cons List.map_nil
  Option.map_some Option.map_none
  Nat.add_zero Nat.zero_add Nat.sub_zero

theorem var_ghost (nm : Lean.Name) (n m : Nat) : EXPR.var nm n m = EXPR.var' n m := by
  with_unfolding_all rfl

@[expr_simp] theorem annot_expr (e : EXPR.{i}) (τ : TYPE.{i}) : EXPR.annot e τ = e := by
  with_unfolding_all rfl

def simpWith (u : Level) (tactic : TSyntax `tactic) (e : Q(EXPR.{u})) :
    TacticM (Σ' (result : Q(EXPR.{u})), Q($e = $result)) := do
  let context ← Lean.Elab.Tactic.mkSimpContext tactic false
  let simplified : Lean.Meta.Simp.ResultQ q(EXPR.{u}) × _ ←
    (Lean.Meta.simp e context.ctx : MetaM (Lean.Meta.Simp.ResultQ q(EXPR.{u}) × _))
  let result : Q(EXPR.{u}) := simplified.1.expr
  let proof : Q($e = $result) ← simplified.1.getProof
  pure ⟨result, proof⟩

def normSimp (u : Level) (e : Q(EXPR.{u})) :
    TacticM (Σ' (result : Q(EXPR.{u})), Q($e = $result)) := do
  simpWith u (← `(tactic| simp only [expr_simp])) e

def normSimpW (u : Level) (e : Q(EXPR.{u})) :
    TacticM (Σ' (result : Q(EXPR.{u})), Q($e = $result)) := do
  simpWith u (← `(tactic| simp (config := { failIfUnchanged := false }) only
    [weaken, weaken_var', weaken_var, weaken_lam, weaken_forall, weaken_exists, weaken_fix])) e

end prf
