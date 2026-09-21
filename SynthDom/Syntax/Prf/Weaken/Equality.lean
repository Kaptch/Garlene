module

public import SynthDom.Syntax.Prf.Weaken.Substitution
public import SynthDom.Interp.Interp

@[expose] public section

section prf
open Lean

open CategoryTheory in
theorem expr_interp_ctx_pad {Γ : CTX.{i}} (Γ' : CTX.{i}) {e : EXPR.{i}} {τ : TYPE.{i}}
    (H : TYPED Γ e τ) (HΓ : 0 < Γ.length) :
    expr_interp (Γ ++ Γ') e τ
      = (expr_interp Γ e τ).map (fun x => ⟦TSSUBST.pad Γ Γ' HΓ⟧ₛₛ ≫ x) := by
  have h := eq_bind Γ e τ (TSSUBST.pad Γ Γ' HΓ) H
  rwa [binds_ctx_id H] at h

theorem expr_interp_ctx_pad_congr {Γ : CTX.{i}} (Γ' : CTX.{i}) {e e' : EXPR.{i}} {τ : TYPE.{i}}
    (H : TYPED Γ e τ) (H' : TYPED Γ e' τ) (Heq : expr_interp Γ e τ = expr_interp Γ e' τ) :
    expr_interp (Γ ++ Γ') e τ = expr_interp (Γ ++ Γ') e' τ := by
  rw [expr_interp_ctx_pad Γ' H (typing_stack_len H),
    expr_interp_ctx_pad Γ' H' (typing_stack_len H), Heq]

theorem global_shift_lift_comm (σ : REN) :
    REN.equiv (REN.comp σ (REN.global_shift 1 REN.id))
      (REN.comp (REN.global_shift 1 REN.id) σ.global_lift) := by
  refine ⟨fun n m => ?_, fun n => ?_⟩
  · simp only [weaken_var']
    rcases h : weaken_var' σ n m with ⟨a, b⟩
    show (1 + a, b) = weaken_var' σ.global_lift (1 + n) m
    rw [show (1 : Nat) + n = n + 1 from by omega]
    simp only [weaken_var', h, Nat.add_comm a 1]
  · simp only [offset_comp_all]
    cases n with
    | zero => simp [offset_ren]
    | succ n' =>
      obtain ⟨j, hj⟩ : ∃ j, offset_ren σ (n' + 1) = j + 1 :=
        ⟨_, (Nat.succ_pred_eq_of_pos (offset_succ_pos σ n')).symm⟩
      rw [hj, off_global_shift_succ, off_id, off_global_shift_succ, off_id]
      rw [show (1 : Nat) + (n' + 1) = (n' + 1) + 1 from by omega, off_global_lift_succ, hj]
      omega

theorem global_shift_lift_cons_comm (σ : REN) :
    REN.equiv (REN.comp σ.cons (REN.global_shift 1 REN.id).cons)
      (REN.comp (REN.global_shift 1 REN.id).cons σ.global_lift.cons) :=
  (equiv_cons_comp σ (REN.global_shift 1 REN.id)).trans
    (((global_shift_lift_comm σ).cons).trans
      (equiv_cons_comp (REN.global_shift 1 REN.id) σ.global_lift).symm)

theorem ren_dom_cons_shape {σ : REN} {Δ Γ : CTX.{i}} (Hσ : TYPED_REN σ Δ Γ) :
    ∃ Δ0 Δs, Δ = Δ0 :: Δs := by
  cases Δ with
  | nil => exact absurd (ren_len' _ Hσ) (by simp)
  | cons a b => exact ⟨a, b, rfl⟩

theorem EQ.weaken {Γ : CTX.{i}} {τ : TYPE.{i}} {e1 e2 : EXPR.{i}} (H : EQ Γ τ e1 e2) :
    ∀ {Δ : CTX.{i}} {σ : REN}, TYPED_REN σ Δ Γ → EQ Δ τ (weaken e1 σ) (weaken e2 σ) := by
  induction H with
  | rfl He => intro Δ σ Hσ; exact EQ.rfl (weaken_typing He Hσ)
  | sym He H IH => intro Δ σ Hσ; exact EQ.sym (weaken_typing He Hσ) (IH Hσ)
  | tran H1 H2 IH1 IH2 => intro Δ σ Hσ; exact EQ.tran (IH1 Hσ) (IH2 Hσ)
  | @beta_lam' Γ Γs e' τ' e σ' He' He =>
    intro Δ σ Hσ
    obtain ⟨Δ0, Δs, rfl⟩ := ren_dom_cons_shape Hσ
    have key := EQ.beta_lam' (weaken_typing He' Hσ) (weaken_typing He (TYPED_REN.cons τ' Hσ))
    refine key.subst_r ?_
    exact (weaken_single_subst He He' Hσ).symm
  | @eta_lam' Γ e τ' σ' He =>
    intro Δ σ Hσ
    have key := EQ.eta_lam' (weaken_typing He Hσ)
    refine key.subst_r ?_
    show EXPR.lam' τ' (EXPR.app τ' (_root_.weaken (_root_.weaken e σ) (REN.local_weaken REN.id))
            (EXPR.var' 0 0))
       = EXPR.lam' τ' (EXPR.app τ' (_root_.weaken (_root_.weaken e (REN.local_weaken REN.id)) σ.cons)
            (EXPR.var' 0 0))
    congr 2
    rw [weaken_comp, weaken_comp]
    exact (weaken_congr e (shift_cons σ)).symm
  | @beta_delay Γ e τ' n Hlt Hlt' He =>

    intro Δ σ Hσ
    have Horig : EQ Γ τ' (EXPR.adv n (EXPR.delay e))
        (_root_.weaken e (wk_delay (Γ[0]'(Nat.lt_trans Hlt Hlt')).length (n - 1))) :=
      EQ.beta_delay n Hlt Hlt' He
    have He1 : TYPED Γ (EXPR.adv n (EXPR.delay e)) τ' := Horig.typed
    have He2 : TYPED Γ (_root_.weaken e (wk_delay (Γ[0]'(Nat.lt_trans Hlt Hlt')).length (n - 1))) τ' :=
      Horig.typed'
    refine EQ.ax (weaken_typing He1 Hσ) (weaken_typing He2 Hσ) ?_
    rw [eq_weak Γ _ τ' Hσ He1, eq_weak Γ _ τ' Hσ He2, eq_interp Γ _ _ τ' Horig]
  | @eta_delay Γ e τ' He =>
    intro Δ σ Hσ
    have key := EQ.eta_delay (weaken_typing He Hσ)
    refine key.subst_r ?_
    show EXPR.delay (EXPR.adv 1 (_root_.weaken e σ))
       = EXPR.delay (EXPR.adv (offset_ren σ.global_lift 1)
            (_root_.weaken e (cut_ren σ.global_lift 1)))
    rw [off_global_lift_succ, offset_ren_zero, cut_global_lift_succ, cut_ren_zero]
  | beta_embed_apply f x h =>
    intro Δ σ Hσ
    exact EQ.beta_embed_apply f x (ren_len' _ Hσ)
  | @unfold' τ' Δ' Γ' e He =>
    intro Δ σ Hσ
    obtain ⟨Δ0, Δs, rfl⟩ := ren_dom_cons_shape Hσ
    have key := EQ.unfold' (weaken_typing He (TYPED_REN.cons (TYPE.later τ') Hσ))
    refine key.subst_r ?_
    have Hfix : TYPED (Δ' :: Γ') (EXPR.fix' (TYPE.later τ') e) τ' := TYPED.fix' He
    have Hshift : TYPED_REN (REN.global_shift 1 REN.id) ([] :: Δ' :: Γ') (Δ' :: Γ') :=
      TYPED_REN.global_shift (Ψ := [[]]) (Γ := Δ' :: Γ') (Δ := Δ' :: Γ') (σ := REN.id) 1 (by simp)
        (TYPED_REN.id (by simp))
    have Ha : TYPED (Δ' :: Γ')
        (EXPR.delay (_root_.weaken (EXPR.fix' (TYPE.later τ') e) (REN.global_shift 1 REN.id)))
        τ'.later :=
      TYPED.delay (by simp) (weaken_typing Hfix Hshift)
    rw [weaken_single_subst He Ha Hσ]
    congr 2
    show (_root_.weaken (EXPR.fix' τ'.later (_root_.weaken e σ.cons)) (REN.global_shift 1 REN.id)).delay
       = (_root_.weaken (_root_.weaken (EXPR.fix' τ'.later e) (REN.global_shift 1 REN.id))
           σ.global_lift).delay
    congr 1
    show EXPR.fix' τ'.later (_root_.weaken (_root_.weaken e σ.cons) (REN.global_shift 1 REN.id).cons)
       = EXPR.fix' τ'.later (_root_.weaken (_root_.weaken e (REN.global_shift 1 REN.id).cons)
           σ.global_lift.cons)
    congr 1
    rw [weaken_comp, weaken_comp]
    exact weaken_congr e (global_shift_lift_cons_comm σ)
  | beta_prod_l He He' =>
    intro Δ σ Hσ
    exact EQ.beta_prod_l (weaken_typing He Hσ) (weaken_typing He' Hσ)
  | beta_prod_r He He' =>
    intro Δ σ Hσ
    exact EQ.beta_prod_r (weaken_typing He Hσ) (weaken_typing He' Hσ)
  | eta_prod He =>
    intro Δ σ Hσ
    exact EQ.eta_prod (weaken_typing He Hσ)
  | cong_app H1 H2 IH1 IH2 => intro Δ σ Hσ; exact EQ.cong_app (IH1 Hσ) (IH2 Hσ)
  | cong_embed_apply H1 H2 IH1 IH2 => intro Δ σ Hσ; exact EQ.cong_embed_apply (IH1 Hσ) (IH2 Hσ)
  | cong_pure H IH => intro Δ σ Hσ; exact EQ.cong_pure (IH Hσ)
  | cong_lam' H IH =>
    intro Δ σ Hσ
    obtain ⟨Δ0, Δs, rfl⟩ := ren_dom_cons_shape Hσ
    exact EQ.cong_lam' (IH (TYPED_REN.cons _ Hσ))
  | cong_delay h H IH =>
    intro Δ σ Hσ
    exact EQ.cong_delay (ren_len' _ Hσ) (IH (TYPED_REN.global_lift Hσ))
  | @cong_adv Γ A e e' n H hn IH =>
    intro Δ σ Hσ
    have hnlen : n < Γ.length := by
      have := typing_stack_len H.typed
      simp only [List.length_drop] at this; omega
    refine EQ.cong_adv (offset_ren σ n) (IH (cut_ren_typing σ Hσ n hnlen))
      (offset_ren_pos σ n hn)
  | cong_fix' H IH =>
    intro Δ σ Hσ
    obtain ⟨Δ0, Δs, rfl⟩ := ren_dom_cons_shape Hσ
    exact EQ.cong_fix' (IH (TYPED_REN.cons _ Hσ))
  | cong_pair H1 H2 IH1 IH2 => intro Δ σ Hσ; exact EQ.cong_pair (IH1 Hσ) (IH2 Hσ)
  | cong_or H1 H2 IH1 IH2 => intro Δ σ Hσ; exact EQ.cong_or (IH1 Hσ) (IH2 Hσ)
  | cong_and H1 H2 IH1 IH2 => intro Δ σ Hσ; exact EQ.cong_and (IH1 Hσ) (IH2 Hσ)
  | cong_impl H1 H2 IH1 IH2 => intro Δ σ Hσ; exact EQ.cong_impl (IH1 Hσ) (IH2 Hσ)
  | cong_forall' H IH =>
    intro Δ σ Hσ
    obtain ⟨Δ0, Δs, rfl⟩ := ren_dom_cons_shape Hσ
    exact EQ.cong_forall' (IH (TYPED_REN.cons _ Hσ))
  | cong_exists' H IH =>
    intro Δ σ Hσ
    obtain ⟨Δ0, Δs, rfl⟩ := ren_dom_cons_shape Hσ
    exact EQ.cong_exists' (IH (TYPED_REN.cons _ Hσ))
  | cong_proj1 H IH => intro Δ σ Hσ; exact EQ.cong_proj1 (IH Hσ)
  | cong_proj2 H IH => intro Δ σ Hσ; exact EQ.cong_proj2 (IH Hσ)
  | beta_case_inl Ha Hf Hg => intro Δ σ Hσ
                              exact EQ.beta_case_inl (weaken_typing Ha Hσ) (weaken_typing Hf Hσ) (weaken_typing Hg Hσ)
  | beta_case_inr Hb Hf Hg => intro Δ σ Hσ
                              exact EQ.beta_case_inr (weaken_typing Hb Hσ) (weaken_typing Hf Hσ) (weaken_typing Hg Hσ)
  | cong_inl H IH => intro Δ σ Hσ; exact EQ.cong_inl (IH Hσ)
  | cong_inr H IH => intro Δ σ Hσ; exact EQ.cong_inr (IH Hσ)
  | cong_case He Hf Hg IHe IHf IHg => intro Δ σ Hσ; exact EQ.cong_case (IHe Hσ) (IHf Hσ) (IHg Hσ)
  | cong_lift H IH => intro Δ σ Hσ; exact EQ.cong_lift (IH Hσ)
  | cong_eq H1 H2 IH1 IH2 => intro Δ σ Hσ; exact EQ.cong_eq (IH1 Hσ) (IH2 Hσ)
  | @ax Γ e1 τ e2 He He' heq =>
    intro Δ σ Hσ
    refine EQ.ax (weaken_typing He Hσ) (weaken_typing He' Hσ) ?_
    rw [eq_weak Γ e1 τ Hσ He, eq_weak Γ e2 τ Hσ He', heq]

theorem EQ.ctx_pad {Γ : CTX.{i}} {τ : TYPE.{i}} {e1 e2 : EXPR.{i}} (H : EQ Γ τ e1 e2) :
    ∀ Δ : CTX.{i}, EQ (Γ ++ Δ) τ e1 e2 := by
  induction H with
  | rfl He => intro Δ; exact EQ.rfl (He.ctx_pad Δ)
  | sym He _ IH => intro Δ; exact EQ.sym (He.ctx_pad Δ) (IH Δ)
  | tran _ _ IH1 IH2 => intro Δ; exact EQ.tran (IH1 Δ) (IH2 Δ)
  | @beta_lam' Γ0 Γs e' τ' e σ' He' He =>
    intro Δ
    have h := EQ.beta_lam' (He'.ctx_pad Δ) (He.ctx_pad Δ)
    simp only [List.append_eq] at h
    rwa [binds_single_subst_pad He] at h
  | @eta_lam' Γ0 e τ' σ' He => intro Δ; exact EQ.eta_lam' (He.ctx_pad Δ)
  | @beta_delay Γ0 e τ' n Hlt Hlt' He =>
    intro Δ
    have Hlt'' : n < (Γ0 ++ Δ).length := by simp; omega
    have hpre : TYPED ([] :: List.drop n (Γ0 ++ Δ)) e τ' := by
      rw [List.drop_append_of_le_length (Nat.le_of_lt Hlt')]
      exact He.ctx_pad Δ
    have h := EQ.beta_delay (Γ := Γ0 ++ Δ) n Hlt Hlt'' hpre
    rwa [List.getElem_append_left (Nat.lt_trans Hlt Hlt')] at h
  | @eta_delay Γ0 e τ' He => intro Δ; exact EQ.eta_delay (He.ctx_pad Δ)
  | beta_embed_apply f x h => intro Δ; exact EQ.beta_embed_apply f x (by simp; omega)
  | @unfold' τ' Δ' Γ0 e He =>
    intro Δ
    have h := EQ.unfold' (He.ctx_pad Δ)
    simp only [List.append_eq] at h
    rwa [binds_single_subst_pad He] at h
  | beta_prod_l He He' => intro Δ; exact EQ.beta_prod_l (He.ctx_pad Δ) (He'.ctx_pad Δ)
  | beta_prod_r He He' => intro Δ; exact EQ.beta_prod_r (He.ctx_pad Δ) (He'.ctx_pad Δ)
  | eta_prod He => intro Δ; exact EQ.eta_prod (He.ctx_pad Δ)
  | beta_case_inl Ha Hf Hg =>
    intro Δ; exact EQ.beta_case_inl (Ha.ctx_pad Δ) (Hf.ctx_pad Δ) (Hg.ctx_pad Δ)
  | beta_case_inr Hb Hf Hg =>
    intro Δ; exact EQ.beta_case_inr (Hb.ctx_pad Δ) (Hf.ctx_pad Δ) (Hg.ctx_pad Δ)
  | cong_inl _ IH => intro Δ; exact EQ.cong_inl (IH Δ)
  | cong_inr _ IH => intro Δ; exact EQ.cong_inr (IH Δ)
  | cong_case _ _ _ IHe IHf IHg => intro Δ; exact EQ.cong_case (IHe Δ) (IHf Δ) (IHg Δ)
  | cong_app _ _ IH1 IH2 => intro Δ; exact EQ.cong_app (IH1 Δ) (IH2 Δ)
  | cong_embed_apply _ _ IH1 IH2 => intro Δ; exact EQ.cong_embed_apply (IH1 Δ) (IH2 Δ)
  | cong_pure _ IH => intro Δ; exact EQ.cong_pure (IH Δ)
  | cong_lam' _ IH => intro Δ; exact EQ.cong_lam' (IH Δ)
  | cong_delay h _ IH => intro Δ; exact EQ.cong_delay (by simp; omega) (IH Δ)
  | @cong_adv Γ0 A e e' n Hsub hn IH =>
    intro Δ
    have hnlen : n < Γ0.length := by
      have := typing_stack_len Hsub.typed
      simp only [List.length_drop] at this; omega
    have h := IH Δ
    rw [← List.drop_append_of_le_length (Nat.le_of_lt hnlen)] at h
    exact EQ.cong_adv n h hn
  | cong_fix' _ IH => intro Δ; exact EQ.cong_fix' (IH Δ)
  | cong_pair _ _ IH1 IH2 => intro Δ; exact EQ.cong_pair (IH1 Δ) (IH2 Δ)
  | cong_or _ _ IH1 IH2 => intro Δ; exact EQ.cong_or (IH1 Δ) (IH2 Δ)
  | cong_and _ _ IH1 IH2 => intro Δ; exact EQ.cong_and (IH1 Δ) (IH2 Δ)
  | cong_impl _ _ IH1 IH2 => intro Δ; exact EQ.cong_impl (IH1 Δ) (IH2 Δ)
  | cong_forall' _ IH => intro Δ; exact EQ.cong_forall' (IH Δ)
  | cong_exists' _ IH => intro Δ; exact EQ.cong_exists' (IH Δ)
  | cong_proj1 _ IH => intro Δ; exact EQ.cong_proj1 (IH Δ)
  | cong_proj2 _ IH => intro Δ; exact EQ.cong_proj2 (IH Δ)
  | cong_lift _ IH => intro Δ; exact EQ.cong_lift (IH Δ)
  | cong_eq _ _ IH1 IH2 => intro Δ; exact EQ.cong_eq (IH1 Δ) (IH2 Δ)
  | @ax Γ0 e τ' e' He He' heq =>
    intro Δ
    exact EQ.ax (He.ctx_pad Δ) (He'.ctx_pad Δ) (expr_interp_ctx_pad_congr Δ He He' heq)

end prf
