module

public import SynthDom.Syntax.Prf.Weaken.Equality

@[expose] public section

section prf
open Lean

def REN.TickPres (σ : REN) : Prop := ∀ n, offset_ren σ n = n

theorem REN.TickPres.cons {σ : REN} (h : σ.TickPres) : σ.cons.TickPres := by
  intro n; cases n with
  | zero => rfl
  | succ n' => rw [off_cons_succ]; exact h (n'+1)

theorem REN.TickPres.local_weaken {σ : REN} (h : σ.TickPres) : σ.local_weaken.TickPres := by
  intro n; cases n with
  | zero => rfl
  | succ n' => rw [off_lw_succ]; exact h (n'+1)

theorem REN.TickPres.global_lift {σ : REN} (h : σ.TickPres) : σ.global_lift.TickPres := by
  intro n; cases n with
  | zero => rfl
  | succ n' => rw [off_global_lift_succ]; rw [h n']

theorem REN.TickPres.cut {σ : REN} (h : σ.TickPres) (k : Nat) : (cut_ren σ k).TickPres := by
  intro n
  have hcut := offset_cut σ k n
  rw [h k, h (k + n)] at hcut
  omega

theorem TickPres.local_weaken_list (k : Nat) : (local_weaken_list k REN.id).TickPres := by
  induction k with
  | zero => intro n; exact off_id n
  | succ k IH => exact IH.local_weaken

theorem weaken_pctx_length (σ : REN) (Ψ : PCTX.{i}) :
    (weaken_pctx σ Ψ).length = Ψ.length := by
  simp [weaken_pctx]

theorem weaken_pctx_nil (σ : REN) : weaken_pctx σ ([] : PCTX.{i}) = [] := rfl

theorem weaken_pctx_cons (σ : REN) (Ψ0 : POCTX.{i}) (Ψs : PCTX.{i}) :
    weaken_pctx σ (Ψ0 :: Ψs)
      = (Ψ0.map (fun p => weaken p σ)) :: weaken_pctx (cut_ren σ 1) Ψs := by
  simp only [weaken_pctx, List.mapIdx_cons, cut_ren_zero]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_mapIdx]
  congr 2
  rw [cut_cut, Nat.add_comm]

theorem weaken_pctx_getElem? (σ : REN) (Ψ : PCTX.{i}) (n : Nat) :
    (weaken_pctx σ Ψ)[n]? = (Ψ[n]?).map (fun Ψn => Ψn.map (fun p => weaken p (cut_ren σ n))) := by
  simp only [weaken_pctx, List.getElem?_mapIdx]

theorem comp_tickpres {x y : REN} (h : (REN.comp x y).TickPres) : x.TickPres ∧ y.TickPres := by
  have hx : x.TickPres := by
    intro n
    have hn := h n; rw [offset_comp_all] at hn
    have h1 := offset_ren_ge x n
    have h2 := offset_ren_ge y (offset_ren x n)
    omega
  refine ⟨hx, fun n => ?_⟩
  have hn := h n; rw [offset_comp_all, hx n] at hn; exact hn

theorem intro_wrap_cons (Ψ0 : POCTX.{i}) (Ψs : PCTX.{i}) :
    intro_wrap (Ψ0 :: Ψs) = intro_wrap' Ψ0 :: Ψs := rfl

theorem weaken_pctx_intro_wrap (σ : REN) (Ψ : PCTX.{i}) :
    weaken_pctx σ.cons (intro_wrap Ψ) = intro_wrap (weaken_pctx σ Ψ) := by
  cases Ψ with
  | nil => rfl
  | cons Ψ0 Ψs =>
    rw [weaken_pctx_cons σ Ψ0 Ψs, intro_wrap_cons, intro_wrap_cons, weaken_pctx_cons]

    congr 1

    simp only [intro_wrap']
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro p _
    simp only [Function.comp_apply, octx_wk]
    rw [weaken_comp, weaken_comp]
    exact weaken_congr p (shift_cons σ)

theorem weaken_pctx_lift (σ : REN) (Ψ : PCTX.{i}) :
    weaken_pctx σ.global_lift ([] :: Ψ) = [] :: weaken_pctx σ Ψ := by
  rw [weaken_pctx_cons]
  simp only [List.map_nil]
  congr 1
  rw [cut_global_lift_succ, cut_ren_zero]

private theorem tp_of_lw {σ : REN} (h : σ.local_weaken.TickPres) : σ.TickPres :=
  fun n => match n with
  | 0 => offset_ren_zero σ
  | n + 1 => by have := h (n + 1); rwa [off_lw_succ] at this

private theorem tp_of_cons {σ : REN} (h : σ.cons.TickPres) : σ.TickPres :=
  fun n => match n with
  | 0 => offset_ren_zero σ
  | n + 1 => by have := h (n + 1); rwa [off_cons_succ] at this

private theorem tick_pres_of_global_lift {σ : REN} (h : σ.global_lift.TickPres) : σ.TickPres :=
  fun n => match n with
  | 0 => offset_ren_zero σ
  | n + 1 => by have := h (n + 2); rw [off_global_lift_succ] at this; omega

private theorem tick_pres_ren_len {σ : REN} {Δ Γ : CTX.{i}}
    (hσ : TYPED_REN σ Δ Γ) (htp : REN.TickPres σ) : Δ.length = Γ.length := by
  induction hσ with
  | id => rfl
  | @comp σ' σ'' _ _ _ _ _ IH1 IH2 =>
    obtain ⟨htp1, htp2⟩ := comp_tickpres htp
    exact (IH2 htp2).trans (IH1 htp1)
  | local_weaken _ _ IH => exact IH (tp_of_lw htp)
  | cons _ _ IH => exact IH (tp_of_cons htp)
  | global_lift _ IH => simp only [List.length_cons]; exact congrArg (· + 1) (IH (tick_pres_of_global_lift htp))
  | @global_shift σ_inner _ _ Ψ_inner n hn _ IH =>

    have htp1 := htp 1

    have hoff : offset_ren (REN.global_shift n σ_inner) 1 = n + offset_ren σ_inner 1 := rfl
    rw [hoff] at htp1
    have hpos : 0 < offset_ren σ_inner 1 := offset_succ_pos σ_inner 0
    have hn0 : n = 0 := by omega
    subst hn0
    have hΨ : Ψ_inner = [] := List.eq_nil_of_length_eq_zero (hn.symm)
    subst hΨ; simp only [List.nil_append]

    exact IH (fun m => by
      have := htp m
      try simp only [offset_ren] at this ⊢
      cases m with
      | zero => simp
      | succ m' => simpa using this)

theorem PROVES.weaken {Γ : CTX.{i}} {Ψ : PCTX.{i}} {Φ : EXPR.{i}} (H : PROVES Γ Ψ Φ) :
    ∀ {Δ : CTX.{i}} {σ : REN}, REN.TickPres σ → TYPED_REN σ Δ Γ →
    PROVES Δ (weaken_pctx σ Ψ) (weaken Φ σ) := by
  induction H with
  | @asm Ψ Ψ' Φ Γ n m Hn Hm Htyped Hlen =>
    intro Δ σ Htp Hσ
    rw [weaken_comp]
    have hoff : offset_ren σ n = n := Htp n
    rw [weaken_congr Φ (asm_nat n σ), hoff, ← weaken_comp]

    have Hn' : (weaken_pctx σ Ψ)[n]?
        = some (Ψ'.map (fun p => _root_.weaken p (cut_ren σ n))) := by
      rw [weaken_pctx_getElem?, Hn]; rfl
    have Hm' : (Ψ'.map (fun p => _root_.weaken p (cut_ren σ n)))[m]?
        = some (_root_.weaken Φ (cut_ren σ n)) := by
      rw [List.getElem?_map, Hm]; rfl
    have Htyped' : TYPED Δ (_root_.weaken (_root_.weaken Φ (cut_ren σ n))
        (REN.global_shift n REN.id)) TYPE.prop := by
      have h := weaken_typing Htyped Hσ
      rw [weaken_comp, weaken_congr Φ (asm_nat n σ), hoff, ← weaken_comp] at h; exact h
    exact PROVES.asm n m Hn' Hm' (Htyped := Htyped')
      (Hlen := by rw [weaken_pctx_length]; exact (tick_pres_ren_len Hσ Htp).trans Hlen)
  | true_intro Hpos Hlen =>
    intro Δ σ Htp Hσ
    show PROVES Δ (weaken_pctx σ _) EXPR.true
    exact PROVES.true_intro (Hpos := ren_len' σ Hσ)
      (Hlen := by rw [weaken_pctx_length]; exact (tick_pres_ren_len Hσ Htp).trans Hlen)
  | and_intro _ _ IH1 IH2 =>
    intro Δ σ Htp Hσ; exact PROVES.and_intro (IH1 Htp Hσ) (IH2 Htp Hσ)
  | and_elim_l _ IH =>
    intro Δ σ Htp Hσ; exact PROVES.and_elim_l (IH Htp Hσ)
  | and_elim_r _ IH =>
    intro Δ σ Htp Hσ; exact PROVES.and_elim_r (IH Htp Hσ)
  | or_intro_l Htyped _ IH =>
    intro Δ σ Htp Hσ
    exact PROVES.or_intro_l (Htyped := weaken_typing Htyped Hσ) (IH Htp Hσ)
  | or_intro_r Htyped _ IH =>
    intro Δ σ Htp Hσ
    exact PROVES.or_intro_r (Htyped := weaken_typing Htyped Hσ) (IH Htp Hσ)
  | @or_elim Γ P Ψ0 Ψs Q Φ _ _ _ IH1 IH2 IH3 =>
    intro Δ σ Htp Hσ
    have h1 := IH1 Htp Hσ
    have h2 := IH2 Htp Hσ
    have h3 := IH3 Htp Hσ
    rw [weaken_pctx_cons] at h1 h2 h3
    simp only [List.map_cons] at h1 h2
    rw [weaken_pctx_cons]
    exact PROVES.or_elim h1 h2 h3
  | @impl_intro Γ Φ1 Ψ0 Ψs Φ2 Htyped _ IH =>
    intro Δ σ Htp Hσ
    have h := IH Htp Hσ
    rw [weaken_pctx_cons] at h
    simp only [List.map_cons] at h
    rw [weaken_pctx_cons]
    exact PROVES.impl_intro (Htyped := weaken_typing Htyped Hσ) h
  | impl_elim _ _ IH1 IH2 =>
    intro Δ σ Htp Hσ
    exact PROVES.impl_elim (IH1 Htp Hσ) (IH2 Htp Hσ)
  | @forall_intro' τ Γ Γs Ψ Φ _ IH =>
    intro Δ σ Htp Hσ
    obtain ⟨Δ0, Δs, rfl⟩ := ren_dom_cons_shape Hσ
    have h := IH Htp.cons (TYPED_REN.cons τ Hσ)
    rw [weaken_pctx_intro_wrap] at h
    exact PROVES.forall_intro' h
  | @forall_elim' Γ Γs Ψ τ Φ e HΦ H He IH =>
    intro Δ σ Htp Hσ
    obtain ⟨Δ0, Δs, rfl⟩ := ren_dom_cons_shape Hσ
    have h := IH Htp Hσ
    have key := PROVES.forall_elim' τ (_root_.weaken Φ σ.cons) (_root_.weaken e σ)
      (weaken_typing HΦ (TYPED_REN.cons τ Hσ)) h (weaken_typing He Hσ)
    rw [weaken_single_subst HΦ He Hσ]
    exact key
  | lift_intro Hpos _ IH =>
    intro Δ σ Htp Hσ
    obtain ⟨Δ0, Δs, rfl⟩ := ren_dom_cons_shape Hσ
    have h := IH Htp.global_lift (TYPED_REN.global_lift Hσ)
    rw [weaken_pctx_lift] at h
    exact PROVES.lift_intro (Hpos := ren_len' σ Hσ) h
  | @later_mono Γ Ψ P Q Hpos H1 H2 IH1 IH2 =>
    intro Δ σ Htp Hσ
    obtain ⟨Δ0, Δs, rfl⟩ := ren_dom_cons_shape Hσ
    have h1 := IH1 Htp Hσ
    have h2 := IH2 Htp.global_lift (TYPED_REN.global_lift Hσ)
    rw [weaken_pctx_cons] at h2
    simp only [List.map_cons, List.map_nil] at h2
    rw [cut_global_lift_succ, cut_ren_zero] at h2
    exact PROVES.later_mono (Hpos := by simp) h1 h2
  | later_and _ _ IH1 IH2 =>
    intro Δ σ Htp Hσ

    exact PROVES.later_and (IH1 Htp Hσ) (IH2 Htp Hσ)
  | later_or _ IH =>
    intro Δ σ Htp Hσ
    exact PROVES.later_or (IH Htp Hσ)
  | @loeb_ind Γ Φ Ψs Φs _ IH =>
    intro Δ σ Htp Hσ
    have h := IH Htp Hσ
    rw [weaken_pctx_cons] at h
    simp only [List.map_cons] at h

    have hhead : _root_.weaken (.lift (.delay (_root_.weaken Φ (REN.global_shift 1 REN.id)))) σ
        = .lift (.delay (_root_.weaken (_root_.weaken Φ σ) (REN.global_shift 1 REN.id))) := by
      show (_root_.weaken (_root_.weaken Φ (REN.global_shift 1 REN.id)) σ.global_lift).delay.lift
        = (_root_.weaken (_root_.weaken Φ σ) (REN.global_shift 1 REN.id)).delay.lift
      rw [weaken_comp, weaken_comp, weaken_congr Φ (global_shift_lift_comm σ).symm]
    rw [hhead] at h
    rw [weaken_pctx_cons]
    exact PROVES.loeb_ind h
  | @eq_def Γ τ e1 e2 Ψ Heq Hlen =>
    intro Δ σ Htp Hσ
    exact PROVES.eq_def (Heq.weaken Hσ)
      (Hlen := by rw [weaken_pctx_length]; exact (tick_pres_ren_len Hσ Htp).trans Hlen)
  | eq_elim HΦ He1 He2 Heq _ IH1 IH2 =>
    intro Δ σ Htp Hσ
    obtain ⟨Δ0, Δs, rfl⟩ := ren_dom_cons_shape Hσ
    have h1 := IH1 Htp Hσ
    have h2 := IH2 Htp Hσ
    rw [weaken_single_subst HΦ He1 Hσ] at h2
    have key := PROVES.eq_elim (weaken_typing HΦ (TYPED_REN.cons _ Hσ))
      (weaken_typing He1 Hσ) (weaken_typing He2 Hσ) h1 h2
    rw [← weaken_single_subst HΦ He2 Hσ] at key
    exact key
  | false_elim P Htyped _ IH =>
    intro Δ σ Htp Hσ
    exact PROVES.false_elim _ (Htyped := weaken_typing Htyped Hσ) (IH Htp Hσ)
  | @pure_intro Pr Γ Ψ p Htyped Hlen =>
    intro Δ σ Htp Hσ
    exact PROVES.pure_intro p (Htyped := weaken_typing Htyped Hσ)
      (Hlen := by rw [weaken_pctx_length]; exact (tick_pres_ren_len Hσ Htp).trans Hlen)
  | delay_eq H IH =>
    intro Δ σ Htp Hσ

    exact PROVES.delay_eq (IH Htp Hσ)
  | inl_inj H IH =>
    intro Δ σ Htp Hσ

    exact PROVES.inl_inj (IH Htp Hσ)
  | inr_inj H IH =>
    intro Δ σ Htp Hσ
    exact PROVES.inr_inj (IH Htp Hσ)
  | inl_inr_disj H IH =>
    intro Δ σ Htp Hσ
    exact PROVES.inl_inr_disj (IH Htp Hσ)
  | @exists_intro' Γ Γs Ψ τ Φ e HΦ He H IH =>
    intro Δ σ Htp Hσ
    obtain ⟨Δ0, Δs, rfl⟩ := ren_dom_cons_shape Hσ
    have h := IH Htp Hσ
    rw [weaken_single_subst HΦ He Hσ] at h
    exact PROVES.exists_intro' τ (_root_.weaken Φ σ.cons) (_root_.weaken e σ)
      (weaken_typing HΦ (TYPED_REN.cons τ Hσ)) (weaken_typing He Hσ) h
  | @forall_intro_points Γ Γs Ψ A Φ HΦ Hlen Hfam IH =>
    intro Δ σ Htp Hσ
    obtain ⟨Δ0, Δs, rfl⟩ := ren_dom_cons_shape Hσ
    refine PROVES.forall_intro_points A (_root_.weaken Φ σ.cons)
      (weaken_typing HΦ (TYPED_REN.cons (TYPE.embed A) Hσ))
      (by rw [weaken_pctx_length]; exact (tick_pres_ren_len Hσ Htp).trans Hlen) (fun a => ?_)
    have h := IH a Htp Hσ
    rw [weaken_single_subst HΦ (TYPED.embed (by simp)) Hσ] at h
    exact h
  | @exists_elim' Γ Γs Ψ Ψs τ Φ Q HQ Hex Hbr IH1 IH2 =>
    intro Δ σ Htp Hσ
    obtain ⟨Δ0, Δs, rfl⟩ := ren_dom_cons_shape Hσ
    have h1 := IH1 Htp Hσ
    have h2 := IH2 Htp.cons (TYPED_REN.cons τ Hσ)
    rw [weaken_pctx_cons] at h1 h2
    rw [weaken_pctx_cons]
    simp only [List.map_cons] at h1 h2

    have hcomm : _root_.weaken (_root_.weaken Q octx_wk) σ.cons
        = _root_.weaken (_root_.weaken Q σ) octx_wk := by
      rw [weaken_comp, weaken_comp]; exact weaken_congr Q (shift_cons σ)
    have hiw : (intro_wrap' Ψ).map (fun p => _root_.weaken p σ.cons)
        = intro_wrap' (Ψ.map (fun p => _root_.weaken p σ)) := by
      simp only [intro_wrap', List.map_map]
      apply List.map_congr_left
      intro p _
      simp only [Function.comp_apply, octx_wk]
      rw [weaken_comp, weaken_comp]; exact weaken_congr p (shift_cons σ)
    rw [hcomm, hiw] at h2
    exact PROVES.exists_elim' (weaken_typing HQ Hσ) h1 h2
  | @sum_elim Γ Γs Ψ Ψs A B Φ e HΦ He _ _ IHinl IHinr =>
    intro Δ σ Htp Hσ
    obtain ⟨Δ0, Δs, rfl⟩ := ren_dom_cons_shape Hσ

    have h1 := IHinl Htp.cons (TYPED_REN.cons A Hσ)
    have h2 := IHinr Htp.cons (TYPED_REN.cons B Hσ)
    rw [weaken_pctx_cons] at h1 h2
    rw [weaken_pctx_cons]
    simp only [List.map_cons] at h1 h2

    have hcomm : ∀ X : EXPR.{i}, _root_.weaken (_root_.weaken X octx_wk) σ.cons
        = _root_.weaken (_root_.weaken X σ) octx_wk := by
      intro X; rw [weaken_comp, weaken_comp]; exact weaken_congr X (shift_cons σ)

    have hiw : (intro_wrap' Ψ).map (fun p => _root_.weaken p σ.cons)
        = intro_wrap' (Ψ.map (fun p => _root_.weaken p σ)) := by
      simp only [intro_wrap', List.map_map]
      apply List.map_congr_left
      intro p _
      simp only [Function.comp_apply, octx_wk]
      rw [weaken_comp, weaken_comp]; exact weaken_congr p (shift_cons σ)

    have hvar : _root_.weaken (EXPR.var' 0 0) σ.cons = EXPR.var' 0 0 := rfl
    rw [hcomm Φ, hiw] at h1 h2

    have heq_inl : _root_.weaken (EXPR.eq (TYPE.sum A B) (_root_.weaken e octx_wk) (EXPR.inl B (EXPR.var' 0 0))) σ.cons
        = EXPR.eq (TYPE.sum A B) (_root_.weaken (_root_.weaken e σ) octx_wk) (EXPR.inl B (EXPR.var' 0 0)) := by
      show EXPR.eq (TYPE.sum A B) (_root_.weaken (_root_.weaken e octx_wk) σ.cons)
          (EXPR.inl B (_root_.weaken (EXPR.var' 0 0) σ.cons)) = _
      rw [hcomm e, hvar]
    have heq_inr : _root_.weaken (EXPR.eq (TYPE.sum A B) (_root_.weaken e octx_wk) (EXPR.inr A (EXPR.var' 0 0))) σ.cons
        = EXPR.eq (TYPE.sum A B) (_root_.weaken (_root_.weaken e σ) octx_wk) (EXPR.inr A (EXPR.var' 0 0)) := by
      show EXPR.eq (TYPE.sum A B) (_root_.weaken (_root_.weaken e octx_wk) σ.cons)
          (EXPR.inr A (_root_.weaken (EXPR.var' 0 0) σ.cons)) = _
      rw [hcomm e, hvar]
    rw [heq_inl] at h1
    rw [heq_inr] at h2
    exact PROVES.sum_elim (_root_.weaken e σ) (weaken_typing HΦ Hσ) (weaken_typing He Hσ) h1 h2

end prf
