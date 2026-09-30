module

public import SynthDom.Interp.Global
public import SynthDom.Interp.Univ
public import SynthDom.Interp.Soundness
public import SynthDom.Syntax.Prf.Wrappers

@[expose] public section

section guarded_type

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed

@[irreducible] def GTY.cast.hom {τ σ : TYPE.{i}} (h : ⟦τ⟧ₜ = ⟦σ⟧ₜ) :
    𝟙_ _ ⟶ ⟦⦃τ → σ⦄⟧ₜ := MonoidalClosed.curry' (eqToHom h)

lemma GTY.cast.hom_eq {τ σ : TYPE.{i}} (h : ⟦τ⟧ₜ = ⟦σ⟧ₜ) :
    GTY.cast.hom h = MonoidalClosed.curry' (eqToHom h) := by
  unfold GTY.cast.hom
  rfl

def GTY.cast {τ σ : TYPE.{i}} (h : ⟦τ⟧ₜ = ⟦σ⟧ₜ) : SYNT ⦃τ → σ⦄ :=
  ⟨EXPR.ax ⦃τ → σ⦄ (GTY.cast.hom h), TYPED.ax _ _ (by decide)⟩

@[simp] lemma GTY.cast_expr {τ σ : TYPE.{i}} (h : ⟦τ⟧ₜ = ⟦σ⟧ₜ) :
    (GTY.cast h).expr = EXPR.ax ⦃τ → σ⦄ (MonoidalClosed.curry' (eqToHom h)) := by
  show EXPR.ax _ (GTY.cast.hom h) = _
  rw [GTY.cast.hom_eq]

def GTY.unfold {τ σ : TYPE.{i}} (h : ⟦τ⟧ₜ = ⟦σ⟧ₜ) : SYNT ⦃τ → σ⦄ :=
  GTY.cast h

def GTY.fold {τ σ : TYPE.{i}} (h : ⟦τ⟧ₜ = ⟦σ⟧ₜ) : SYNT ⦃σ → τ⦄ :=
  GTY.cast h.symm

@[simp] lemma GTY.unfold_expr {τ σ : TYPE.{i}} (h : ⟦τ⟧ₜ = ⟦σ⟧ₜ) :
    (GTY.unfold h).expr = EXPR.ax ⦃τ → σ⦄ (MonoidalClosed.curry' (eqToHom h)) := by
  exact GTY.cast_expr h

@[simp] lemma GTY.fold_expr {τ σ : TYPE.{i}} (h : ⟦τ⟧ₜ = ⟦σ⟧ₜ) :
    (GTY.fold h).expr = EXPR.ax ⦃σ → τ⦄ (MonoidalClosed.curry' (eqToHom h.symm)) := by
  exact GTY.cast_expr h.symm

theorem GTY.cast_inverse {τ σ : TYPE.{i}} (h : ⟦τ⟧ₜ = ⟦σ⟧ₜ) :
    GOAL [[]] [[]] [[]] [[]] ⟪∀ x : τ. ([GTY.cast h.symm]ₛ ([GTY.cast h]ₛ x)) = x⟫ := by
  refine GOAL_forall_intro `x ?_
  refine ⟨PROVES.eq_def (EQ.ax ?hl ?hr ?hsem)⟩
  case hl =>
    refine TYPED.app (TYPED.quote [[⦃τ⦄]] Nat.one_pos (GTY.cast h.symm))
      (TYPED.app (TYPED.quote [[⦃τ⦄]] Nat.one_pos (GTY.cast h)) ?_)
    exact TYPED.var_explicit (Γ := [[⦃τ⦄]]) (nm := `x) (0 : Fin 1) (0 : Fin 1)
  case hr =>
    exact TYPED.var_explicit (Γ := [[⦃τ⦄]]) (nm := `x) (0 : Fin 1) (0 : Fin 1)
  case hsem =>
    have hvar : expr_interp [[⦃τ⦄]] (EXPR.var `x 0 0) ⦃τ⦄
        = Part.some ((expr_interp [[⦃τ⦄]] (EXPR.var `x 0 0) ⦃τ⦄).get
            (expr_interp_correct
              (TYPED.var_explicit (Γ := [[⦃τ⦄]]) (nm := `x) (0 : Fin 1) (0 : Fin 1)))) :=
      (Part.some_get _).symm
    rw [quote_eq_expr, quote_eq_expr, GTY.cast_expr, GTY.cast_expr,
      app_curry_interp (A := ⦃σ⦄) (B := ⦃τ⦄) [[⦃τ⦄]] (eqToHom h.symm) _
        (app_curry_interp (A := ⦃τ⦄) (B := ⦃σ⦄) [[⦃τ⦄]]
          (eqToHom h) (EXPR.var `x 0 0) hvar)]
    conv_rhs => rw [hvar]
    congr 1
    rw [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

theorem GTY.unfold_fold {τ σ : TYPE.{i}} (h : ⟦τ⟧ₜ = ⟦σ⟧ₜ) :
    GOAL [[]] [[]] [[]] [[]] ⟪∀ x : σ. ([GTY.unfold h]ₛ ([GTY.fold h]ₛ x)) = x⟫ := by
  simpa only [GTY.unfold, GTY.fold] using GTY.cast_inverse h.symm

theorem GTY.fold_unfold {τ σ : TYPE.{i}} (h : ⟦τ⟧ₜ = ⟦σ⟧ₜ) :
    GOAL [[]] [[]] [[]] [[]] ⟪∀ x : τ. ([GTY.fold h]ₛ ([GTY.unfold h]ₛ x)) = x⟫ := by
  simpa only [GTY.unfold, GTY.fold] using GTY.cast_inverse h

end guarded_type

section global_elements
  open CategoryTheory MonoidalCategory CartesianMonoidalCategory Logic

  universe u

  private lemma interp_eq_pure {Γ : CTX.{u}} {τ : TYPE.{u}} {e1 e2 : EXPR.{u}}
      (h1 : (expr_interp Γ e1 τ).Dom) (h2 : (expr_interp Γ e2 τ).Dom) :
      expr_interp Γ (EXPR.eq τ e1 e2) TYPE.prop
        = pure (interp_eq ((expr_interp Γ e1 τ).get h1) ((expr_interp Γ e2 τ).get h2)) := by
    simp only [expr_interp, bind, Part.Dom.bind h1, Part.Dom.bind h2]

  theorem denote_eq {τ : TYPE.{u}} {L R : EXPR.{u}}
      (H : PROVES [[]] [[]] (EXPR.eq τ L R))
      (dL : (expr_interp [[]] L τ).Dom) (dR : (expr_interp [[]] R τ).Dom) :
      (expr_interp [[]] L τ).get dL = (expr_interp [[]] R τ).get dR :=
    soundness_eq _ _ <| entails_trans _ _ _
      (by simp only [pctx, poctx]; exact conj_intro true_intro true_intro) <|
      Soundness.soundness H
        (by intro k l Ψ' Φ Hk Hl; rcases k with _ | k <;> simp_all)
        [[]] _
        (by simp only [Soundness.interp_pctx, Soundness.interp_pctx_at,
              Soundness.interp_poctx_at]
            exact (Part.bind_some _ _).trans (Part.bind_some _ _))
        (interp_eq_pure dL dR)

  private lemma nil_ren_interp_id {σ : REN} (H : TYPED_REN σ [[]] [[]]) :
      interp_typed_ren H = 𝟙 (⟦([[]] : CTX.{u})⟧ₛ) :=
    NatTrans.ext <| funext fun X => ConcreteCategory.hom_ext _ _ fun _ =>
      @Subsingleton.elim _ (interp_nil_obj_subsingleton X.unop) _ _

  theorem quote_interp {τ : TYPE.{u}} (c : SYNT τ) (k : Nat) (m : Option Nat) :
      expr_interp ([[]] : CTX.{u}) (EXPR.quote c k m) τ = expr_interp [[]] c.expr τ := by
    refine (congrArg (expr_interp ([[]] : CTX.{u}) · τ)
      (quote_reoffset c k m 1 (some 0))).trans
        ((eq_weak _ c.expr τ (TYPED_REN.global_n_weak [[]] (by simp)) c.proof).trans ?_)
    rw [nil_ren_interp_id]
    simp only [Category.id_comp]
    exact Part.map_id' (fun _ => rfl) _

  theorem quote_interp_get {τ : TYPE.{u}} (c : SYNT τ) (k : Nat) (m : Option Nat)
      (d : (expr_interp [[]] (EXPR.quote c k m) τ).Dom) :
      (expr_interp [[]] (EXPR.quote c k m) τ).get d = synt_interp c := by
    simp only [quote_interp] at d ⊢
    rfl

end global_elements

section decoding
  open CategoryTheory MonoidalCategory

  def El (c : SYNT ⦃UNIV⦄) : TYPE := ⦃[classify.hom (Fam c)]ₘ⦄

  def UNIV.prod (c₁ c₂ : SYNT ⦃UNIV⦄) : SYNT ⦃UNIV⦄ := box([UNIV.PROD]ₛ ⟨[c₁]ₛ, [c₂]ₛ⟩)
  def UNIV.sum (c₁ c₂ : SYNT ⦃UNIV⦄) : SYNT ⦃UNIV⦄ := box([UNIV.SUM]ₛ ⟨[c₁]ₛ, [c₂]ₛ⟩)
  def UNIV.later (c : SYNT ⦃UNIV⦄) : SYNT ⦃UNIV⦄ := box([UNIV.LATER]ₛ (delay [c]ₛ))
  def UNIV.arr (c₁ c₂ : SYNT ⦃UNIV⦄) : SYNT ⦃UNIV⦄ := box([UNIV.ARR]ₛ ⟨[c₁]ₛ, [c₂]ₛ⟩)

  theorem DECODES_prod {c₁ c₂ : SYNT ⦃UNIV⦄} {X₁ X₂ : ℐ.{i}}
      (h₁ : DECODES c₁ X₁) (h₂ : DECODES c₂ X₂) : DECODES (UNIV.prod c₁ c₂) (X₁ ⊗ X₂) :=
    DECODES_PROD h₁ h₂
  theorem DECODES_sum {c₁ c₂ : SYNT ⦃UNIV⦄} {X₁ X₂ : ℐ.{i}}
      (h₁ : DECODES c₁ X₁) (h₂ : DECODES c₂ X₂) : DECODES (UNIV.sum c₁ c₂) (ℐ.psum X₁ X₂) :=
    DECODES_SUM h₁ h₂
  theorem DECODES_later {c : SYNT ⦃UNIV⦄} {X : ℐ.{i}} (h : DECODES c X) :
      DECODES (UNIV.later c) (later.obj X) :=
    DECODES_LATER h
  theorem DECODES_arr {c₁ c₂ : SYNT ⦃UNIV⦄} {X₁ X₂ : ℐ.{i}}
      (h₁ : DECODES c₁ X₁) (h₂ : DECODES c₂ X₂) : DECODES (UNIV.arr c₁ c₂) (ℐ.parr X₁ X₂) :=
    DECODES_ARR h₁ h₂

  unseal UNIV in
  theorem DECODES_of_goal {PΓ PΨ} {c c' : SYNT ⦃UNIV⦄} {k k' : Nat} {m m' : Option Nat} {X : ℐ.{i}}
      (H : GOAL PΓ PΨ [[]] [[]] (EXPR.eq ⦃UNIV⦄ (EXPR.quote c k m) (EXPR.quote c' k' m')))
      (hd : DECODES c' X) : DECODES c X := by
    refine DECODES_of_Fam_eq ?_ hd
    have h := denote_eq H.goal (expr_interp_correct (TYPED.eq_inversion H.goal.typed).2.1)
      (expr_interp_correct (TYPED.eq_inversion H.goal.typed).2.2)
    rw [quote_interp_get, quote_interp_get] at h
    simp only [Fam, GlobalElt]
    rw [h]

end decoding

end
