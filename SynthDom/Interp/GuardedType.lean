module

public import SynthDom.Interp.Global
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

end
