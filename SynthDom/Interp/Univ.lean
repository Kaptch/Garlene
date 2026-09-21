module

public import SynthDom.Semantics.Univ.Temporal
public import SynthDom.Interp.Global
public import SynthDom.Syntax.Expr.Delab

@[expose] public section

section constructors
  open CategoryTheory Functor MonoidalCategory CartesianMonoidalCategory

  @[irreducible] def UNIV : TYPE := ⦃[U]ₘ⦄
  unseal UNIV in @[irreducible] def UNIV.DISCRETE (A : Type i) : SYNT ⦃UNIV⦄ :=
    box([U_discrete A]ₘ)
  unseal UNIV in @[irreducible] def UNIV.LATER : SYNT ⦃▸ UNIV → UNIV⦄ :=
    box([U_later]ₘ)
  unseal UNIV in @[irreducible] def UNIV.PROD : SYNT ⦃UNIV × UNIV → UNIV⦄ :=
    box([U_prod]ₘ)
  @[irreducible] def UNIV.UNIT : SYNT ⦃UNIV⦄ :=
    UNIV.DISCRETE PUnit
  unseal UNIV in @[irreducible] def UNIV.SUM : SYNT ⦃UNIV × UNIV → UNIV⦄ :=
    box([U_sum]ₘ)
  unseal UNIV in @[irreducible] def UNIV.LARR : SYNT ⦃▸ UNIV × ▸ UNIV → UNIV⦄ :=
    box([U_larr]ₘ)
  unseal UNIV UNIV.DISCRETE in
  lemma UNIV.DISCRETE.INTERP {A} : expr_interp Γ (UNIV.DISCRETE A).expr ⦃UNIV⦄ = Part.some (toUnit _ ≫ U_discrete A) := by
    rw [show (UNIV.DISCRETE A).expr = EXPR.ax ⦃UNIV⦄ (U_discrete A) from rfl]
    exact ax_interp (A := ⦃UNIV⦄) Γ (U_discrete A)
  unseal UNIV UNIV.LATER in
  lemma UNIV.LATER.INTERP : expr_interp Γ (UNIV.LATER).expr ⦃▸ UNIV → UNIV⦄ = Part.some (toUnit _ ≫ U_later) := by
    rw [show UNIV.LATER.expr = EXPR.ax ⦃▸ UNIV → UNIV⦄ U_later from rfl]
    exact ax_interp (A := ⦃▸ UNIV → UNIV⦄) Γ U_later
  unseal UNIV UNIV.PROD in
  lemma UNIV.PROD.INTERP : expr_interp Γ (UNIV.PROD).expr ⦃UNIV × UNIV → UNIV⦄ = Part.some (toUnit _ ≫ U_prod) := by
    rw [show UNIV.PROD.expr = EXPR.ax ⦃UNIV × UNIV → UNIV⦄ U_prod from rfl]
    exact ax_interp (A := ⦃UNIV × UNIV → UNIV⦄) Γ U_prod
  unseal UNIV UNIV.UNIT UNIV.DISCRETE in
  lemma UNIV.UNIT.INTERP : expr_interp Γ (UNIV.UNIT).expr ⦃UNIV⦄ = Part.some (toUnit _ ≫ U_discrete PUnit) := by
    simpa only [UNIV.UNIT] using UNIV.DISCRETE.INTERP (Γ := Γ) (A := PUnit)
  unseal UNIV UNIV.SUM in
  lemma UNIV.SUM.INTERP : expr_interp Γ (UNIV.SUM).expr ⦃UNIV × UNIV → UNIV⦄ = Part.some (toUnit _ ≫ U_sum) := by
    rw [show UNIV.SUM.expr = EXPR.ax ⦃UNIV × UNIV → UNIV⦄ U_sum from rfl]
    exact ax_interp (A := ⦃UNIV × UNIV → UNIV⦄) Γ U_sum
  unseal UNIV UNIV.LARR in
  lemma UNIV.LARR.INTERP : expr_interp Γ (UNIV.LARR).expr ⦃▸ UNIV × ▸ UNIV → UNIV⦄ = Part.some (toUnit _ ≫ U_larr) := by
    rw [show UNIV.LARR.expr = EXPR.ax ⦃▸ UNIV × ▸ UNIV → UNIV⦄ U_larr from rfl]
    exact ax_interp (A := ⦃▸ UNIV × ▸ UNIV → UNIV⦄) Γ U_larr

  def U_code (X : ℐ.{i}) : 𝟙_ ℐ.{i + 1} ⟶ U.{i} := classify.inv X

  @[simp] lemma U_code_push (X : ℐ.{i}) : classify.hom (U_code X) = X :=
    CategoryTheory.Iso.inv_hom_id_apply classify X

  unseal UNIV in
  @[irreducible] def UNIV.CODE (τ : TYPE.{i}) : SYNT ⦃UNIV⦄ :=
    box([U_code ⟦τ⟧ₜ]ₘ)

  unseal UNIV UNIV.CODE in
  lemma UNIV.CODE.INTERP {τ : TYPE.{i}} :
      expr_interp Γ (UNIV.CODE τ).expr ⦃UNIV⦄ = Part.some (toUnit _ ≫ U_code ⟦τ⟧ₜ) := by
    rw [show (UNIV.CODE τ).expr = EXPR.ax ⦃UNIV⦄ (U_code ⟦τ⟧ₜ) from rfl]
    exact ax_interp (A := ⦃UNIV⦄) Γ (U_code ⟦τ⟧ₜ)

end constructors

section lang
  open CategoryTheory MonoidalCategory CartesianMonoidalCategory

  unseal UNIV UNIV.DISCRETE in
  lemma globalElt_UNIV_DISCRETE {A : Type i} : GlobalElt (UNIV.DISCRETE A) = U_discrete A :=
    globalElt_ax (UNIV.DISCRETE A) (U_discrete A) rfl

  unseal UNIV UNIV.LATER in
  lemma globalElt_UNIV_LATER : GlobalElt UNIV.LATER = U_later :=
    globalElt_ax UNIV.LATER U_later rfl

  unseal UNIV UNIV.PROD in
  lemma globalElt_UNIV_PROD : GlobalElt UNIV.PROD = U_prod :=
    globalElt_ax UNIV.PROD U_prod rfl

  unseal UNIV UNIV.SUM in
  lemma globalElt_UNIV_SUM : GlobalElt UNIV.SUM = U_sum :=
    globalElt_ax UNIV.SUM U_sum rfl

  unseal UNIV UNIV.LARR in
  lemma globalElt_UNIV_LARR : GlobalElt UNIV.LARR = U_larr :=
    globalElt_ax UNIV.LARR U_larr rfl

  unseal UNIV UNIV.UNIT UNIV.DISCRETE in
  lemma globalElt_UNIV_UNIT : GlobalElt UNIV.UNIT = U_discrete PUnit.{i+1} := by
    unfold UNIV.UNIT
    exact globalElt_UNIV_DISCRETE

  unseal UNIV UNIV.CODE in
  lemma globalElt_UNIV_CODE {τ : TYPE.{i}} : GlobalElt (UNIV.CODE τ) = U_code ⟦τ⟧ₜ :=
    globalElt_ax (UNIV.CODE τ) (U_code ⟦τ⟧ₜ) rfl

end lang

section decodes
  open CategoryTheory MonoidalCategory CartesianMonoidalCategory

  unseal UNIV in
  def Fam (c : SYNT ⦃UNIV⦄) : 𝟙_ ℐ.{i + 1} ⟶ U.{i} := GlobalElt c

  def DECODES (c : SYNT ⦃UNIV⦄) (X : ℐ.{i}) : Prop := classify.hom (Fam c) = X

  unseal UNIV in
  lemma DECODES_DISCRETE (A : Type i) : DECODES (UNIV.DISCRETE A) (discrete.obj A) := by
    show classify.hom (Fam (UNIV.DISCRETE A)) = _
    rw [show Fam (UNIV.DISCRETE A) = U_discrete A from globalElt_UNIV_DISCRETE]
    exact U_discrete_push

  unseal UNIV in
  lemma DECODES_UNIT : DECODES UNIV.UNIT (discrete.obj PUnit.{i+1}) := by
    show classify.hom (Fam UNIV.UNIT) = _
    rw [show Fam UNIV.UNIT = U_discrete PUnit from globalElt_UNIV_UNIT]
    exact U_discrete_push

  unseal UNIV in
  lemma DECODES_CODE (τ : TYPE.{i}) : DECODES (UNIV.CODE τ) ⟦τ⟧ₜ := by
    show classify.hom (Fam (UNIV.CODE τ)) = _
    rw [show Fam (UNIV.CODE τ) = U_code ⟦τ⟧ₜ from globalElt_UNIV_CODE]
    exact U_code_push _

  unseal UNIV in
  lemma DECODES_PROD {c₁ c₂ : SYNT ⦃UNIV⦄} {X₁ X₂ : ℐ.{i}}
      (h₁ : DECODES c₁ X₁) (h₂ : DECODES c₂ X₂) :
      DECODES (box([UNIV.PROD]ₛ ⟨[c₁]ₛ, [c₂]ₛ⟩)) (X₁ ⊗ X₂) := by
    have key : Fam (box([UNIV.PROD]ₛ ⟨[c₁]ₛ, [c₂]ₛ⟩))
        = CartesianMonoidalCategory.lift (Fam c₁) (Fam c₂) ≫ MonoidalClosed.uncurry' U_prod := by
      have h := globalElt_app_pair UNIV.PROD c₁ c₂
      rw [globalElt_UNIV_PROD] at h
      simp only [Fam, GlobalElt] at h ⊢
      exact h
    unfold DECODES; rw [key, U_prod_push, h₁, h₂]

  unseal UNIV in
  lemma DECODES_SUM {c₁ c₂ : SYNT ⦃UNIV⦄} {X₁ X₂ : ℐ.{i}}
      (h₁ : DECODES c₁ X₁) (h₂ : DECODES c₂ X₂) :
      DECODES (box([UNIV.SUM]ₛ ⟨[c₁]ₛ, [c₂]ₛ⟩)) (ℐ.psum X₁ X₂) := by
    have key : Fam (box([UNIV.SUM]ₛ ⟨[c₁]ₛ, [c₂]ₛ⟩))
        = CartesianMonoidalCategory.lift (Fam c₁) (Fam c₂) ≫ MonoidalClosed.uncurry' U_sum := by
      have h := globalElt_app_pair UNIV.SUM c₁ c₂
      rw [globalElt_UNIV_SUM] at h
      simp only [Fam, GlobalElt] at h ⊢
      exact h
    unfold DECODES; rw [key, U_sum_push, h₁, h₂]

  unseal UNIV in
  lemma DECODES_LATER {c : SYNT ⦃UNIV⦄} {X : ℐ.{i}} (h : DECODES c X) :
      DECODES (box([UNIV.LATER]ₛ (delay [c]ₛ))) (later.obj X) := by
    have key : Fam (box([UNIV.LATER]ₛ (delay [c]ₛ)))
        = (Fam c ≫ next.app U) ≫ MonoidalClosed.uncurry' U_later := by
      have h := globalElt_app_delay UNIV.LATER c
      rw [globalElt_UNIV_LATER] at h
      simp only [Fam, GlobalElt] at h ⊢
      exact h
    unfold DECODES; rw [key, Category.assoc, U_later_push, h]

  unseal UNIV in
  lemma DECODES_LARR {c₁ c₂ : SYNT ⦃UNIV⦄} {X₁ X₂ : ℐ.{i}}
      (h₁ : DECODES c₁ X₁) (h₂ : DECODES c₂ X₂) :
      DECODES (box([UNIV.LARR]ₛ ⟨delay [c₁]ₛ, delay [c₂]ₛ⟩)) (later.obj (ℐ.parr X₁ X₂)) := by
    have key : Fam (box([UNIV.LARR]ₛ ⟨delay [c₁]ₛ, delay [c₂]ₛ⟩))
        = CartesianMonoidalCategory.lift (Fam c₁ ≫ next.app U) (Fam c₂ ≫ next.app U)
            ≫ MonoidalClosed.uncurry' U_larr := by
      have h := globalElt_app_delayed_pair UNIV.LARR c₁ c₂
      rw [globalElt_UNIV_LARR] at h
      simp only [Fam, GlobalElt] at h ⊢
      exact h
    unfold DECODES; rw [key, U_larr_push, h₁, h₂]

  lemma DECODES_refl (c : SYNT ⦃UNIV⦄) : DECODES c (classify.hom (Fam c)) := rfl

  lemma DECODES_of_Fam_eq {c c' : SYNT ⦃UNIV⦄} {X : ℐ.{i}} (h : Fam c = Fam c')
      (hd : DECODES c' X) : DECODES c X := by
    unfold DECODES; rw [h]; exact hd

  unseal UNIV in
  lemma DECODES_congr {c c' : SYNT ⦃UNIV⦄} {X : ℐ.{i}} (h : c.expr = c'.expr)
      (hd : DECODES c' X) : DECODES c X :=
    DECODES_of_Fam_eq (show _root_.Fam c = _root_.Fam c' from globalElt_congr h) hd

end decodes

end
