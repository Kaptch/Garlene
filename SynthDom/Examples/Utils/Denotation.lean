module

public import SynthDom
public import SynthDom.Examples.Delay.Base
public import SynthDom.Examples.Utils.Funext
@[expose] public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Logic

section denotation

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

def denoteHom {σ τ : TYPE.{u}} (e : SYNT ⦃σ → τ⦄) : (⟦σ⟧ₜ : ℐ.{u}) ⟶ ⟦τ⟧ₜ :=
  (ρ_ _).inv ≫ MonoidalClosed.uncurry (GlobalElt e)

end denotation

section capstone

universe u

unseal EXPR.lam EXPR.var in
theorem denoteHom_idfun (τ : TYPE.{u}) : denoteHom (idfun τ) = 𝟙 (⟦τ⟧ₜ : ℐ.{u}) := by
  have h1 : getElem? (((τ :: []) :: []) : CTX.{u}) 0 = some (τ :: []) := by rfl
  have h2 : getElem? ((τ :: []) : OCTX.{u}) 0 = some τ := by rfl
  have hsem : synt_interp (idfun τ) = interp_lam (interp_var 0 0 h1 h2) :=
    Part.get_eq_iff_eq_some.mpr <| by
      unfold idfun
      show expr_interp [[]] (EXPR.lam' τ (EXPR.var' 0 0)) (TYPE.arr τ τ) = _
      simp only [expr_interp]
      rw [Part.assert_pos (by simp), Part.assert_pos (by simp)]
      simp
  unfold denoteHom GlobalElt
  rw [hsem, interp_lam]
  refine ((congrArg ((ρ_ (⟦τ⟧ₜ : ℐ.{u})).inv ≫ ·)
    ((MonoidalClosed.uncurry_natural_left _ _).trans
      (congrArg (((⟦τ⟧ₜ : ℐ.{u}) ◁
          CartesianMonoidalCategory.lift (𝟙 (𝟙_ ℐ.{u})) earlier_terminal.inv) ≫ ·)
        (MonoidalClosed.uncurry_curry _))))).trans ?_
  simp only [interp_var]
  simp [ctx_proj, octx_proj, interp_ctx, interp_octx]

theorem Delay.map_id_denotation (A : TYPE.{u}) :
    denoteHom (box([Delay.map A A]ₛ [idfun A]ₛ)) = 𝟙 (⟦Delay A⟧ₜ : ℐ.{u}) := by
  obtain ⟨H⟩ := Delay.map_id' A
  obtain ⟨-, HL, HR⟩ := TYPED.eq_inversion (PROVES.typed H)
  unfold denoteHom GlobalElt
  rw [show synt_interp (box([Delay.map A A]ₛ [idfun A]ₛ)) = synt_interp (idfun (Delay A)) from
    (denote_eq H (expr_interp_correct HL) (expr_interp_correct HR)).trans
      (quote_interp_get _ _ _ _)]
  exact denoteHom_idfun (Delay A)

end capstone

section interface

universe u

def interpNilIso : 𝟙_ ℐ.{u} ≅ (⟦[[]]⟧ₛ : ℐ.{u}) where
  hom := CartesianMonoidalCategory.lift (𝟙 _) earlier_terminal.inv
  inv := CartesianMonoidalCategory.toUnit _
  hom_inv_id := CartesianMonoidalCategory.toUnit_unique _ _
  inv_hom_id := hom_to_nil_unique _ _

theorem denoteHom_eq_uncurry' {σ τ : TYPE.{u}} (e : SYNT ⦃σ → τ⦄) :
    denoteHom e = MonoidalClosed.uncurry' (GlobalElt e) := rfl

def SYNT.ofHom (σ τ : TYPE.{u}) (k : (⟦σ⟧ₜ : ℐ.{u}) ⟶ ⟦τ⟧ₜ) : SYNT ⦃σ → τ⦄ :=
  ⟨.ax ⦃σ → τ⦄ (MonoidalClosed.curry' k), .ax _ _ (by simp)⟩

theorem globalElt_ofHom {σ τ : TYPE.{u}} (k : (⟦σ⟧ₜ : ℐ.{u}) ⟶ ⟦τ⟧ₜ) :
    GlobalElt (SYNT.ofHom σ τ k) = MonoidalClosed.curry' k :=
  (congrArg (CartesianMonoidalCategory.lift (𝟙 _) earlier_terminal.inv ≫ ·)
      (synt_interp_eq_of_expr_interp _ (ax_interp _ _))).trans <|
    (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ MonoidalClosed.curry' k) interpNilIso.hom_inv_id).trans
        (Category.id_comp _)

@[simp] theorem denoteHom_ofHom {σ τ : TYPE.{u}} (k : (⟦σ⟧ₜ : ℐ.{u}) ⟶ ⟦τ⟧ₜ) :
    denoteHom (SYNT.ofHom σ τ k) = k := by
  rw [denoteHom_eq_uncurry', globalElt_ofHom, MonoidalClosed.uncurry'_curry']

theorem globalElt_eq_of_denoteHom {σ τ : TYPE.{u}} {e₁ e₂ : SYNT ⦃σ → τ⦄}
    (h : denoteHom e₁ = denoteHom e₂) : GlobalElt e₁ = GlobalElt e₂ :=
  (MonoidalClosed.curry'_uncurry' (GlobalElt e₁)).symm.trans <|
    (congrArg MonoidalClosed.curry' h).trans (MonoidalClosed.curry'_uncurry' (GlobalElt e₂))

theorem synt_interp_eq_of_globalElt {τ : TYPE.{u}} {e₁ e₂ : SYNT τ}
    (h : GlobalElt e₁ = GlobalElt e₂) : synt_interp e₁ = synt_interp e₂ :=
  (Iso.cancel_iso_hom_left interpNilIso _ _).mp h

theorem denoteHom_congr {σ τ : TYPE.{u}} {e₁ e₂ : SYNT ⦃σ → τ⦄}
    (H : PROVES [[]] [[]] (.eq ⦃σ → τ⦄ e₁.expr e₂.expr)) :
    denoteHom e₁ = denoteHom e₂ := by
  unfold denoteHom GlobalElt
  rw [show synt_interp e₁ = synt_interp e₂ from
    denote_eq H (expr_interp_correct e₁.proof) (expr_interp_correct e₂.proof)]

end interface

section application_interp

theorem interp_quote_toUnit {τ : TYPE.{u}} {Γ : CTX.{u}} (HΓ : 0 < Γ.length)
    (P : SYNT τ) (n : Nat) (m : Option Nat) :
    expr_interp Γ (EXPR.quote P n m) τ
      = Part.some (toUnit ⟦Γ⟧ₛ ≫ GlobalElt P) := by
  refine ((congrArg (expr_interp Γ · τ)
    (quote_reoffset P n m Γ.length (Γ.getLast?.map List.length))).trans
      (eq_weak _ P.expr τ (TYPED_REN.global_n_weak Γ HΓ) P.proof)).trans ?_
  rw [expr_interp_eq_some P, Part.map_some]
  exact congrArg Part.some
    ((congrArg (· ≫ synt_interp P)
      (hom_to_nil_unique _ (toUnit _ ≫ interpNilIso.hom))).trans (Category.assoc _ _ _))

theorem interp_app_quote {σ τ : TYPE.{u}} {Γ : CTX.{u}} (HΓ : 0 < Γ.length)
    (P : SYNT ⦃σ → τ⦄) (n : Nat) (m : Option Nat) {a : EXPR.{u}}
    {g : ⟦Γ⟧ₛ ⟶ (⟦σ⟧ₜ : ℐ.{u})} (ha : expr_interp Γ a σ = Part.some g) :
    expr_interp Γ (.app σ (EXPR.quote P n m) a) τ = Part.some (g ≫ denoteHom P) := by
  show (expr_interp Γ (EXPR.quote P n m) (TYPE.arr σ τ)).bind
      (fun e1 => (expr_interp Γ a σ).bind fun e2 => Part.some (interp_app e1 e2)) = _
  rw [interp_quote_toUnit HΓ P n m, ha, Part.bind_some, Part.bind_some]
  exact congrArg Part.some (const_app g (GlobalElt P))

theorem interp_var_head (σ : TYPE.{u}) :
    expr_interp (((σ :: []) :: []) : CTX.{u}) (.var' 0 0) σ
      = Part.some (interp_var 0 0 rfl rfl) := by
  show Part.assert _ (fun Hn => Part.assert _ fun Hm =>
    pure (interp_var 0 0 (getElem?_pos _ 0 Hn) Hm)) = _
  rw [Part.assert_pos (by simp), Part.assert_pos (by simp)]
  rfl

theorem interp_var_head' (nm : Lean.Name) (σ : TYPE.{u}) :
    expr_interp (((σ :: []) :: []) : CTX.{u}) (.var nm 0 0) σ
      = Part.some (interp_var 0 0 rfl rfl) := by
  rw [var_ghost]
  exact interp_var_head σ

end application_interp

section program_composition

universe u

gdef SYNT.comp (σ τ υ : TYPE) (P : SYNT ⦃σ → τ⦄) (Q : SYNT ⦃τ → υ⦄) : σ → υ :=
  λ x : σ. [Q]ₛ ([P]ₛ x)

theorem denoteHom_eq_of_interp_lam {σ τ : TYPE.{u}} {e : SYNT ⦃σ → τ⦄}
    {k : (⟦σ⟧ₜ : ℐ.{u}) ⟶ ⟦τ⟧ₜ}
    (h : synt_interp e = interp_lam (interp_var 0 0 rfl rfl ≫ k)) :
    denoteHom e = k := by
  unfold denoteHom GlobalElt
  rw [h, interp_lam]
  refine ((congrArg ((ρ_ (⟦σ⟧ₜ : ℐ.{u})).inv ≫ ·)
    ((MonoidalClosed.uncurry_natural_left _ _).trans
      (congrArg (((⟦σ⟧ₜ : ℐ.{u}) ◁
          CartesianMonoidalCategory.lift (𝟙 (𝟙_ ℐ.{u})) earlier_terminal.inv) ≫ ·)
        (MonoidalClosed.uncurry_curry _))))).trans ?_
  simp only [interp_var]
  simp [ctx_proj, octx_proj, interp_ctx, interp_octx]

unseal SYNT.comp EXPR.lam EXPR.var in
theorem denoteHom_comp {σ τ υ : TYPE.{u}} (P : SYNT ⦃σ → τ⦄) (Q : SYNT ⦃τ → υ⦄) :
    denoteHom (SYNT.comp σ τ υ P Q) = denoteHom P ≫ denoteHom Q := by
  refine denoteHom_eq_of_interp_lam (synt_interp_eq_of_expr_interp _ ?_)
  show expr_interp [[]] (.lam' σ (.app τ (EXPR.quote Q 1 (some 1))
    (.app σ (EXPR.quote P 1 (some 1)) (.var' 0 0)))) ⦃σ → υ⦄ = _
  show (expr_interp (((σ :: []) :: []) : CTX.{u}) (.app τ (EXPR.quote Q 1 (some 1))
      (.app σ (EXPR.quote P 1 (some 1)) (.var' 0 0))) υ).bind
    (fun e' => Part.some (interp_lam e')) = _
  rw [interp_app_quote (by simp) Q 1 (some 1)
      (interp_app_quote (by simp) P 1 (some 1) (interp_var_head σ)),
    Part.bind_some]
  exact congrArg (Part.some <| interp_lam ·) (Category.assoc _ _ _).symm

end program_composition

section semantic_import

universe u

gtheorem SYNT.app_ext (σ τ : TYPE.{u}) (P Q : SYNT ⦃σ → τ⦄) (h : denoteHom P = denoteHom Q) :
    ∀ x : σ. (([P]ₛ x) = ([Q]ₛ x)) := by
  gintro x
  refine ⟨PROVES.eq_def (EQ.ax ?_ ?_ ?_)⟩
  · exact TYPED.app
      (weaken_typing P.proof (TYPED_REN.global_n_weak (((σ :: []) :: []) : CTX.{u}) (by simp)))
      (TYPED.var_explicit (Γ := ((σ :: []) :: [])) (0 : Fin 1) (0 : Fin 1))
  · exact TYPED.app
      (weaken_typing Q.proof (TYPED_REN.global_n_weak (((σ :: []) :: []) : CTX.{u}) (by simp)))
      (TYPED.var_explicit (Γ := ((σ :: []) :: [])) (0 : Fin 1) (0 : Fin 1))
  · rw [interp_app_quote (by simp) P _ _ (interp_var_head' _ σ),
      interp_app_quote (by simp) Q _ _ (interp_var_head' _ σ), h]

end semantic_import

gtheorem SYNT.eq_of_denoteHom (σ τ : TYPE) (P Q : SYNT ⦃σ → τ⦄)
    (h : denoteHom P = denoteHom Q) : ([P]ₛ = [Q]ₛ) := by
  refine ⟨PROVES.eq_def (EQ.ax ?_ ?_ ?_)⟩
  · exact weaken_typing P.proof (TYPED_REN.global_n_weak [[]] (by simp))
  · exact weaken_typing Q.proof (TYPED_REN.global_n_weak [[]] (by simp))
  · rw [interp_quote_toUnit (by simp) P, interp_quote_toUnit (by simp) Q,
      globalElt_eq_of_denoteHom h]

theorem denoteHom_congr' {σ τ : TYPE.{u}} {P Q : SYNT ⦃σ → τ⦄} {n₁ n₂ : Nat}
    {m₁ m₂ : Option Nat}
    (H : PROVES [[]] [[]] (EXPR.eq ⦃σ → τ⦄ (EXPR.quote P n₁ m₁) (EXPR.quote Q n₂ m₂))) :
    denoteHom P = denoteHom Q := by
  have hP := interp_quote_toUnit (Γ := [[]]) (by simp) P n₁ m₁
  have hQ := interp_quote_toUnit (Γ := [[]]) (by simp) Q n₂ m₂
  have dP : (expr_interp [[]] (EXPR.quote P n₁ m₁) ⦃σ → τ⦄).Dom := by rw [hP]; trivial
  have dQ : (expr_interp [[]] (EXPR.quote Q n₂ m₂) ⦃σ → τ⦄).Dom := by rw [hQ]; trivial
  have h : toUnit (⟦[[]]⟧ₛ : ℐ.{u}) ≫ GlobalElt P = toUnit _ ≫ GlobalElt Q :=
    (Part.get_eq_iff_eq_some.mpr hP).symm.trans
      ((denote_eq H dP dQ).trans (Part.get_eq_iff_eq_some.mpr hQ))
  exact congrArg MonoidalClosed.uncurry'
    ((Iso.hom_inv_id_assoc interpNilIso _).symm.trans
      ((congrArg (interpNilIso.hom ≫ ·) h).trans (Iso.hom_inv_id_assoc interpNilIso _)))

section goal_consumers

universe u

theorem denoteHom_of_goal {σ τ : TYPE.{u}} {P Q : SYNT ⦃σ → τ⦄} {n₁ n₂ : Nat}
    {m₁ m₂ : Option Nat}
    (G : ⊢ᵍ (EXPR.eq ⦃σ → τ⦄ (EXPR.quote P n₁ m₁) (EXPR.quote Q n₂ m₂))) :
    denoteHom P = denoteHom Q := by
  obtain ⟨H⟩ := G
  exact denoteHom_congr' H

theorem globalElt_app_congr {A B : TYPE.{u}} (K : SYNT ⦃A → B⦄) {P Q : SYNT A}
    (h : GlobalElt P = GlobalElt Q) :
    GlobalElt (box([K]ₛ [P]ₛ) : SYNT B) = GlobalElt (box([K]ₛ [Q]ₛ) : SYNT B) := by
  rw [globalElt_app, globalElt_app, h]

end goal_consumers

end
