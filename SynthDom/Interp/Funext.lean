module

public import SynthDom.Interp.Soundness
public import SynthDom.Syntax.Prf.Wrappers
public import SynthDom.Syntax.Expr.Delab
@[expose] public section

open CategoryTheory
open Logic

noncomputable section
namespace funext_sem

def funext_prop (A B : TYPE.{i}) : SYNT.{i} TYPE.prop :=
  box(∀ f : A → B. ∀ g : A → B.
      (∀ x : A. (f x) = (g x)) → (f = g))

theorem entails_antisymm {G : ℐ.{i}} {P Q : G ⟶ Ω} (h1 : P ⊢ᵢ Q) (h2 : Q ⊢ᵢ P) : P = Q := by
  apply NatTrans.ext
  funext x
  apply ConcreteCategory.hom_ext
  intro γ
  apply ULift.ext
  apply Sieve.ext
  intro m f
  exact ⟨fun hf => h1 x.unop γ m f hf, fun hf => h2 x.unop γ m f hf⟩

private lemma precomp_pctx_nil {Γ Γ' : CTX.{i}} (f : ⟦Γ'⟧ₛ ⟶ ⟦Γ⟧ₛ) :
    f ≫ pctx (Γ := Γ) [[]] = pctx (Γ := Γ') [[]] := by
  rw [Soundness.pctx_natural]; rfl

private lemma forall_some {Γ0 : OCTX.{i}} {Γs : CTX.{i}} {τ : TYPE.{i}} {body : EXPR.{i}}
    (h : (expr_interp ((τ :: Γ0) :: Γs) body TYPE.prop).Dom) :
    expr_interp (Γ0 :: Γs) (EXPR.forall' τ body) TYPE.prop
      = Part.some (interp_forall ((expr_interp ((τ :: Γ0) :: Γs) body TYPE.prop).get h)) := by
  simp only [expr_interp, bind, Part.Dom.bind h]; rfl

private lemma impl_some {G : CTX.{i}} {Φ₁ Φ₂ : EXPR.{i}}
    (h1 : (expr_interp G Φ₁ TYPE.prop).Dom) (h2 : (expr_interp G Φ₂ TYPE.prop).Dom) :
    expr_interp G (EXPR.impl Φ₁ Φ₂) TYPE.prop
      = Part.some (interp_impl ((expr_interp G Φ₁ TYPE.prop).get h1)
          ((expr_interp G Φ₂ TYPE.prop).get h2)) := by
  simp only [expr_interp, bind, Part.Dom.bind h1, Part.Dom.bind h2]; rfl

private lemma eq_some {G : CTX.{i}} {τ : TYPE.{i}} {e1 e2 : EXPR.{i}}
    (h1 : (expr_interp G e1 τ).Dom) (h2 : (expr_interp G e2 τ).Dom) :
    expr_interp G (EXPR.eq τ e1 e2) TYPE.prop
      = Part.some (interp_eq ((expr_interp G e1 τ).get h1) ((expr_interp G e2 τ).get h2)) := by
  simp only [expr_interp, bind, Part.Dom.bind h1, Part.Dom.bind h2]; rfl

private lemma app_some {G : CTX.{i}} {σ τ : TYPE.{i}} {e1 e2 : EXPR.{i}}
    (h1 : (expr_interp G e1 (TYPE.arr σ τ)).Dom) (h2 : (expr_interp G e2 σ).Dom) :
    expr_interp G (EXPR.app σ e1 e2) τ
      = Part.some (interp_app ((expr_interp G e1 (TYPE.arr σ τ)).get h1)
          ((expr_interp G e2 σ).get h2)) := by
  simp only [expr_interp, bind, Part.Dom.bind h1, Part.Dom.bind h2]; rfl

private lemma get_of_some {α} {o : Part α} {a : α} (h : o.Dom) (he : o = Part.some a) :
    o.get h = a := by simp only [he, Part.get_some]

section funext_internal_sec
open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite
variable {X Y G : ℐ.{i}}

private lemma eqI_mem {Z : ℐ.{i}} (a b : G ⟶ Z) (n m : ℕ) (γ : G.obj (op n)) (φ : m ⟶ n) :
    ((eq a b).app (op n) γ).down.arrows φ
      ↔ Z.map φ.op (a.app (op n) γ) = Z.map φ.op (b.app (op n) γ) := by
  show (Z.map φ.op (((CartesianMonoidalCategory.lift a b).app (op n) γ).1)
        = Z.map φ.op (((CartesianMonoidalCategory.lift a b).app (op n) γ).2)) ↔ _
  rw [lift_app_fst a, lift_app_snd b]

private lemma eq_precomp {A D D' : ℐ.{i}} (h : D' ⟶ D) (a b : D ⟶ A) :
    h ≫ (a ≡ᵢ b) = (h ≫ a) ≡ᵢ (h ≫ b) := by
  rw [Logic.eq, Logic.eq, ← Category.assoc, comp_lift]

private lemma funext_internal (f g : G ⟶ ℐ.parr X Y) :
    (∀ᵢ[X] ((MonoidalClosed.uncurry f) ≡ᵢ (MonoidalClosed.uncurry g)))
      ⊢ᵢ (f ≡ᵢ g) := by
  set P : (X ⊗ G) ⟶ Ω := (MonoidalClosed.uncurry f) ≡ᵢ (MonoidalClosed.uncurry g) with hP
  have hdagger : (snd X G ≫ (∀ᵢ[X] P)) ⊢ᵢ P := by
    rw [all_natural (snd X G) P]
    have h := all_elim (X ◁ (snd X G) ≫ P) (fst X G)
    rw [← Category.assoc, show CartesianMonoidalCategory.lift (fst X G) (𝟙 (X ⊗ G))
          ≫ (X ◁ (snd X G)) = 𝟙 (X ⊗ G) by
        apply CartesianMonoidalCategory.hom_ext <;> simp, Category.id_comp] at h
    exact h
  intro n γ m φ hH
  rw [eqI_mem]
  refine Subtype.ext (funext fun k => funext fun hk => funext fun x => ?_)
  have le_kn : k ≤ n := hk.trans (leOfHom φ)
  have hAB : ∀ (h : G ⟶ ℐ.parr X Y),
      ((ℐ.parr X Y).map φ.op (h.app (op n) γ)).1 k hk x
        = (h.app (op k) (G.map (homOfLE le_kn).op γ)).1 k (le_refl k) x := by
    intro h
    rw [NatTrans.naturality_apply h ((homOfLE le_kn).op) γ]
    rfl
  rw [hAB f, hAB g]
  have prem : ((snd X G ≫ (∀ᵢ[X] P)).app (op k)
      ((x, G.map (homOfLE le_kn).op γ) : (X ⊗ G).obj (op k))).down.arrows (𝟙 k) := by
    show ((∀ᵢ[X] P).app (op k) (G.map (homOfLE le_kn).op γ)).down.arrows (𝟙 k)
    rw [NatTrans.naturality_apply (∀ᵢ[X] P) ((homOfLE le_kn).op) γ]
    show (Sieve.pullback (homOfLE le_kn) ((∀ᵢ[X] P).app (op n) γ).down).arrows (𝟙 k)
    rw [Sieve.pullback_apply, Category.id_comp]
    have hdc : ((∀ᵢ[X] P).app (op n) γ).down.arrows (homOfLE hk ≫ φ) :=
      ((∀ᵢ[X] P).app (op n) γ).down.downward_closed hH (homOfLE hk)
    rwa [Subsingleton.elim (homOfLE hk ≫ φ) (homOfLE le_kn)] at hdc
  have hconcl := hdagger k ((x, G.map (homOfLE le_kn).op γ) : (X ⊗ G).obj (op k)) k (𝟙 k) prem
  rw [hP] at hconcl
  have key := (eqI_mem (MonoidalClosed.uncurry f) (MonoidalClosed.uncurry g)
    k k ((x, G.map (homOfLE le_kn).op γ) : (X ⊗ G).obj (op k)) (𝟙 k)).mp hconcl
  rw [op_id] at key
  simp only [CategoryTheory.Functor.map_id_apply] at key
  exact key

end funext_internal_sec

open CategoryTheory Opposite in
private lemma var0_get {Γ : CTX.{i}} {D : OCTX.{i}} {τ : TYPE.{i}} {q : Nat}
    (H0 : Γ[0]? = some D) (Hq : D[q]? = some τ) (h : (⟦Γ, EXPR.var' 0 q, τ⟧ₑ).Dom) :
    (⟦Γ, EXPR.var' 0 q, τ⟧ₑ).get h = ctx_proj Γ 0 D H0 ≫ octx_proj D q τ Hq := by
  have hlen : 0 < Γ.length := by
    cases Γ with
    | nil => simp at H0
    | cons => simp
  have hD : Γ[0]'hlen = D := by
    have hh := List.getElem?_eq_getElem hlen
    rw [H0] at hh; exact (Option.some.injEq _ _ ▸ hh).symm
  subst hD
  have hq : (Γ[0]'hlen)[q]? = some τ := Hq
  rw [get_of_some h (show ⟦Γ, EXPR.var' 0 q, τ⟧ₑ
        = Part.some (interp_var 0 q (getElem?_pos Γ 0 hlen) hq) by
      simp only [expr_interp, Part.assert_pos hlen, Part.assert_pos hq]; rfl), interp_var]

open CategoryTheory CartesianMonoidalCategory MonoidalCategory Opposite in
private lemma funext_core (Aty Bty : TYPE.{i}) :
    interp_forall
      (interp_eq
        (interp_app
          (ctx_proj [[Aty, Aty.arr Bty, Aty.arr Bty]] 0 [Aty, Aty.arr Bty, Aty.arr Bty] rfl
              ≫ octx_proj [Aty, Aty.arr Bty, Aty.arr Bty] 2 (Aty.arr Bty) rfl)
          (ctx_proj [[Aty, Aty.arr Bty, Aty.arr Bty]] 0 [Aty, Aty.arr Bty, Aty.arr Bty] rfl
              ≫ octx_proj [Aty, Aty.arr Bty, Aty.arr Bty] 0 Aty rfl))
        (interp_app
          (ctx_proj [[Aty, Aty.arr Bty, Aty.arr Bty]] 0 [Aty, Aty.arr Bty, Aty.arr Bty] rfl
              ≫ octx_proj [Aty, Aty.arr Bty, Aty.arr Bty] 1 (Aty.arr Bty) rfl)
          (ctx_proj [[Aty, Aty.arr Bty, Aty.arr Bty]] 0 [Aty, Aty.arr Bty, Aty.arr Bty] rfl
              ≫ octx_proj [Aty, Aty.arr Bty, Aty.arr Bty] 0 Aty rfl)))
      ⊢ᵢ
    interp_eq
      (ctx_proj [[Aty.arr Bty, Aty.arr Bty]] 0 [Aty.arr Bty, Aty.arr Bty] rfl
          ≫ octx_proj [Aty.arr Bty, Aty.arr Bty] 1 (Aty.arr Bty) rfl)
      (ctx_proj [[Aty.arr Bty, Aty.arr Bty]] 0 [Aty.arr Bty, Aty.arr Bty] rfl
          ≫ octx_proj [Aty.arr Bty, Aty.arr Bty] 0 (Aty.arr Bty) rfl) := by
  rw [interp_forall]
  simp only [interp_eq, interp_app, ctx_proj, octx_proj, eqToHom_refl, Category.comp_id,
    interp_octx, interp_ctx]
  set AB : ℐ.{i} := ⟦Aty.arr Bty⟧ₜ with hABd
  set Q : ℐ.{i} := earlier.obj (𝟙_ ℐ.{i}) with hQd
  set P : ℐ.{i} := AB ⊗ AB ⊗ 𝟙_ ℐ.{i} with hPd
  set ftail : P ⟶ AB := snd AB (AB ⊗ 𝟙_ ℐ.{i}) ≫ fst AB (𝟙_ ℐ.{i}) with hftail
  set ffst : P ⟶ AB := fst AB (AB ⊗ 𝟙_ ℐ.{i}) with hffst
  set f : P ⊗ Q ⟶ AB := fst P Q ≫ ftail with hf
  set g : P ⊗ Q ⟶ AB := fst P Q ≫ ffst with hg
  convert funext_internal (X := ⟦Aty⟧ₜ) (Y := ⟦Bty⟧ₜ) f g using 2
  · rw [eq_precomp]
    congr 1
  all_goals rfl

unseal EXPR.forall EXPR.var in
theorem funext_hsem (A B : TYPE.{i}) :
    expr_interp [[]] EXPR.true TYPE.prop
      = expr_interp [[]] (funext_prop A B).expr TYPE.prop := by
  set Aty : TYPE.{i} := ⦃A⦄ with hAty
  set Bty : TYPE.{i} := ⦃B⦄ with hBty
  set ABty : TYPE.{i} := TYPE.arr Aty Bty with hABty
  set Γfg : CTX.{i} := [[ABty, ABty]] with hΓfg
  set Γx : CTX.{i} := [[Aty, ABty, ABty]] with hΓx
  have Hf_x : TYPED Γx (EXPR.var' 0 2) ABty := TYPED.var'_explicit (Γ := Γx) (0 : Fin 1) (2 : Fin 3)
  have Hg_x : TYPED Γx (EXPR.var' 0 1) ABty := TYPED.var'_explicit (Γ := Γx) (0 : Fin 1) (1 : Fin 3)
  have Hx   : TYPED Γx (EXPR.var' 0 0) Aty  := TYPED.var'_explicit (Γ := Γx) (0 : Fin 1) (0 : Fin 3)
  have Hfx  : TYPED Γx (EXPR.app Aty (.var' 0 2) (.var' 0 0)) Bty := TYPED.app Hf_x Hx
  have Hgx  : TYPED Γx (EXPR.app Aty (.var' 0 1) (.var' 0 0)) Bty := TYPED.app Hg_x Hx
  have Hf_fg : TYPED Γfg (EXPR.var' 0 1) ABty := TYPED.var'_explicit (Γ := Γfg) (0 : Fin 1) (1 : Fin 2)
  have Hg_fg : TYPED Γfg (EXPR.var' 0 0) ABty := TYPED.var'_explicit (Γ := Γfg) (0 : Fin 1) (0 : Fin 2)
  set Φraw : EXPR.{i} :=
    EXPR.forall' ABty (EXPR.forall' ABty (EXPR.impl
      (EXPR.forall' Aty (EXPR.eq Bty (EXPR.app Aty (EXPR.var' 0 2) (EXPR.var' 0 0))
        (EXPR.app Aty (EXPR.var' 0 1) (EXPR.var' 0 0))))
      (EXPR.eq ABty (EXPR.var' 0 1) (EXPR.var' 0 0)))) with hΦraw
  rw [show (funext_prop A B).expr = Φraw by unfold funext_prop; rfl]
  have Teqx  : TYPED Γx (EXPR.eq Bty _ _) TYPE.prop := TYPED.eq Hfx Hgx
  have Tfax  : TYPED Γfg (EXPR.forall' Aty _) TYPE.prop := TYPED.forall' Teqx
  have Teqfg : TYPED Γfg (EXPR.eq ABty _ _) TYPE.prop := TYPED.eq Hf_fg Hg_fg
  have Timpl : TYPED Γfg (EXPR.impl _ _) TYPE.prop := TYPED.impl Tfax Teqfg
  have Tf2   : TYPED [[ABty]] (EXPR.forall' ABty _) TYPE.prop := TYPED.forall' Timpl
  have hd := expr_interp_correct (TYPED.forall' Tf2)
  rw [show expr_interp [[]] EXPR.true TYPE.prop = Part.some interp_true from rfl,
    (Part.some_get hd).symm]
  congr 1
  rw [get_of_some hd (forall_some (expr_interp_correct Tf2)),
      get_of_some (expr_interp_correct Tf2) (forall_some (expr_interp_correct Timpl)),
      get_of_some (expr_interp_correct Timpl)
        (impl_some (expr_interp_correct Tfax) (expr_interp_correct Teqfg)),
      get_of_some (expr_interp_correct Tfax) (forall_some (expr_interp_correct Teqx)),
      get_of_some (expr_interp_correct Teqx)
        (eq_some (expr_interp_correct Hfx) (expr_interp_correct Hgx)),
      get_of_some (expr_interp_correct Hfx)
        (app_some (expr_interp_correct Hf_x) (expr_interp_correct Hx)),
      get_of_some (expr_interp_correct Hgx)
        (app_some (expr_interp_correct Hg_x) (expr_interp_correct Hx)),
      get_of_some (expr_interp_correct Teqfg)
        (eq_some (expr_interp_correct Hf_fg) (expr_interp_correct Hg_fg))]
  apply entails_antisymm
  · refine entails_trans _ _ _ (?_ : interp_true ⊢ᵢ pctx (Γ := ([[]] : CTX.{i})) [[]]) ?_
    · simp only [interp_true, pctx, poctx]
      apply conj_intro <;> exact true_intro
    · apply intro_all
      rw [show (interp_ren_local_weaken interp_ren_id ≫ pctx [[]] : ⟦[[ABty]]⟧ₛ ⟶ Ω)
            = pctx [[]] from precomp_pctx_nil _]
      apply intro_all
      rw [show (interp_ren_local_weaken interp_ren_id ≫ pctx [[]] : ⟦Γfg⟧ₛ ⟶ Ω)
            = pctx [[]] from precomp_pctx_nil _]
      apply intro_impl
      refine entails_trans _ _ _ (intro_asm (n := 0) (m := 0) rfl rfl) ?_
      rw [var0_get (Γ := Γx) (D := [Aty, ABty, ABty]) (by rw [hΓx]; rfl) rfl
            (expr_interp_correct Hf_x),
          var0_get (Γ := Γx) (D := [Aty, ABty, ABty]) (by rw [hΓx]; rfl) rfl
            (expr_interp_correct Hg_x),
          var0_get (Γ := Γx) (D := [Aty, ABty, ABty]) (by rw [hΓx]; rfl) rfl
            (expr_interp_correct Hx),
          var0_get (Γ := Γfg) (D := [ABty, ABty]) (by rw [hΓfg]; rfl) rfl
            (expr_interp_correct Hf_fg),
          var0_get (Γ := Γfg) (D := [ABty, ABty]) (by rw [hΓfg]; rfl) rfl
            (expr_interp_correct Hg_fg)]
      exact funext_core Aty Bty
  · exact true_intro

theorem funext (A B : TYPE.{i}) :
    GOAL [[]] [[]] [[]] [[]] (funext_prop A B).expr := by
  refine ⟨?_⟩
  exact simplify_prop (EQ.ax (TYPED.true (by simp)) ((funext_prop A B).proof)
    (funext_hsem A B)) (PROVES.true_intro)

end funext_sem

end

end
