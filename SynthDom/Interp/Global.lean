module

public import SynthDom.Interp.Interp
public import SynthDom.Syntax.Expr.Typecheck

@[expose] public section

section global

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

open Opposite Limits in
theorem interp_nil_obj_subsingleton (n : ℕ) : Subsingleton ((⟦[[]]⟧ₛ : ℐ.{i}).obj (op n)) := by
  rw [show (⟦[[]]⟧ₛ : ℐ.{i}) = ((𝟙_ ℐ.{i}) ⊗ earlier.obj (𝟙_ ℐ.{i})) by
    simp [interp_ctx, interp_octx]]
  simp only [CategoryTheory.Monoidal.tensorObj_obj, CategoryTheory.Monoidal.tensorUnit_obj,
    earlier, earlier_obj, types_tensorObj_def, types_tensorUnit_def]
  infer_instance

open Opposite in
theorem hom_to_nil_unique {X : ℐ.{i}} (a b : X ⟶ ⟦[[]]⟧ₛ) : a = b := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  cases n with
  | op n' =>
    have := interp_nil_obj_subsingleton n'
    apply Subsingleton.elim

open Opposite Limits in
theorem delay_factor_point_eq_next (m : (𝟙_ ℐ.{i} ⊗ earlier.obj ⟦[[]]⟧ₛ) ⟶ ⟦[[]]⟧ₛ)
    (p : 𝟙_ ℐ.{i} ⟶ ⟦[[]]⟧ₛ) :
    p ≫ unit_adj.app ⟦[[]]⟧ₛ ≫ later.map ((λ_ (earlier.obj ⟦[[]]⟧ₛ)).inv ≫ m)
      = p ≫ next.app ⟦[[]]⟧ₛ := by
  apply NatTrans.ext
  funext X
  apply ConcreteCategory.hom_ext
  intro a
  cases X with
  | op n => cases n with
    | zero =>
      have : Subsingleton ((later.obj (⟦[[]]⟧ₛ : ℐ.{i})).obj (op 0)) := by
        rw [later_obj_obj_zero]; infer_instance
      apply Subsingleton.elim
    | succ n =>
      have := interp_nil_obj_subsingleton.{i} n
      have : Subsingleton ((later.obj (⟦[[]]⟧ₛ : ℐ.{i})).obj (op (n + 1))) := by
        rw [later_obj_obj_succ]; infer_instance
      apply Subsingleton.elim

theorem interp_delay_reshape {τ : TYPE.{i}} (m : (𝟙_ ℐ.{i} ⊗ earlier.obj ⟦[[]]⟧ₛ) ⟶ ⟦[[]]⟧ₛ)
    (g : (⟦[[]]⟧ₛ : ℐ.{i}) ⟶ ⟦τ⟧ₜ) :
    interp_delay (Γ := [[]]) (m ≫ g)
      = (unit_adj.app ⟦[[]]⟧ₛ ≫ later.map ((λ_ (earlier.obj ⟦[[]]⟧ₛ)).inv ≫ m)) ≫ later.map g := by
  rw [interp_delay]
  simp only [Equiv.toFun_as_coe, Adjunction.homEquiv_unit, interp_ctx, interp_octx]
  rw [show earlier_later_adj.unit = unit_adj from rfl, Category.assoc]
  congr 1
  simp only [Functor.map_comp]
  exact (Category.assoc _ _ _).symm

theorem interp_delay_point_eq_next {τ : TYPE.{i}} (m : (𝟙_ ℐ.{i} ⊗ earlier.obj ⟦[[]]⟧ₛ) ⟶ ⟦[[]]⟧ₛ)
    (g : (⟦[[]]⟧ₛ : ℐ.{i}) ⟶ ⟦τ⟧ₜ) (p : 𝟙_ ℐ.{i} ⟶ ⟦[[]]⟧ₛ) :
    p ≫ interp_delay (Γ := [[]]) (m ≫ g) = (p ≫ g) ≫ next.app ⟦τ⟧ₜ := by
  calc p ≫ interp_delay (Γ := [[]]) (m ≫ g)
      = p ≫ ((unit_adj.app ⟦[[]]⟧ₛ ≫ later.map ((λ_ (earlier.obj ⟦[[]]⟧ₛ)).inv ≫ m)) ≫ later.map g) :=
        congrArg (p ≫ ·) (interp_delay_reshape m g)
    _ = (p ≫ (unit_adj.app ⟦[[]]⟧ₛ ≫ later.map ((λ_ (earlier.obj ⟦[[]]⟧ₛ)).inv ≫ m))) ≫ later.map g :=
        (Category.assoc _ _ _).symm
    _ = (p ≫ next.app ⟦[[]]⟧ₛ) ≫ later.map g := by rw [delay_factor_point_eq_next m p]
    _ = p ≫ (next.app ⟦[[]]⟧ₛ ≫ later.map g) := Category.assoc _ _ _
    _ = p ≫ (g ≫ next.app ⟦τ⟧ₜ) := congrArg (p ≫ ·) (by
        have := next.naturality g; rw [Functor.id_map] at this; exact this.symm)
    _ = (p ≫ g) ≫ next.app ⟦τ⟧ₜ := (Category.assoc _ _ _).symm

theorem synt_interp_delay_factors {τ : TYPE.{i}} (c : SYNT τ) :
    ∃ m : ⟦[] :: [[]]⟧ₛ ⟶ ⟦[[]]⟧ₛ,
      synt_interp (box(delay [c]ₛ) : SYNT (TYPE.later τ)) = interp_delay (m ≫ synt_interp c) := by
  have H : TYPED_REN (REN.global_n_weak 2 (some 0)) ([] :: [[]]) [[]] :=
    TYPED_REN.global_n_weak ([] :: [[]]) (by simp)
  refine ⟨⟦H⟧ᵣ, ?_⟩
  have hpart : expr_interp [[]] (box(delay [c]ₛ) : SYNT (TYPE.later τ)).expr (TYPE.later τ)
      = Part.some (interp_delay (⟦H⟧ᵣ ≫ synt_interp c)) := by
    show expr_interp [[]] (EXPR.delay (EXPR.quote c 2 (some 0))) (TYPE.later τ) = _
    simp only [expr_interp]
    rw [EXPR.quote]
    rw [eq_weak (H := H) _ c.expr τ c.proof]
    rw [synt_interp]
    simp [← Part.bind_some_eq_map, Part.Dom.bind (expr_interp_correct c.proof)]
  simp only [synt_interp, hpart, Part.get_some]

theorem const_app {X : ℐ.{i}} {A B : ℐ.{i}} (g : X ⟶ A)
    (f : 𝟙_ ℐ.{i} ⟶ (ihom A).obj B) :
    CartesianMonoidalCategory.lift g (CartesianMonoidalCategory.toUnit X ≫ f)
        ≫ (ihom.ev A).app B = g ≫ MonoidalClosed.uncurry' f := by
  rw [show CartesianMonoidalCategory.lift g (CartesianMonoidalCategory.toUnit X ≫ f)
        = g ≫ (ρ_ A).inv ≫ (A ◁ f) by
      apply CartesianMonoidalCategory.hom_ext <;> simp,
    MonoidalClosed.uncurry', MonoidalClosed.uncurry_eq]
  simp only [Category.assoc]

lemma expr_interp_eq_some {τ : TYPE.{i}} (c : SYNT τ) :
    expr_interp [[]] c.expr τ = Part.some (synt_interp c) :=
  (Part.some_get (expr_interp_correct c.proof)).symm

lemma synt_interp_eq_of_expr_interp {τ : TYPE.{i}} (c : SYNT τ) {v : ⟦[[]]⟧ₛ ⟶ ⟦τ⟧ₜ}
    (h : expr_interp [[]] c.expr τ = Part.some v) : synt_interp c = v :=
  Part.some_inj.mp ((expr_interp_eq_some c).symm.trans h)

lemma synt_interp_congr {τ : TYPE.{i}} {e1 e2 : SYNT τ} (h : e1.expr = e2.expr) :
    synt_interp e1 = synt_interp e2 := by
  unfold synt_interp
  congr 1
  rw [h]

def GlobalElt {τ : TYPE.{i}} (e : SYNT τ) : 𝟙_ ℐ.{i} ⟶ ⟦τ⟧ₜ :=
  CartesianMonoidalCategory.lift (𝟙 _) earlier_terminal.inv ≫ synt_interp e

lemma globalElt_congr {τ : TYPE.{i}} {e1 e2 : SYNT τ} (h : e1.expr = e2.expr) :
    GlobalElt e1 = GlobalElt e2 := by
  unfold GlobalElt
  rw [synt_interp_congr h]

private def globalQuoteRen : TYPED_REN (REN.global_n_weak 1 (some 0)) [[]] [[]] :=
  TYPED_REN.global_n_weak [[]] (by simp)

private lemma globalQuoteRen_kill
    (p : 𝟙_ ℐ.{i} ⟶ ⟦[[]]⟧ₛ) : p ≫ ⟦globalQuoteRen⟧ᵣ = p :=
  hom_to_nil_unique _ _

lemma globalElt_app {A B : TYPE.{i}} (f : SYNT (TYPE.arr A B)) (x : SYNT A) :
    GlobalElt (box([f]ₛ [x]ₛ) : SYNT B) = GlobalElt x ≫ MonoidalClosed.uncurry' (GlobalElt f) := by
  have hpart : expr_interp [[]] (box([f]ₛ [x]ₛ) : SYNT B).expr B
      = Part.some (interp_app (⟦globalQuoteRen⟧ᵣ ≫ synt_interp f) (⟦globalQuoteRen⟧ᵣ ≫ synt_interp x)) := by
    show expr_interp [[]] (EXPR.app A (EXPR.quote f 1 (some 0)) (EXPR.quote x 1 (some 0))) B = _
    simp only [expr_interp]
    rw [EXPR.quote, EXPR.quote]
    rw [eq_weak (H := globalQuoteRen) _ f.expr _ f.proof,
      eq_weak (H := globalQuoteRen) _ x.expr _ x.proof]
    rw [synt_interp, synt_interp]
    simp [← Part.bind_some_eq_map, Part.Dom.bind (expr_interp_correct f.proof),
      Part.Dom.bind (expr_interp_correct x.proof)]
  have hs : synt_interp (box([f]ₛ [x]ₛ) : SYNT B)
      = interp_app (⟦globalQuoteRen⟧ᵣ ≫ synt_interp f) (⟦globalQuoteRen⟧ᵣ ≫ synt_interp x) := by
    simp only [synt_interp, hpart, Part.get_some]
  simp only [GlobalElt, hs]
  set p : 𝟙_ ℐ.{i} ⟶ ⟦[[]]⟧ₛ := CartesianMonoidalCategory.lift (𝟙 _) earlier_terminal.inv
  show CartesianMonoidalCategory.lift (p ≫ synt_interp x) (p ≫ synt_interp f)
      ≫ (ihom.ev ⟦A⟧ₜ).app ⟦B⟧ₜ = _
  calc CartesianMonoidalCategory.lift (p ≫ synt_interp x) (p ≫ synt_interp f)
        ≫ (ihom.ev ⟦A⟧ₜ).app ⟦B⟧ₜ
      = CartesianMonoidalCategory.lift (p ≫ synt_interp x)
            (CartesianMonoidalCategory.toUnit _ ≫ (p ≫ synt_interp f))
          ≫ (ihom.ev ⟦A⟧ₜ).app ⟦B⟧ₜ := by
        rw [CartesianMonoidalCategory.toUnit_unit, Category.id_comp]
    _ = (p ≫ synt_interp x) ≫ MonoidalClosed.uncurry' (p ≫ synt_interp f) :=
        const_app _ _

lemma globalElt_pair {A B : TYPE.{i}} (a : SYNT A) (b : SYNT B) :
    GlobalElt (box(⟨[a]ₛ, [b]ₛ⟩) : SYNT (TYPE.prod A B))
      = CartesianMonoidalCategory.lift (GlobalElt a) (GlobalElt b) := by
  have hpart : expr_interp [[]] (box(⟨[a]ₛ, [b]ₛ⟩) : SYNT (TYPE.prod A B)).expr (TYPE.prod A B)
      = Part.some (interp_pair (⟦globalQuoteRen⟧ᵣ ≫ synt_interp a) (⟦globalQuoteRen⟧ᵣ ≫ synt_interp b)) := by
    show expr_interp [[]] (EXPR.pair (EXPR.quote a 1 (some 0)) (EXPR.quote b 1 (some 0)))
        (TYPE.prod A B) = _
    simp only [expr_interp]
    rw [EXPR.quote, EXPR.quote]
    rw [eq_weak (H := globalQuoteRen) _ a.expr _ a.proof,
      eq_weak (H := globalQuoteRen) _ b.expr _ b.proof]
    rw [synt_interp, synt_interp]
    simp [← Part.bind_some_eq_map, Part.Dom.bind (expr_interp_correct a.proof),
      Part.Dom.bind (expr_interp_correct b.proof)]
  have hs : synt_interp (box(⟨[a]ₛ, [b]ₛ⟩) : SYNT (TYPE.prod A B))
      = interp_pair (⟦globalQuoteRen⟧ᵣ ≫ synt_interp a) (⟦globalQuoteRen⟧ᵣ ≫ synt_interp b) := by
    simp only [synt_interp, hpart, Part.get_some]
  simp only [GlobalElt, hs]
  set p : 𝟙_ ℐ.{i} ⟶ ⟦[[]]⟧ₛ := CartesianMonoidalCategory.lift (𝟙 _) earlier_terminal.inv
  show CartesianMonoidalCategory.lift (p ≫ synt_interp a) (p ≫ synt_interp b) = _
  rfl

lemma globalElt_app_pair {A B C : TYPE.{i}} (f : SYNT (TYPE.arr (TYPE.prod A B) C))
    (a : SYNT A) (b : SYNT B) :
    GlobalElt (box([f]ₛ ⟨[a]ₛ, [b]ₛ⟩) : SYNT C) =
      CartesianMonoidalCategory.lift (GlobalElt a) (GlobalElt b)
        ≫ MonoidalClosed.uncurry' (GlobalElt f) := by
  let pair : SYNT (TYPE.prod A B) := box(⟨[a]ₛ, [b]ₛ⟩)
  calc
    GlobalElt (box([f]ₛ ⟨[a]ₛ, [b]ₛ⟩) : SYNT C) =
        GlobalElt (box([f]ₛ [pair]ₛ) : SYNT C) :=
      globalElt_congr (by simp only [pair, quote_eq_expr])
    _ = GlobalElt pair ≫ MonoidalClosed.uncurry' (GlobalElt f) := globalElt_app f pair
    _ = CartesianMonoidalCategory.lift (GlobalElt a) (GlobalElt b)
          ≫ MonoidalClosed.uncurry' (GlobalElt f) :=
      congrArg (· ≫ MonoidalClosed.uncurry' (GlobalElt f)) (globalElt_pair a b)

lemma globalElt_delay {τ : TYPE.{i}} (c : SYNT τ) :
    GlobalElt (box(delay [c]ₛ) : SYNT (TYPE.later τ)) = GlobalElt c ≫ next.app ⟦τ⟧ₜ := by
  obtain ⟨m, hm⟩ := synt_interp_delay_factors c
  simp only [GlobalElt, hm]
  exact interp_delay_point_eq_next m (synt_interp c)
    (CartesianMonoidalCategory.lift (𝟙 _) earlier_terminal.inv)

lemma globalElt_app_delay {A B : TYPE.{i}} (f : SYNT (TYPE.arr (TYPE.later A) B))
    (c : SYNT A) :
    GlobalElt (box([f]ₛ (delay [c]ₛ)) : SYNT B) =
      (GlobalElt c ≫ next.app ⟦A⟧ₜ) ≫ MonoidalClosed.uncurry' (GlobalElt f) := by
  let delayed : SYNT (TYPE.later A) := box(delay [c]ₛ)
  calc
    GlobalElt (box([f]ₛ (delay [c]ₛ)) : SYNT B) =
        GlobalElt (box([f]ₛ [delayed]ₛ) : SYNT B) :=
      globalElt_congr (by simp only [delayed, quote_eq_expr])
    _ = GlobalElt delayed ≫ MonoidalClosed.uncurry' (GlobalElt f) := globalElt_app f delayed
    _ = (GlobalElt c ≫ next.app ⟦A⟧ₜ) ≫ MonoidalClosed.uncurry' (GlobalElt f) :=
      congrArg (· ≫ MonoidalClosed.uncurry' (GlobalElt f)) (globalElt_delay c)

lemma globalElt_app_delayed_pair {A B C : TYPE.{i}}
    (f : SYNT (TYPE.arr (TYPE.prod (TYPE.later A) (TYPE.later B)) C))
    (a : SYNT A) (b : SYNT B) :
    GlobalElt (box([f]ₛ ⟨delay [a]ₛ, delay [b]ₛ⟩) : SYNT C) =
      CartesianMonoidalCategory.lift (GlobalElt a ≫ next.app ⟦A⟧ₜ)
          (GlobalElt b ≫ next.app ⟦B⟧ₜ) ≫ MonoidalClosed.uncurry' (GlobalElt f) := by
  let delayedA : SYNT (TYPE.later A) := box(delay [a]ₛ)
  let delayedB : SYNT (TYPE.later B) := box(delay [b]ₛ)
  calc
    GlobalElt (box([f]ₛ ⟨delay [a]ₛ, delay [b]ₛ⟩) : SYNT C) =
        GlobalElt (box([f]ₛ ⟨[delayedA]ₛ, [delayedB]ₛ⟩) : SYNT C) :=
      globalElt_congr (by simp only [delayedA, delayedB, quote_eq_expr])
    _ = CartesianMonoidalCategory.lift (GlobalElt delayedA) (GlobalElt delayedB)
          ≫ MonoidalClosed.uncurry' (GlobalElt f) := globalElt_app_pair f delayedA delayedB
    _ = CartesianMonoidalCategory.lift (GlobalElt a ≫ next.app ⟦A⟧ₜ)
          (GlobalElt b ≫ next.app ⟦B⟧ₜ) ≫ MonoidalClosed.uncurry' (GlobalElt f) :=
      congrArg (· ≫ MonoidalClosed.uncurry' (GlobalElt f))
        (congrArg₂ CartesianMonoidalCategory.lift (globalElt_delay a) (globalElt_delay b))

lemma ax_interp {A : TYPE.{i}} (Γ : CTX.{i}) (f : 𝟙_ ℐ.{i} ⟶ ⟦A⟧ₜ) :
    expr_interp Γ (EXPR.ax A f) A = Part.some (toUnit ⟦Γ⟧ₛ ≫ f) := by
  rw [show expr_interp Γ (EXPR.ax A f) A
        = Part.assert (A = A)
            (fun Heq => pure (toUnit ⟦Γ⟧ₛ ≫ f ≫ eqToHom (congr_arg interp_ty Heq)))
      from rfl, Part.assert_pos (rfl : A = A)]
  simp only [eqToHom_refl, Category.comp_id]
  rfl

lemma globalElt_ax {A : TYPE.{i}} (c : SYNT A) (f : 𝟙_ ℐ.{i} ⟶ ⟦A⟧ₜ)
    (h : c.expr = EXPR.ax A f) : GlobalElt c = f := by
  have hi : expr_interp [[]] c.expr A = Part.some (toUnit ⟦[[]]⟧ₛ ≫ f) := by
    rw [h]
    exact ax_interp [[]] f
  unfold GlobalElt
  rw [synt_interp_eq_of_expr_interp c hi]
  have hunit : CartesianMonoidalCategory.lift (𝟙 (𝟙_ ℐ.{i})) earlier_terminal.inv
        ≫ CartesianMonoidalCategory.toUnit (⟦[[]]⟧ₛ : ℐ.{i})
      = CartesianMonoidalCategory.toUnit (𝟙_ ℐ.{i}) :=
    CartesianMonoidalCategory.toUnit_unique _ _
  exact congrArg (· ≫ f) hunit |>.trans (by
    rw [CartesianMonoidalCategory.toUnit_unit, Category.id_comp])

lemma interp_app_curry {A B : TYPE.{i}} {Γ : CTX.{i}} (k : ⟦A⟧ₜ ⟶ ⟦B⟧ₜ) (g : ⟦Γ⟧ₛ ⟶ ⟦A⟧ₜ) :
    interp_app (toUnit ⟦Γ⟧ₛ ≫ MonoidalClosed.curry' k) g = g ≫ k :=
  (const_app g (MonoidalClosed.curry' k)).trans
    (congrArg (g ≫ ·) (MonoidalClosed.uncurry'_curry' k))

lemma app_curry_interp {A B : TYPE.{i}} (Γ : CTX.{i}) (k : ⟦A⟧ₜ ⟶ ⟦B⟧ₜ)
    (a : EXPR.{i}) {g : ⟦Γ⟧ₛ ⟶ ⟦A⟧ₜ} (ha : expr_interp Γ a A = Part.some g) :
    expr_interp Γ (EXPR.app A (EXPR.ax (TYPE.arr A B) (MonoidalClosed.curry' k)) a) B
      = Part.some (g ≫ k) := by
  show (expr_interp Γ (EXPR.ax (TYPE.arr A B) (MonoidalClosed.curry' k)) (TYPE.arr A B)).bind
          (fun e1 => (expr_interp Γ a A).bind (fun e2 => Part.some (interp_app e1 e2))) = _
  rw [ax_interp, ha, Part.bind_some, Part.bind_some]
  exact congrArg Part.some (interp_app_curry k g)

end global

end
