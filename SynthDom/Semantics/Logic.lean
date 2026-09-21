module

public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Equivalence

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

public import Mathlib.CategoryTheory.Sites.Sieves

public import Mathlib.Tactic

@[expose] public section

namespace Logic
  open CategoryTheory
  open Opposite
  open Functor
  open MonoidalCategory
  open CartesianMonoidalCategory

  variable {C : Type} [Category.{0, 0} C]

  @[simp]
  def subobject_classifier_psh.{u} : Cᵒᵖ ⥤ Type u :=
  {
    obj x := ULift (Sieve x.unop)
    map f := ↾(fun s : ULift (Sieve _) ↦ ULift.up (Sieve.pullback f.unop s.down))
  }

  notation "Ω" => subobject_classifier_psh

  section constructors
    variable {C : Type} [Category.{0, 0} C]

    variable {Γ : Cᵒᵖ ⥤ Type u}

    def entails (P Q : Γ ⟶ Ω) : Prop :=
      ∀ n γ (m : C) (f : m ⟶ n), (P.app (op n) γ : ULift (Sieve n)).down.arrows f →
        (Q.app (op n) γ : ULift (Sieve n)).down.arrows f

    infix:99 " ⊢ᵢ " => entails

    lemma entails_refl (P : Γ ⟶ Ω) : P ⊢ᵢ P := fun _ _ _ _ h => h

    lemma entails_trans (P Q R : Γ ⟶ Ω) : P ⊢ᵢ Q → Q ⊢ᵢ R → P ⊢ᵢ R :=
      fun h₁ h₂ _ _ _ _ h => h₂ _ _ _ _ (h₁ _ _ _ _ h)

    lemma entails_subst {A : Cᵒᵖ ⥤ Type u} (t : Γ ⟶ A) (P Q : A ⟶ Ω) :
      P ⊢ᵢ Q → (t ≫ P) ⊢ᵢ (t ≫ Q) := fun h _ _ _ _ h' => h _ _ _ _ h'

    def eqI {X : Cᵒᵖ ⥤ Type u} : (X ⊗ X) ⟶ Ω :=
      {
        app := λ x ↦ ↾(fun y ↦ ULift.up $ Sieve.mk (λ p t ↦ X.map t.op y.1 = X.map t.op y.2)
          (
            by
              intro Y Z f x_1 g
              simp_all only [op_unop, op_comp, CategoryTheory.Functor.map_comp_apply]
          ))
      }

    def eq {A : Cᵒᵖ ⥤ Type u} (t u : Γ ⟶ A) : Γ ⟶ Ω := (lift t u) ≫ eqI

    infix:70 " ≡ᵢ " => eq

    def true_arr : (𝟙_ (Cᵒᵖ ⥤ Type u)) ⟶ Ω :=
      { app := λ _ ↦ ↾(fun _ ↦ ULift.up (⊤ : Sieve _)) }

    def true : Γ ⟶ Ω := (toUnit _) ≫ true_arr

    notation "⊤ᵢ" => true

    def falseI : (𝟙_ (Cᵒᵖ ⥤ Type u)) ⟶ Ω :=
      { app := λ _ ↦ ↾(fun _ ↦ ULift.up (⊥ : Sieve _)) }

    def false : Γ ⟶ Ω := (toUnit _) ≫ falseI

    notation "⊥ᵢ" => false

    def conj_arr : (Ω ⊗ Ω : Cᵒᵖ ⥤ Type u) ⟶ Ω :=
      { app := λ _ ↦ ↾(fun y ↦ ULift.up (y.1.down ⊓ y.2.down : Sieve _)) }

    def conj (P Q : Γ ⟶ Ω) : Γ ⟶ Ω := (lift P Q) ≫ conj_arr

    infix:80 " ∧ᵢ " => conj

    lemma lift_app {A B Δ : Cᵒᵖ ⥤ Type u} (P : Δ ⟶ A) (Q : Δ ⟶ B) (x : Cᵒᵖ) :
        (CartesianMonoidalCategory.lift P Q).app x
          = CartesianMonoidalCategory.lift (P.app x) (Q.app x) := by
      apply CartesianMonoidalCategory.hom_ext
      · have h := congrArg (·.app x) (CartesianMonoidalCategory.lift_fst P Q)
        simp only [NatTrans.comp_app, CategoryTheory.Functor.Monoidal.fst_app] at h
        rw [CartesianMonoidalCategory.lift_fst]; exact h
      · have h := congrArg (·.app x) (CartesianMonoidalCategory.lift_snd P Q)
        simp only [NatTrans.comp_app, CategoryTheory.Functor.Monoidal.snd_app] at h
        rw [CartesianMonoidalCategory.lift_snd]; exact h

    lemma conj_app (P Q : Γ ⟶ Ω) (x : Cᵒᵖ) (a : Γ.obj x) :
        (ConcreteCategory.hom ((P ∧ᵢ Q).app x)) a
          = ULift.up ((ConcreteCategory.hom (P.app x) a).down
              ⊓ (ConcreteCategory.hom (Q.app x) a).down) := by
      have hfst := types_congr_hom (CartesianMonoidalCategory.lift_fst (P.app x) (Q.app x)) a
      have hsnd := types_congr_hom (CartesianMonoidalCategory.lift_snd (P.app x) (Q.app x)) a
      simp only [types_comp_apply] at hfst hsnd
      simp only [conj, conj_arr, NatTrans.comp_app, lift_app]
      rw [← hfst, ← hsnd]
      rfl

    lemma true_app (x : Cᵒᵖ) (a : Γ.obj x) :
        (ConcreteCategory.hom ((⊤ᵢ : Γ ⟶ Ω).app x)) a = ULift.up (⊤ : Sieve _) := by
      simp only [true, true_arr, NatTrans.comp_app, ConcreteCategory.comp_apply,
        ConcreteCategory.hom_ofHom]
      rfl

    def disjI : (Ω ⊗ Ω : Cᵒᵖ ⥤ Type u) ⟶ Ω :=
      { app := λ _ ↦ ↾(fun y ↦ ULift.up (y.1.down ⊔ y.2.down : Sieve _)) }

    def disj (P Q : Γ ⟶ Ω) : Γ ⟶ Ω := (lift P Q) ≫ disjI

    infix:85 " ∨ᵢ " => disj

    lemma disj_app (P Q : Γ ⟶ Ω) (x : Cᵒᵖ) (a : Γ.obj x) :
        (ConcreteCategory.hom ((P ∨ᵢ Q).app x)) a
          = ULift.up ((ConcreteCategory.hom (P.app x) a).down
              ⊔ (ConcreteCategory.hom (Q.app x) a).down) := by
      have hfst := types_congr_hom (CartesianMonoidalCategory.lift_fst (P.app x) (Q.app x)) a
      have hsnd := types_congr_hom (CartesianMonoidalCategory.lift_snd (P.app x) (Q.app x)) a
      simp only [types_comp_apply] at hfst hsnd
      simp only [disj, disjI, NatTrans.comp_app, lift_app]
      rw [← hfst, ← hsnd]
      rfl

    def implI : (Ω ⊗ Ω : Cᵒᵖ ⥤ Type u) ⟶ Ω :=
      {
        app := λ _ ↦ ↾(fun y ↦ ULift.up $ Sieve.mk (λ p t ↦ ∀ {q} (e : q ⟶ p), y.1.down.arrows (e ≫ t) → y.2.down.arrows (e ≫ t))
          (
            by
              intro X Y f H g q e a
              rw [<-Category.assoc]
              apply H
              rw [Category.assoc]
              apply a
          ))
        naturality := by
          intros X Y f
          simp only [Functor.Monoidal.tensorObj_map, Functor.Monoidal.tensorObj_obj]
          ext ⟨y1, y2⟩
          apply ULift.ext
          apply Sieve.ext
          intro q e
          show (∀ {q_1 : C} (e_1 : q_1 ⟶ q),
            (Sieve.pullback f.unop y1.down).arrows (e_1 ≫ e) →
            (Sieve.pullback f.unop y2.down).arrows (e_1 ≫ e)) ↔
            (∀ {q_1 : C} (e_1 : q_1 ⟶ q),
            y1.down.arrows (e_1 ≫ e ≫ f.unop) → y2.down.arrows (e_1 ≫ e ≫ f.unop))
          simp only [Sieve.pullback_apply, Category.assoc]
      }

    def impl (P Q : Γ ⟶ Ω) : Γ ⟶ Ω := (lift P Q) ≫ implI

    infix:90 " →ᵢ " => impl

    def all_arr {X : Cᵒᵖ ⥤ Type u} : ((ihom X).obj Ω) ⟶ Ω :=
      {
        app := λ x ↦ ↾(fun y ↦ ULift.up $ Sieve.mk (λ p t ↦ ∀ {q} (e : q ⟶ p) (r : X.obj (op q)),
              ((y.app (op q) (t.op ≫ e.op) r : ULift (Sieve q)).down.arrows (𝟙 q)))
          (
            by
              intro Y Z f H g q e r; simp
              simp_all only
              apply H
          ))
      }

    def all A (P : (A ⊗ Γ) ⟶ Ω) : Γ ⟶ Ω :=
      MonoidalClosed.curry P ≫ all_arr

    notation "∀ᵢ[" A "] " P => all A P

    lemma all_natural {A Γ' : Cᵒᵖ ⥤ Type u} (g : Γ' ⟶ Γ) (P : (A ⊗ Γ) ⟶ Ω) :
        g ≫ all A P = all A (A ◁ g ≫ P) := by
      simp only [all, MonoidalClosed.curry_natural_left, Category.assoc]

    def exist_arr {X : Cᵒᵖ ⥤ Type u} : ((ihom X).obj Ω) ⟶ Ω :=
      {
        app := λ x ↦ ↾(fun y ↦ ULift.up $ Sieve.mk (λ p t ↦ ∃ (r : X.obj (op p)),
              ((y.app (op p) t.op r : ULift (Sieve p)).down.arrows (𝟙 p)))
          (
            by
              intro Y Z f H g
              obtain ⟨r, H⟩ := H
              refine ⟨X.map g.op r, ?_⟩
              have nat' : y.app (op Z) (g ≫ f).op (X.map g.op r) =
                  subobject_classifier_psh.map g.op (y.app (op Y) f.op r) := by
                have raw := HomObj.naturality y g.op f.op
                have key : (ConcreteCategory.hom ((unop (coyoneda.rightOp.obj x)).map g.op)) f.op =
                    (g ≫ f).op := by
                  show (ConcreteCategory.hom ((unop (coyoneda.rightOp.obj x)).map g.op)) f.op =
                    f.op ≫ g.op
                  change f.op ≫ g.op = f.op ≫ g.op
                  rfl
                rw [← key]
                exact types_congr_hom raw r
              rw [nat']
              simp only [subobject_classifier_psh, ConcreteCategory.hom_ofHom]
              show (Sieve.pullback g ((ConcreteCategory.hom (y.app (op Y) f.op)) r).down).arrows (𝟙 Z)
              rw [Sieve.pullback_apply, Category.id_comp]
              simpa [Category.comp_id] using (y.app (op Y) f.op r).down.downward_closed H g
          ))
      }

    def exist A (P : (A ⊗ Γ) ⟶ Ω) : Γ ⟶ Ω :=
      MonoidalClosed.curry P ≫ exist_arr

    notation "∃ᵢ[" A "] " P => exist A P

    lemma exist_natural {A Γ' : Cᵒᵖ ⥤ Type u} (g : Γ' ⟶ Γ) (P : (A ⊗ Γ) ⟶ Ω) :
        g ≫ exist A P = exist A (A ◁ g ≫ P) := by
      simp only [exist, MonoidalClosed.curry_natural_left, Category.assoc]

    def pureI (P : Prop) : (𝟙_ (Cᵒᵖ ⥤ Type u)) ⟶ Ω :=
      {
        app := λ _ ↦ ↾(fun _ ↦ ULift.up $ Sieve.mk (λ p t ↦ P)
          (
            by
              intro X Y f x_1 g
              assumption
          ))
      }

    def pure (P : Prop) : Γ ⟶ Ω :=
      (toUnit _) ≫ pureI P

    notation "⌜" P "⌝ᵢ" => pure P

  end constructors

  section rules
    variable {C : Type} [Category C]

    variable {Γ : Cᵒᵖ ⥤ Type u}

    lemma eq_refl {A} (t : Γ ⟶ A) :
      ⊤ᵢ ⊢ᵢ (t ≡ᵢ t) := fun _ _ _ _ _ => rfl

    @[simp]
    lemma lift_app_fst {A} (t : Γ ⟶ A) : ((lift t u).app n γ).1 = t.app n γ := rfl

    @[simp]
    lemma lift_app_snd {A} (u : Γ ⟶ A) : ((lift t u).app n γ).2 = u.app n γ := rfl

    lemma eq_sym {A} (t u : Γ ⟶ A) :
      (t ≡ᵢ u) ⊢ᵢ (u ≡ᵢ t) := by
      intros _ _ _ _ H
      simp only [eq, eqI, subobject_classifier_psh] at H ⊢
      exact H.symm

    lemma eq_trans {A} (t u v : Γ ⟶ A) :
      ((t ≡ᵢ u) ∧ᵢ (u ≡ᵢ v)) ⊢ᵢ (t ≡ᵢ v) := by
      intros _ _ _ _ H
      simp only [conj, conj_arr, eq, eqI, subobject_classifier_psh] at H ⊢
      exact H.1.trans H.2

    lemma eq_subst {A B} (t u : Γ ⟶ A) (D : A ⟶ B) :
      (t ≡ᵢ u) ⊢ᵢ ((t ≫ D) ≡ᵢ (u ≫ D)) := by
      intros n γ m f He
      simp only [eq, eqI, subobject_classifier_psh, NatTrans.comp_app] at He
      show (B.map f.op (D.app (op n) (t.app (op n) γ)) = B.map f.op (D.app (op n) (u.app (op n) γ)))
      rw [← CategoryTheory.NatTrans.naturality_apply D f.op (t.app (op n) γ),
          ← CategoryTheory.NatTrans.naturality_apply D f.op (u.app (op n) γ)]
      exact congrArg _ He

    lemma eq_coerce (P Q : Γ ⟶ Ω) :
      ((P ≡ᵢ Q) ∧ᵢ P) ⊢ᵢ Q := by
      intros n γ m f H
      simp only [conj, conj_arr, NatTrans.comp_app, comp_apply] at H
      obtain ⟨hH_eq, hH_p⟩ := H
      rw [show (ConcreteCategory.hom ((lift (P ≡ᵢ Q) P).app (op n)) γ).1 =
          (P ≡ᵢ Q).app (op n) γ from rfl] at hH_eq
      rw [show (ConcreteCategory.hom ((lift (P ≡ᵢ Q) P).app (op n)) γ).2 =
          P.app (op n) γ from rfl] at hH_p
      have hse : Sieve.pullback f (P.app (op n) γ).down =
          Sieve.pullback f (Q.app (op n) γ).down := by
        simp only [eq, NatTrans.comp_app, comp_apply] at hH_eq
        rw [show (ConcreteCategory.hom ((lift P Q).app (op n)) γ) =
            (P.app (op n) γ, Q.app (op n) γ) from rfl] at hH_eq
        simp only [eqI] at hH_eq
        simp only [subobject_classifier_psh, ConcreteCategory.hom_ofHom] at hH_eq
        exact congr_arg ULift.down hH_eq
      have hmem : (Sieve.pullback f (P.app (op n) γ).down).arrows (𝟙 m) := by
        simp only [Sieve.pullback_apply, Category.id_comp]; exact hH_p
      rw [hse] at hmem
      simpa [Sieve.pullback_apply] using hmem

    lemma true_intro {P : Γ ⟶ Ω} :
      P ⊢ᵢ ⊤ᵢ := fun _ _ _ _ _ => ⟨⟩

    lemma false_elim {P : Γ ⟶ Ω} :
      ⊥ᵢ ⊢ᵢ P := fun _ _ _ _ h => h.elim

    lemma conj_intro {R P Q : Γ ⟶ Ω} :
      R ⊢ᵢ P →
      R ⊢ᵢ Q →
      R ⊢ᵢ (P ∧ᵢ Q) := fun hP hQ _ _ _ _ hR => ⟨hP _ _ _ _ hR, hQ _ _ _ _ hR⟩

    lemma conj_elim_l {P Q : Γ ⟶ Ω} :
      (P ∧ᵢ Q) ⊢ᵢ P := fun _ _ _ _ h => h.1

    lemma conj_elim_r {P Q : Γ ⟶ Ω} :
      (P ∧ᵢ Q) ⊢ᵢ Q := fun _ _ _ _ h => h.2

    lemma disj_intro_l {P Q : Γ ⟶ Ω} :
      P ⊢ᵢ (P ∨ᵢ Q) := fun _ _ _ _ Px => Or.inl Px

    lemma disj_intro_r {P Q : Γ ⟶ Ω} :
      Q ⊢ᵢ (P ∨ᵢ Q) := fun _ _ _ _ Qx => Or.inr Qx

    lemma disj_elim {P Q R : Γ ⟶ Ω} :
      P ⊢ᵢ R →
      Q ⊢ᵢ R →
      (P ∨ᵢ Q) ⊢ᵢ R := fun hP hQ _ _ _ _ h => h.elim (hP _ _ _ _) (hQ _ _ _ _)

    lemma impl_intro {P Q R : Γ ⟶ Ω} :
      (R ∧ᵢ P) ⊢ᵢ Q →
      R ⊢ᵢ (P →ᵢ Q) := by
      intros h n γ m f Rx j Hj Px
      apply (h n γ j (Hj ≫ f))
      constructor
      . apply (R.app (op n) γ).down.downward_closed Rx Hj
      . apply Px

    lemma impl_elim {P Q : Γ ⟶ Ω} :
      ((P →ᵢ Q) ∧ᵢ P) ⊢ᵢ Q := by
      intros n γ m f h
      cases h with
      | intro H Px =>
      rw [<-Category.id_comp f]
      apply H
      rw [Category.id_comp]
      apply Px

    private lemma curry_eval_aux {A : Cᵒᵖ ⥤ Type u} (P : (A ⊗ Γ) ⟶ Ω)
        (X : Cᵒᵖ) (γ : Γ.obj X) (Y : Cᵒᵖ)
        (f : (Opposite.unop (Functor.rightOp coyoneda |>.obj X)).obj Y) (ay : A.obj Y) :
        ConcreteCategory.hom ((ConcreteCategory.hom ((MonoidalClosed.curry P).app X) γ).app Y f) ay =
        ConcreteCategory.hom (P.app Y) (ay, ConcreteCategory.hom (Γ.map f) γ) := by
      rw [show MonoidalClosed.curry P = (FunctorToTypes.functorHomEquiv A Γ Ω).symm P by
        apply (FunctorToTypes.functorHomEquiv A Γ Ω).injective
        simp only [Equiv.apply_symm_apply]
        exact MonoidalClosed.uncurry_curry P]
      rfl

    lemma all_intro {A : Cᵒᵖ ⥤ Type u} (R : Γ ⟶ Ω) (P : (A ⊗ Γ) ⟶ Ω) :
      ((snd _ _) ≫ R) ⊢ᵢ P → R ⊢ᵢ ∀ᵢ[A] P := by
      intros h n γ m f Rx j Hj y
      simp only
      suffices key : (ConcreteCategory.hom (P.app (op j)))
          (y, (ConcreteCategory.hom (Γ.map (f.op ≫ Hj.op))) γ) |>.down.arrows (𝟙 j) by
        exact (curry_eval_aux P (op n) γ (op j) (f.op ≫ Hj.op) y ▸ key)
      apply h j (y, (ConcreteCategory.hom (Γ.map (f.op ≫ Hj.op))) γ) j (𝟙 j)
      show ((ConcreteCategory.hom (R.app (op j)))
          ((ConcreteCategory.hom (Γ.map (f.op ≫ Hj.op))) γ)).down.arrows (𝟙 j)
      rw [NatTrans.naturality_apply R (f.op ≫ Hj.op) γ]
      show (Sieve.pullback (f.op ≫ Hj.op).unop (R.app (op n) γ).down).arrows (𝟙 j)
      simp only [Sieve.pullback_apply, Category.id_comp, Opposite.unop_op]
      exact (R.app (op n) γ).down.downward_closed Rx Hj

    lemma all_elim {A : Cᵒᵖ ⥤ Type u} (P : (A ⊗ Γ) ⟶ Ω) (t : Γ ⟶ A) :
      (∀ᵢ[A] P) ⊢ᵢ ((lift t (𝟙 _)) ≫ P) := by
      intros n γ m f H
      specialize H (𝟙 m) ((t.app (op m)) ((Γ.map f.op) γ))
      simp only [NatTrans.comp_app, comp_apply]
      suffices key : ((ConcreteCategory.hom (P.app (op m)))
          ((ConcreteCategory.hom ((lift t (𝟙 Γ)).app (op m)))
            ((ConcreteCategory.hom (Γ.map f.op)) γ))).down.arrows (𝟙 m) by
        have sieve_eq : ((ConcreteCategory.hom (P.app (op m)))
            ((ConcreteCategory.hom ((lift t (𝟙 Γ)).app (op m)))
              ((ConcreteCategory.hom (Γ.map f.op)) γ))).down =
            Sieve.pullback f ((ConcreteCategory.hom (P.app (op n)))
              ((ConcreteCategory.hom ((lift t (𝟙 Γ)).app (op n))) γ)).down := by
          have nat := NatTrans.naturality_apply (lift t (𝟙 Γ) ≫ P) f.op γ
          simp only [NatTrans.comp_app, comp_apply] at nat
          have h := congrArg ULift.down nat
          simp only [subobject_classifier_psh, Opposite.unop_op] at h
          exact h
        rw [sieve_eq] at key
        simp only [Sieve.pullback_apply, Category.id_comp] at key
        exact key
      rw [show (ConcreteCategory.hom ((lift t (𝟙 Γ)).app (op m)))
          ((ConcreteCategory.hom (Γ.map f.op)) γ) =
          (t.app (op m) ((ConcreteCategory.hom (Γ.map f.op)) γ),
           (ConcreteCategory.hom (Γ.map f.op)) γ) from rfl]
      simp only at H
      have H' : ((ConcreteCategory.hom (P.app (op m)))
          ((ConcreteCategory.hom (t.app (op m))) ((ConcreteCategory.hom (Γ.map f.op)) γ),
           (ConcreteCategory.hom (Γ.map (f.op ≫ (𝟙 m).op))) γ)).down.arrows (𝟙 m) :=
        curry_eval_aux P (op n) γ (op m) (f.op ≫ (𝟙 m).op)
          (t.app (op m) ((ConcreteCategory.hom (Γ.map f.op)) γ)) ▸ H
      rwa [show (ConcreteCategory.hom (Γ.map (f.op ≫ (𝟙 m).op))) γ =
          (ConcreteCategory.hom (Γ.map f.op)) γ by simp [op_id]] at H'

    lemma pure_intro {P : Γ ⟶ Ω} {Q : Prop} (q : Q) :
      P ⊢ᵢ ⌜ Q ⌝ᵢ := fun _ _ _ _ _ => q

    lemma pure_elim {P : Γ ⟶ Ω} (φ : Prop) :
      (φ → ⊤ᵢ ⊢ᵢ P) → (⌜ φ ⌝ᵢ) ⊢ᵢ P := fun h _ _ _ _ hφ => h hφ _ _ _ _ ⟨⟩

    lemma soundness {P : Prop} (n : C) :
      ((⊤ᵢ : (𝟙_ (Cᵒᵖ ⥤ Type u)) ⟶ Ω) ⊢ᵢ ⌜ P ⌝ᵢ) → P :=
      fun h => h n PUnit.unit n (𝟙 n) ⟨⟩

    lemma soundness_eq {A : Cᵒᵖ ⥤ Type u} (t u : Γ ⟶ A) :
      ⊤ᵢ ⊢ᵢ (t ≡ᵢ u) → t = u := by
      intros H
      ext x y
      specialize H x.unop y x.unop (𝟙 x.unop) ⟨⟩
      simp only [eq, NatTrans.comp_app, comp_apply] at H
      rw [show (ConcreteCategory.hom ((lift t u).app x) y) =
          (t.app x y, u.app x y) from rfl] at H
      simp only [eqI] at H
      change ConcreteCategory.hom (A.map (𝟙 x.unop).op) (t.app x y) =
        ConcreteCategory.hom (A.map (𝟙 x.unop).op) (u.app x y) at H
      simpa [Functor.map_id_apply] using H

  end rules

  section wrappers
    variable {C : Type} [Category C]

    variable {Γ : Cᵒᵖ ⥤ Type u}

    lemma false_elim' (R P : Γ ⟶ Ω) :
      R ⊢ᵢ ⊥ᵢ →
      R ⊢ᵢ P := fun h => entails_trans _ _ _ h false_elim

    lemma conj_true_l_inv (P : Γ ⟶ Ω) :
      P ⊢ᵢ (⊤ᵢ ∧ᵢ P) := conj_intro true_intro (entails_refl P)

    lemma conj_true_r_inv (P : Γ ⟶ Ω) :
      P ⊢ᵢ (P ∧ᵢ ⊤ᵢ) := conj_intro (entails_refl P) true_intro

    lemma conj_comm (P Q : Γ ⟶ Ω) :
      (P ∧ᵢ Q) ⊢ᵢ (Q ∧ᵢ P) := conj_intro conj_elim_r conj_elim_l

    lemma disj_elim_ctx {P Q R S : Γ ⟶ Ω}
        (h : R ⊢ᵢ (P ∨ᵢ Q))
        (h1 : (R ∧ᵢ P) ⊢ᵢ S)
        (h2 : (R ∧ᵢ Q) ⊢ᵢ S) :
        R ⊢ᵢ S := by
      exact entails_trans _ _ _ (conj_intro (entails_trans _ _ _ h
        (disj_elim (impl_intro (entails_trans _ _ _ (conj_comm P R) h1))
          (impl_intro (entails_trans _ _ _ (conj_comm Q R) h2)))) (entails_refl R)) impl_elim

    lemma conj_mono (P P' Q Q' : Γ ⟶ Ω) :
      P ⊢ᵢ P' →
      Q ⊢ᵢ Q' →
      (P ∧ᵢ Q) ⊢ᵢ (P' ∧ᵢ Q') :=
      fun h1 h2 => conj_intro (entails_trans _ _ _ conj_elim_l h1)
        (entails_trans _ _ _ conj_elim_r h2)

    lemma conj_mono_l (P P' Q : Γ ⟶ Ω) :
      P ⊢ᵢ P' →
      (P ∧ᵢ Q) ⊢ᵢ (P' ∧ᵢ Q) := fun h => conj_mono _ _ _ _ h (entails_refl Q)

    lemma conj_mono_r (P Q Q' : Γ ⟶ Ω) :
      Q ⊢ᵢ Q' →
      (P ∧ᵢ Q) ⊢ᵢ (P ∧ᵢ Q') := fun h => conj_mono _ _ _ _ (entails_refl P) h

    lemma conj_elim_l' (P Q R : Γ ⟶ Ω) :
      R ⊢ᵢ (P ∧ᵢ Q) →
      R ⊢ᵢ P := fun h => entails_trans _ _ _ h conj_elim_l

    lemma conj_elim_r' (P Q R : Γ ⟶ Ω) :
      R ⊢ᵢ (P ∧ᵢ Q) →
      R ⊢ᵢ Q := fun h => entails_trans _ _ _ h conj_elim_r

    lemma disj_false_l (P : Γ ⟶ Ω) :
      (⊥ᵢ ∨ᵢ P) ⊢ᵢ P := disj_elim false_elim (entails_refl P)

    lemma disj_false_r (P : Γ ⟶ Ω) :
      (P ∨ᵢ ⊥ᵢ) ⊢ᵢ P := disj_elim (entails_refl P) false_elim

    lemma disj_comm (P Q : Γ ⟶ Ω) :
      (P ∨ᵢ Q) ⊢ᵢ (Q ∨ᵢ P) := disj_elim disj_intro_r disj_intro_l

    lemma disj_mono (P P' Q Q' : Γ ⟶ Ω) :
      P ⊢ᵢ P' →
      Q ⊢ᵢ Q' →
      (P ∨ᵢ Q) ⊢ᵢ (P' ∨ᵢ Q') :=
      fun h1 h2 => disj_elim (entails_trans _ _ _ h1 disj_intro_l)
        (entails_trans _ _ _ h2 disj_intro_r)

    lemma disj_mono_l (P P' Q : Γ ⟶ Ω) :
      P ⊢ᵢ P' →
      (P ∨ᵢ Q) ⊢ᵢ (P' ∨ᵢ Q) := fun h => disj_mono _ _ _ _ h (entails_refl Q)

    lemma disj_mono_r (P Q Q' : Γ ⟶ Ω) :
      Q ⊢ᵢ Q' →
      (P ∨ᵢ Q) ⊢ᵢ (P ∨ᵢ Q') := fun h => disj_mono _ _ _ _ (entails_refl P) h

    lemma disj_intro_l' (P Q R : Γ ⟶ Ω) :
      R ⊢ᵢ P →
      R ⊢ᵢ (P ∨ᵢ Q) := fun h => entails_trans _ _ _ h disj_intro_l

    lemma disj_intro_r' (P Q R : Γ ⟶ Ω) :
      R ⊢ᵢ Q →
      R ⊢ᵢ (P ∨ᵢ Q) := fun h => entails_trans _ _ _ h disj_intro_r

    lemma impl_elim' (P Q R : Γ ⟶ Ω) :
      R ⊢ᵢ (P →ᵢ Q) →
      (R ∧ᵢ P) ⊢ᵢ Q := fun h => entails_trans _ _ _ (conj_mono_l _ _ _ h) impl_elim

    lemma entails_impl (P Q : Γ ⟶ Ω) :
      P ⊢ᵢ Q →
      ⊤ᵢ ⊢ᵢ (P →ᵢ Q) := fun h => impl_intro (entails_trans _ _ _ conj_elim_r h)

    lemma impl_entails (P Q : Γ ⟶ Ω) :
      ⊤ᵢ ⊢ᵢ (P →ᵢ Q) →
      P ⊢ᵢ Q := fun h => entails_trans _ _ _ (conj_true_l_inv _) (impl_elim' _ _ _ h)

    lemma all_elim' {A : Cᵒᵖ ⥤ Type u} (P : (A ⊗ Γ) ⟶ Ω)
      (t : Γ ⟶ A) (R : Γ ⟶ Ω) :
      R ⊢ᵢ (∀ᵢ[A] P) →
      R ⊢ᵢ ((lift t (𝟙 _)) ≫ P) := fun h => entails_trans _ _ _ h (all_elim P t)

    lemma exist_intro {A : Cᵒᵖ ⥤ Type u} (P : (A ⊗ Γ) ⟶ Ω) (t : Γ ⟶ A) :
      ((lift t (𝟙 _)) ≫ P) ⊢ᵢ (∃ᵢ[A] P) := by
      intros n γ m f H
      simp only [NatTrans.comp_app, comp_apply] at H
      refine ⟨(ConcreteCategory.hom (t.app (op m))) ((ConcreteCategory.hom (Γ.map f.op)) γ), ?_⟩
      have ce := curry_eval_aux P (op n) γ (op m) f.op
          ((ConcreteCategory.hom (t.app (op m))) ((ConcreteCategory.hom (Γ.map f.op)) γ))
      erw [ce]
      have sieve_eq : ((ConcreteCategory.hom (P.app (op m)))
          ((ConcreteCategory.hom ((lift t (𝟙 Γ)).app (op m)))
            ((ConcreteCategory.hom (Γ.map f.op)) γ))).down =
          Sieve.pullback f ((ConcreteCategory.hom (P.app (op n)))
            ((ConcreteCategory.hom ((lift t (𝟙 Γ)).app (op n))) γ)).down := by
        have nat := NatTrans.naturality_apply (lift t (𝟙 Γ) ≫ P) f.op γ
        simp only [NatTrans.comp_app, comp_apply] at nat
        have h := congrArg ULift.down nat
        simp only [subobject_classifier_psh, Opposite.unop_op] at h
        exact h
      show ((ConcreteCategory.hom (P.app (op m)))
          ((ConcreteCategory.hom ((lift t (𝟙 Γ)).app (op m)))
            ((ConcreteCategory.hom (Γ.map f.op)) γ))).down.arrows (𝟙 m)
      rw [sieve_eq]
      simp only [Sieve.pullback_apply, Category.id_comp]
      exact H

    lemma exist_elim {A : Cᵒᵖ ⥤ Type u} {P : (A ⊗ Γ) ⟶ Ω} {R Q : Γ ⟶ Ω} :
      ((P ∧ᵢ ((snd A Γ) ≫ R)) ⊢ᵢ ((snd A Γ) ≫ Q)) →
      (((∃ᵢ[A] P) ∧ᵢ R) ⊢ᵢ Q) := by
      intros h n γ m f Hx
      obtain ⟨HE, HR⟩ := Hx
      obtain ⟨r, Hr⟩ := HE
      erw [curry_eval_aux P (op n) γ (op m) f.op r] at Hr
      have HRm : ((ConcreteCategory.hom (R.app (op m)))
          ((ConcreteCategory.hom (Γ.map f.op)) γ)).down.arrows (𝟙 m) := by
        have h' := congrArg ULift.down (NatTrans.naturality_apply R f.op γ)
        simp only [subobject_classifier_psh, Opposite.unop_op] at h'
        erw [h']
        show (Sieve.pullback f _).arrows (𝟙 m)
        simp only [Sieve.pullback_apply, Category.id_comp]
        exact HR
      have h' := congrArg ULift.down (NatTrans.naturality_apply Q f.op γ)
      simp only [subobject_classifier_psh, Opposite.unop_op] at h'
      have final : ((ConcreteCategory.hom (Q.app (op n))) γ).down.arrows (𝟙 m ≫ f) :=
        (congrArg (fun s => s.arrows (𝟙 m)) h').mp
          (h m (r, (ConcreteCategory.hom (Γ.map f.op)) γ) m (𝟙 m) ⟨Hr, HRm⟩)
      rwa [Category.id_comp] at final

  end wrappers

end Logic
end
