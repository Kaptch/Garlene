module

public import SynthDom.Semantics.Univ.Core

@[expose] public section

section constructors
  open CategoryTheory Functor MonoidalCategory CartesianMonoidalCategory

  private lemma tensor_eqToHom_ext {C : Type*} [Category C] [MonoidalCategory C]
      {A B D X₁ X₂ Y₁ Y₂ W₁ W₂ : C} (M₁ : X₁ ⟶ Y₁) (M₂ : X₂ ⟶ Y₂)
      (p : A = X₁ ⊗ X₂) (s : Y₁ ⊗ Y₂ = D) (t : D = B)
      (p' : A = X₁ ⊗ X₂) (f₁ : Y₁ = W₁) (f₂ : Y₂ = W₂) (q' : W₁ ⊗ W₂ = B) :
      (eqToHom p ≫ (M₁ ⊗ₘ M₂) ≫ eqToHom s) ≫ eqToHom t =
        eqToHom p' ≫ ((M₁ ≫ eqToHom f₁) ⊗ₘ (M₂ ≫ eqToHom f₂)) ≫ eqToHom q' := by
    subst f₁ f₂ s t
    simp

  unseal U in
  @[irreducible]
  def U_discrete (A : Type i) : 𝟙_ ℐ.{i + 1} ⟶ U.{i} where
    app i := ↾(fun _ => (const _).obj A)
  unseal classify U U_discrete in
  @[simp]
  lemma U_discrete_push {A : Type i}
    : classify.hom (U_discrete A) = discrete.obj A := by
    refine CategoryTheory.Functor.ext (fun j => rfl) ?_
    intro A' B φ
    rfl

  unseal U in
  @[irreducible]
  def U_prod' : U.{i} ⊗ U.{i} ⟶ U.{i} where
    app i := ↾(fun x => Functor.diag _ ⋙ Functor.prod x.1 x.2 ⋙ tensor _)
    naturality {X Y} f := by
      refine ConcreteCategory.hom_ext _ _ fun x => ?_
      rfl
  @[irreducible]
  def U_prod : 𝟙_ _ ⟶ (ihom (U.{i} ⊗ U.{i})).obj U.{i} := MonoidalClosed.curry' U_prod'
  unseal U U_prod U_prod' in
  lemma U_prod_el {τ1 τ2 : 𝟙_ ℐ.{i + 1} ⟶ U.{i}} (a : ℕᵒᵖ) :
      U.el (ConcreteCategory.hom ((CartesianMonoidalCategory.lift τ1 τ2 ≫ MonoidalClosed.uncurry' U_prod).app a) (unitPt a)) =
        Functor.diag _ ⋙ Functor.prod (U.el (ConcreteCategory.hom (τ1.app a) (unitPt a)))
          (U.el (ConcreteCategory.hom (τ2.app a) (unitPt a))) ⋙ tensor (Type i) := by
    rw [U_prod, MonoidalClosed.uncurry'_curry']; rfl

  unseal classify U U_prod U_prod' in
  @[simp]
  lemma U_prod_push {τ1 τ2 : 𝟙_ ℐ.{i + 1} ⟶ U.{i}}
    : classify.hom (CartesianMonoidalCategory.lift τ1 τ2 ≫ MonoidalClosed.uncurry' U_prod) = (classify.hom τ1) ⊗ (classify.hom τ2) := by
    refine CategoryTheory.Functor.ext (fun j => rfl) ?_
    intro a b φ
    simp only [Functor.Monoidal.tensorObj_map, classify_hom_map]
    rw [Functor.congr_hom (U_prod_el (τ1 := τ1) (τ2 := τ2) a)]
    simp only [Functor.comp_map, Functor.prod_map, Functor.diag_map, MonoidalCategory.tensor_map]
    exact tensor_eqToHom_ext _ _ _ _ _ _ _ _ _

  unseal U in
  @[irreducible]
  def U_sum' : U.{i} ⊗ U.{i} ⟶ U.{i} where
    app i := ↾(fun x => FunctorToTypes.coprod x.1 x.2)
    naturality {X Y} f := by
      refine ConcreteCategory.hom_ext _ _ fun x => ?_
      rfl
  @[irreducible]
  def U_sum : 𝟙_ _ ⟶ (ihom (U.{i} ⊗ U.{i})).obj U.{i} := MonoidalClosed.curry' U_sum'

  unseal U U_sum U_sum' in
  lemma U_sum_el {τ1 τ2 : 𝟙_ ℐ.{i + 1} ⟶ U.{i}} (a : ℕᵒᵖ) :
      U.el (ConcreteCategory.hom ((CartesianMonoidalCategory.lift τ1 τ2 ≫ MonoidalClosed.uncurry' U_sum).app a) (unitPt a)) =
        FunctorToTypes.coprod (U.el (ConcreteCategory.hom (τ1.app a) (unitPt a)))
          (U.el (ConcreteCategory.hom (τ2.app a) (unitPt a))) := by
    rw [U_sum, MonoidalClosed.uncurry'_curry']; rfl

  private lemma sum_eqToHom_ext {X₁ X₂ Y₁ Y₂ W₁ W₂ A B D : Type u}
      (M₁ : X₁ ⟶ Y₁) (M₂ : X₂ ⟶ Y₂)
      (p : A = (X₁ ⊕ X₂)) (s : (Y₁ ⊕ Y₂) = D) (t : D = B)
      (p' : A = (X₁ ⊕ X₂)) (f₁ : Y₁ = W₁) (f₂ : Y₂ = W₂) (q' : (W₁ ⊕ W₂) = B) :
      (eqToHom p ≫ ↾(Sum.map (M₁ ·) (M₂ ·)) ≫ eqToHom s) ≫ eqToHom t =
        eqToHom p' ≫ ↾(Sum.map ((M₁ ≫ eqToHom f₁) ·) ((M₂ ≫ eqToHom f₂) ·)) ≫ eqToHom q' := by
    subst f₁ f₂ s t
    simp

  unseal classify U U_sum U_sum' in
  @[simp]
  lemma U_sum_push {τ1 τ2 : 𝟙_ ℐ.{i + 1} ⟶ U.{i}}
    : classify.hom (CartesianMonoidalCategory.lift τ1 τ2 ≫ MonoidalClosed.uncurry' U_sum) = ℐ.psum (classify.hom τ1) (classify.hom τ2) := by
    refine CategoryTheory.Functor.ext (fun j => rfl) ?_
    intro a b φ
    simp only [ℐ.psum, classify_hom_map]
    rw [Functor.congr_hom (U_sum_el (τ1 := τ1) (τ2 := τ2) a)]
    simp only [FunctorToTypes.coprod_map]
    exact sum_eqToHom_ext _ _ _ _ _ _ _ _ _

end constructors

end
