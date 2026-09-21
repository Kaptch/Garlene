module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import SynthDom.Semantics.Base

@[expose] public section

section univ
  open CategoryTheory
  open Opposite
  open Functor
  open MonoidalCategory

  @[irreducible]
  def U.{i} : ℐ.{i + 1} where
    obj i := (Over i.unop)ᵒᵖ ⥤ (Type i)
    map {X Y} f := ↾(fun A => (Functor.op (Over.map f.unop)) ⋙ A)

  def unitPt.{u} (X : ℕᵒᵖ) : (𝟙_ ℐ.{u}).obj X := PUnit.unit

  @[simp] lemma unitPt_map.{u} {X Y : ℕᵒᵖ} (g : X ⟶ Y) :
      ConcreteCategory.hom ((𝟙_ ℐ.{u}).map g) (unitPt X) = unitPt Y := rfl

  unseal U in
  def U.el.{u} {X : ℕᵒᵖ} (A : U.{u}.obj X) : (Over (unop X))ᵒᵖ ⥤ Type u := A

  unseal U in
  @[simp] lemma U.el_map.{u} {X Y : ℕᵒᵖ} (g : X ⟶ Y) (A : U.{u}.obj X) :
      U.el (ConcreteCategory.hom (U.map g) A) = (Over.map g.unop).op ⋙ U.el A := rfl

  unseal U in
  def U.mk.{u} {X : ℕᵒᵖ} (A : (Over (unop X))ᵒᵖ ⥤ Type u) : U.{u}.obj X := A

  @[simp] lemma U.el_mk.{u} {X : ℕᵒᵖ} (A : (Over (unop X))ᵒᵖ ⥤ Type u) :
      U.el (U.mk A) = A := rfl

  attribute [implicit_reducible] U.el U.mk

  @[simp] lemma U.mk_el.{u} {X : ℕᵒᵖ} (A : U.{u}.obj X) : U.mk (U.el A) = A := rfl

  unseal U in
  @[simp] lemma U.map_mk.{u} {X Y : ℕᵒᵖ} (g : X ⟶ Y) (A : (Over (unop X))ᵒᵖ ⥤ Type u) :
      ConcreteCategory.hom (U.map g) (U.mk A) = U.mk ((Over.map g.unop).op ⋙ A) := rfl

  private lemma thin_comp_eqToHom {C D : Type*} [Category C] [Category D] [Quiver.IsThin C]
      (F : C ⥤ D) {A B B' E E' : C} (φ : A ⟶ B) (ψ : B' ⟶ E') (χ : A ⟶ E)
      {T : D} (q : F.obj E = T) (q' : F.obj E' = T)
      (pB : F.obj B = F.obj B') (pE : E = E') (pB' : B = B') :
      F.map χ ≫ eqToHom q = F.map φ ≫ eqToHom pB ≫ F.map ψ ≫ eqToHom q' := by
    subst pE pB'
    simp only [eqToHom_refl, Category.id_comp]
    rw [Subsingleton.elim χ (φ ≫ ψ), Functor.map_comp, Category.assoc]

  private lemma thin_hom_eqToHom {C D : Type*} [Category C] [Category D] [Quiver.IsThin C]
      (F : C ⥤ D) {A A' E E' : C} (χ : A ⟶ E) (φ : A' ⟶ E') (pA : A = A') (pE : E = E')
      {S T : D} (l : S = F.obj A) (q : F.obj E = T) (l' : S = F.obj A') (q' : F.obj E' = T) :
      eqToHom l ≫ F.map χ ≫ eqToHom q = eqToHom l' ≫ F.map φ ≫ eqToHom q' := by
    subst pA pE l q
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rw [Subsingleton.elim χ φ]

  private lemma thin_hom_eqToHom' {C D : Type*} [Category C] [Category D] [Quiver.IsThin C]
      (F : C ⥤ D) {A A' E E' : C} (χ : A ⟶ E) (φ : A' ⟶ E') (pA : A = A') (pE : E = E')
      {T : D} (q : F.obj E = T) (l' : F.obj A = F.obj A') (q' : F.obj E' = T) :
      F.map χ ≫ eqToHom q = eqToHom l' ≫ F.map φ ≫ eqToHom q' := by
    subst pA pE q
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rw [Subsingleton.elim χ φ]

  private lemma thin_hom_eqToHom'' {C D : Type*} [Category C] [Category D] [Quiver.IsThin C]
      (F : C ⥤ D) {A A' E E' : C} (χ : A ⟶ E) (φ : A' ⟶ E') (pA : A = A') (pE : E = E')
      {T M M' : D} (q : F.obj E = T) (l₁ : F.obj A = M) (l₂ : M = F.obj A')
      (r₁ : F.obj E' = M') (r₂ : M' = T) :
      F.map χ ≫ eqToHom q = eqToHom l₁ ≫ (eqToHom l₂ ≫ F.map φ ≫ eqToHom r₁) ≫ eqToHom r₂ := by
    subst pA pE
    subst l₂ r₁ q
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rw [Subsingleton.elim χ φ]

  lemma classify_nat {f : 𝟙_ ℐ.{i + 1} ⟶ U.{i}} {X Y : ℕᵒᵖ} (g : X ⟶ Y) :
      U.el (ConcreteCategory.hom (f.app Y) (unitPt Y)) =
        (Over.map g.unop).op ⋙ U.el (ConcreteCategory.hom (f.app X) (unitPt X)) := by
    have HN := ConcreteCategory.congr_hom (f.naturality g) (unitPt X)
    simp only [CategoryTheory.comp_apply, unitPt_map] at HN
    exact (congrArg U.el HN).trans (U.el_map g _)

  @[irreducible]
  def classify : (𝟙_ ℐ.{i + 1} ⟶ U.{i}) ≅ ℐ.{i} where
    hom := ↾(fun f =>
      {
        obj i := (U.el (f.app i (unitPt i))).obj (op (Over.mk (𝟙 _)))
        map {X Y} g := ((U.el (f.app X (unitPt X))).map (op (Over.homMk g.unop)))
          ≫ eqToHom (Functor.congr_obj (classify_nat g) (op (Over.mk (𝟙 (unop Y))))).symm
        map_id {X} := by
          exact Eq.trans (congrArg (fun φ => (U.el (ConcreteCategory.hom (f.app X) (unitPt X))).map φ ≫
              eqToHom (Functor.congr_obj (classify_nat (𝟙 X)) (op (Over.mk (𝟙 (unop X))))).symm)
              (show op (Over.homMk (𝟙 X).unop _) = 𝟙 (op (Over.mk (𝟙 (unop X)))) from
                Quiver.Hom.unop_inj (by ext; rfl)))
            (Eq.trans (congrArg (· ≫ _) (CategoryTheory.Functor.map_id _ _)) (Category.id_comp _))
        map_comp {X Y Z} g h := by
          rw [Functor.congr_hom (classify_nat (f := f) g)]
          simp only [Functor.comp_map, Functor.op_map, Category.assoc, eqToHom_trans,
            eqToHom_trans_assoc]
          have : Quiver.IsThin (Over (unop X))ᵒᵖ :=
            fun _ _ => ⟨fun a b => Quiver.Hom.unop_inj (Over.OverMorphism.ext (Subsingleton.elim _ _))⟩
          exact thin_comp_eqToHom _ _ _ _ _ _ _ rfl rfl
      })
    inv := ↾(fun G =>
      {
        app i := ↾(fun _ => U.mk
          {
            obj j := G.obj (op j.unop.left)
            map {X Y} f := G.map f.unop.left.op
          })
        naturality {X Y} f := by
          refine ConcreteCategory.hom_ext _ _ fun x => ?_
          show U.mk _ = ConcreteCategory.hom (U.map f) (U.mk _)
          rw [U.map_mk]
          refine congrArg U.mk (CategoryTheory.Functor.ext (fun j => rfl) ?_)
          intro A B φ
          rfl
      })
    hom_inv_id := by
      refine ConcreteCategory.hom_ext _ _ fun f => ?_
      refine NatTrans.ext (funext fun i => ?_)
      refine ConcreteCategory.hom_ext _ _ fun x => ?_
      simp only [CategoryTheory.comp_apply, CategoryTheory.id_apply, ConcreteCategory.hom_ofHom]
      show U.mk _ = ConcreteCategory.hom (f.app i) x
      refine Eq.trans (congrArg U.mk (CategoryTheory.Functor.ext
        (fun j => Functor.congr_obj (classify_nat ((j.unop.hom).op)) (op (Over.mk (𝟙 _)))) ?_)) (U.mk_el _)
      intro A B φ
      simp only [TypeCat.Fun.mk_apply]
      simp only [Functor.congr_hom (classify_nat (f := f) ((A.unop.hom).op)),
        Functor.comp_map, Functor.op_map, Category.assoc, eqToHom_trans]
      have : Quiver.IsThin (Over (unop i))ᵒᵖ :=
        fun _ _ => ⟨fun a b => Quiver.Hom.unop_inj (Over.OverMorphism.ext (Subsingleton.elim _ _))⟩
      exact thin_hom_eqToHom (C := (Over (unop i))ᵒᵖ) _ _ _ rfl rfl _ _ _ _
    inv_hom_id := by
      refine ConcreteCategory.hom_ext _ _ fun G => ?_
      simp only [CategoryTheory.comp_apply, CategoryTheory.id_apply, ConcreteCategory.hom_ofHom]
      exact CategoryTheory.Functor.ext (fun j => rfl) (fun A B φ => rfl)

  unseal classify U in
  lemma classify_hom_map {f : 𝟙_ ℐ.{i + 1} ⟶ U.{i}} {X Y : ℕᵒᵖ} (g : X ⟶ Y) :
      (ConcreteCategory.hom classify.hom f).map g =
        (U.el (ConcreteCategory.hom (f.app X) (unitPt X))).map (op (Over.homMk g.unop)) ≫
          eqToHom (Functor.congr_obj (classify_nat g) (op (Over.mk (𝟙 (unop Y))))).symm := rfl

end univ

end
