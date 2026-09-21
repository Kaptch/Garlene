module

public import SynthDom.Semantics.Base

@[expose] public section

section Fixpoint
  open CategoryTheory
  open Opposite
  open Functor
  open MonoidalCategory

  @[simp]
  def mu_app_nat (X : ℐ.{u}) : (n : ℕ) → ((ihom (later.obj X)).obj X).obj (op n) ⟶ X.obj (op n)
    | Nat.zero => ↾fun t ↦ t.1 0 (Nat.le_refl _) PUnit.unit
    | Nat.succ x => ↾fun t ↦ t.1 x.succ (Nat.le_refl _)
         (mu_app_nat X x (ConcreteCategory.hom (((ihom (later.obj X)).obj X).map
           (op (homOfLE (Nat.le_succ _)))) t))

  @[simp]
  def mu_app (X : ℐ.{u}) (x : ℕᵒᵖ) : ((ihom (later.obj X)).obj X).obj x ⟶ X.obj x :=
    mu_app_nat X x.unop

  def mu (X : ℐ.{u}) : ((ihom (later.obj X)).obj X) ⟶ X :=
  {
    app := mu_app X
    naturality x := by
      cases x with
      | op x => induction x with
        | zero => intro y f; cases y with
          | op y => cases y with
            | zero =>
              rw [show f = CategoryStruct.id _ from rfl]
              simp
            | succ y' =>
              exact absurd (leOfHom f.unop) (Nat.not_succ_le_zero _)
        | succ x' IH1 => intro y f; cases y with
          | op y => cases y with
            | zero =>
              refine ConcreteCategory.hom_ext _ _ fun t => ?_
              simp only [mu_app, CategoryTheory.comp_apply]
              exact (t.2 0 (x' + 1) (Nat.zero_le _) (Nat.le_refl _)
                (ConcreteCategory.hom (mu_app X (op x'))
                  (ConcreteCategory.hom (((ihom (later.obj X)).obj X).map
                    (op (homOfLE (Nat.le_succ _)))) t)))
            | succ y' =>
              refine ConcreteCategory.hom_ext _ _ fun t => ?_
              simp only [mu_app, CategoryTheory.comp_apply]
              have IH := ConcreteCategory.congr_hom
                (IH1 (op (homOfLE (Nat.le_of_succ_le_succ (leOfHom f.unop)))))
                (ConcreteCategory.hom (((ihom (later.obj X)).obj X).map
                  (op (homOfLE (Nat.le_succ _)))) t)
              simp only [CategoryTheory.comp_apply] at IH
              exact (congrArg (t.1 (y' + 1) (leOfHom f.unop)) IH).trans
                (t.2 (y' + 1) (x' + 1) (leOfHom f.unop) (Nat.le_refl _)
                  (ConcreteCategory.hom (mu_app X (op x'))
                    (ConcreteCategory.hom (((ihom (later.obj X)).obj X).map
                      (op (homOfLE (Nat.le_succ _)))) t)))
  }

  def fixpoint {X Y : ℐ.{u}} (η : (later.obj X ⊗ Y) ⟶ X) : Y ⟶ X :=
    (MonoidalClosed.curry η) ≫ mu X

  lemma fixpoint_zero {X Y : ℐ.{u}} (η : (later.obj X ⊗ Y) ⟶ X)
    (y : Y.obj (op Nat.zero)) : (fixpoint η).app (op Nat.zero) y = η.app (op Nat.zero) (PUnit.unit, y) := by
    simp [fixpoint, mu]
    simp [MonoidalClosed.curry]
    simp [Adjunction.homEquiv]
    simp [ihom, Closed.rightAdj]
    apply congrArg (η.app (op Nat.zero))
    unfold ihom.coev
    simp [ihom.adjunction, Closed.adj]
    conv_rhs => rw [show y = (𝟙 (Y.obj (op Nat.zero))) y from rfl, ← Y.map_id]
    rfl

  lemma fixpoint_succ {X Y : ℐ.{u}} (η : (later.obj X ⊗ Y) ⟶ X) (α : ℕ) (y : Y.obj (op (Nat.succ α))) :
    (fixpoint η).app (op (Nat.succ α)) y =
      η.app (op (Nat.succ α))
        ((fixpoint η).app (op α) (Y.map (op (homOfLE (Nat.le_succ _))) y), y) := by
    conv =>
      lhs
      simp [fixpoint, mu]
    rw [show (mu_app_nat X α (((ihom (later.obj X)).obj X).map (op (homOfLE (Nat.le_succ _))) ((MonoidalClosed.curry η).app (op (α + 1)) y))) =
        (fixpoint η).app (op α) (Y.map (op (homOfLE (Nat.le_succ _))) y) by
      rw [fixpoint, CategoryTheory.NatTrans.vcomp_app', mu]
      simp]
    simp [MonoidalClosed.curry]
    simp [Adjunction.homEquiv]
    simp [ihom, Closed.rightAdj]
    apply congrArg (η.app (op (α + 1)))
    unfold ihom.coev
    simp [ihom.adjunction, Closed.adj]
    refine Prod.ext ?_ ?_
    · rfl
    · exact types_congr_hom (Y.map_id (op (α + 1))) y

  theorem fixpoint_unfold {X Y : ℐ.{u}} (η : (later.obj X ⊗ Y) ⟶ X) :
    fixpoint η = (CartesianMonoidalCategory.lift (fixpoint η ≫ next_app X) (𝟙 Y)) ≫ η :=
    by
      apply CategoryTheory.NatTrans.ext
      ext x y
      obtain ⟨_ | x⟩ := x
      · simp only [TypeCat.Fun.toFun_apply, fixpoint_zero]
        simp [next_app, CartesianMonoidalCategory.lift]
        congr
      · simp only [TypeCat.Fun.toFun_apply, fixpoint_succ]
        simp [CartesianMonoidalCategory.lift]
        apply congrArg (η.app (op (x + 1)))
        simp
        rfl

  lemma earlier_later_adj_succ {P Q : ℐ.{u}} (f : earlier.obj P ⟶ Q)
    : ((earlier_later_adj.homEquiv P Q) f).app (op (n + 1)) = f.app (op n) := by
    rfl

  open CartesianMonoidalCategory in
  lemma fixpoint_naturality {P Q : ℐ.{u}} (g : later.obj Q ⊗ P ⟶ Q)
    : fixpoint g ≫ next_app Q =
      (earlier_later_adj.homEquiv P Q).toFun
        ((λ_ (earlier.obj P)).inv
        ≫ fixpoint (later.obj Q ◁ (snd (𝟙_ ℐ) (earlier.obj P) ≫ force.app P)
        ≫ g)) := by
    simp [-next_app]
    rw [Adjunction.homEquiv_naturality_right]
    simp [-next_app, fixpoint]
    rw [MonoidalClosed.curry_natural_left, MonoidalClosed.curry_natural_left]
    simp [-next_app]
    rw [←later.map_comp, ←later.map_comp, ←later.map_comp, ←later.map_comp, ←later.map_comp]
    rw [←Category.assoc (OplaxMonoidal.η earlier ▷ earlier.obj P)]
    simp [-next_app]
    rw [←later.map_comp, ←later.map_comp, ←later.map_comp]
    rw [←Adjunction.homEquiv_naturality_right]
    simp only [Adjunction.homEquiv_naturality_right, Functor.map_comp]
    rw [←Category.assoc, ← later.map_comp, ← later.map_comp, ← later.map_comp, ← fixpoint,
      ← earlier_later_adj.homEquiv_naturality_right, ← Category.assoc]
    simp only [Category.assoc]
    have hforce := force.naturality_assoc (snd (𝟙_ ℐ) P) (fixpoint g)
    simp only [Functor.id_map] at hforce
    rw [← hforce]
    rw [← earlier.map_comp_assoc,
      show (λ_ P).inv ≫ snd (𝟙_ ℐ) P = 𝟙 P by simp,
      CategoryTheory.Functor.map_id, Category.id_comp]
    rw [earlier_later_adj.homEquiv_naturality_right]
    simp only [Functor.id_obj]
    rw [show (earlier_later_adj.homEquiv P P) (force.app P) = next.app P by
      apply CategoryTheory.NatTrans.ext
      ext x y
      obtain ⟨_ | x⟩ := x
      · rfl
      · rw [earlier_later_adj_succ]
        simp [force, force_app, next]]
    exact next.naturality (fixpoint g)

  class Contractive {X Y : ℐ.{u}} (f : X ⟶ Y) where
    witness : later.obj X ⟶ Y
    contractive : f = next.app _ ≫ witness

end Fixpoint
end
