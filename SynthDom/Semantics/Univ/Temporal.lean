module

public import SynthDom.Semantics.Univ.Exponential

@[expose] public section

section constructors
  open CategoryTheory Functor MonoidalCategory CartesianMonoidalCategory

  def U_shift {n : ℕ} (F : (Over n)ᵒᵖ ⥤ Type i) : (Over (n + 1))ᵒᵖ ⥤ Type i where
    obj i := match i with
      | Opposite.op (Comma.mk .zero r h) => PUnit
      | Opposite.op (Comma.mk (.succ l) r h) => F.obj (.op (Comma.mk l r (homOfLE (Nat.le_of_succ_le_succ h.le))))
    map {X Y} f := match X with
      | Opposite.op (Comma.mk .zero r h) =>
        match Y with
        | Opposite.op (Comma.mk .zero r' h') => 𝟙 _
        | Opposite.op (Comma.mk (.succ l') r' h') => False.elim $ Nat.not_succ_le_zero _ f.unop.left.le
      | Opposite.op (Comma.mk (.succ l) r h) =>
        match Y with
        | Opposite.op (Comma.mk .zero r' h') => ↾(fun _ => PUnit.unit)
        | Opposite.op (Comma.mk (.succ l') r' h') =>
          F.map (Opposite.op (CommaMorphism.mk (homOfLE (Nat.le_of_succ_le_succ f.unop.left.le)) f.unop.right (by exact Subsingleton.elim _ _)))
    map_id {X} :=
      match X with
      | Opposite.op (Comma.mk .zero r h) => by simp
      | Opposite.op (Comma.mk (.succ n) r h) => by
        simp
        rw [←F.map_id]
        exact congrArg F.map (Quiver.Hom.unop_inj
          (Over.OverMorphism.ext (Subsingleton.elim _ _)))
    map_comp {X Y Z} f g := match X with
      | Opposite.op (Comma.mk .zero r h) =>
        match Y with
        | Opposite.op (Comma.mk .zero r' h') =>
          match Z with
          | Opposite.op (Comma.mk .zero r'' h'') => by simp
          | Opposite.op (Comma.mk (.succ l'') r'' h'') => by simp
        | Opposite.op (Comma.mk (.succ l') r' h') =>
          match Z with
          | Opposite.op (Comma.mk .zero r'' h'') => by
            simp
            exfalso
            apply Nat.not_succ_le_zero l' f.unop.left.le
          | Opposite.op (Comma.mk (.succ l'') r'' h'') => by
            simp
            exfalso
            apply Nat.not_succ_le_zero l' f.unop.left.le
      | Opposite.op (Comma.mk (.succ l) r h) =>
        match Y with
        | Opposite.op (Comma.mk .zero r' h') =>
          match Z with
          | Opposite.op (Comma.mk .zero r'' h'') => by simp
          | Opposite.op (Comma.mk (.succ l'') r'' h'') => by
            simp
            exfalso
            apply Nat.not_succ_le_zero l'' g.unop.left.le
        | Opposite.op (Comma.mk (.succ l') r' h') =>
          match Z with
          | Opposite.op (Comma.mk .zero r'' h'') => by
            ext x
          | Opposite.op (Comma.mk (.succ l'') r'' h'') => by
            simp
            rw [←F.map_comp]
            exact congrArg F.map (Quiver.Hom.unop_inj
              (Over.OverMorphism.ext (Subsingleton.elim _ _)))

  unseal U in
  @[irreducible]
  def U_later' : later.obj U.{i} ⟶ U.{i} where
    app i := ↾(fun x => match i with
      | Opposite.op .zero => (const (Over 0)ᵒᵖ).obj PUnit
      | Opposite.op (.succ n) => U_shift x)
    naturality {X Y} f := by
      refine ConcreteCategory.hom_ext _ _ fun x => ?_
      cases X with | op X' =>
      cases Y with | op Y' =>
      cases X' with
      | zero =>
        cases Y' with
        | zero => rfl
        | succ Y'' => exact absurd (leOfHom f.unop) (Nat.not_succ_le_zero _)
      | succ X'' =>
        cases Y' with
        | zero =>
          show (const (Over 0)ᵒᵖ).obj PUnit = ConcreteCategory.hom (U.map f) (U_shift x)
          rw [← U.mk_el (U_shift x), U.map_mk]
          show U.mk _ = _
          refine congrArg U.mk (CategoryTheory.Functor.ext (fun j => ?_) ?_)
          · cases j with | op jj =>
            cases jj with | mk l r w =>
            cases l with
            | zero => rfl
            | succ l' => exact absurd (leOfHom w) (Nat.not_succ_le_zero _)
          · intro A B ψ
            refine ConcreteCategory.hom_ext _ _ fun u => ?_
            rfl
        | succ Y'' =>
          show U.mk (U_shift (ConcreteCategory.hom ((later.obj U).map f) x)) =
            ConcreteCategory.hom (U.map f) (U_shift x)
          rw [← U.mk_el (U_shift x), U.map_mk]
          refine congrArg U.mk (CategoryTheory.Functor.ext (fun j => ?_) ?_)
          · cases j with | op jj =>
            cases jj with | mk l r w =>
            cases l with
            | zero => rfl
            | succ l' => rfl
          · intro A B ψ
            cases A with | op aa =>
            cases aa with | mk la ra wa =>
            cases B with | op bb =>
            cases bb with | mk lb rb wb =>
            cases la with
            | zero =>
              cases lb with
              | zero => rfl
              | succ lb' => exact absurd (leOfHom ψ.unop.left) (Nat.not_succ_le_zero _)
            | succ la' =>
              cases lb with
              | zero => rfl
              | succ lb' => rfl

  @[irreducible]
  def U_later : 𝟙_ _ ⟶ (ihom (later.obj U.{i})).obj U.{i} := MonoidalClosed.curry' U_later'

  def U_larr' : later.obj U.{i} ⊗ later.obj U.{i} ⟶ U.{i} :=
    LaxMonoidal.μ later U.{i} U.{i} ≫ later.map U_arr' ≫ U_later'
  @[irreducible]
  def U_larr : 𝟙_ _ ⟶ (ihom (later.obj U.{i} ⊗ later.obj U.{i})).obj U.{i} :=
    MonoidalClosed.curry' U_larr'

  unseal U U_later' in
  private lemma U_later'_el {τ : 𝟙_ ℐ.{i + 1} ⟶ U.{i}} (n : ℕ) :
      U.el (ConcreteCategory.hom ((τ ≫ next.app U ≫ U_later').app (Opposite.op (n + 1)))
          (unitPt (Opposite.op (n + 1)))) =
        U_shift (U.el (ConcreteCategory.hom (τ.app (Opposite.op n)) (unitPt (Opposite.op n)))) := by
    rw [show (ConcreteCategory.hom ((τ ≫ next.app U ≫ U_later').app (Opposite.op (n + 1))))
          (unitPt (Opposite.op (n + 1)))
        = ConcreteCategory.hom (U_later'.app (Opposite.op (n + 1)))
          (ConcreteCategory.hom (U.map (Opposite.op (homOfLE (Nat.le_succ n))))
            (ConcreteCategory.hom (τ.app (Opposite.op (n + 1))) (unitPt (Opposite.op (n + 1))))) from rfl]
    show U_shift (U.el (ConcreteCategory.hom (U.map (Opposite.op (homOfLE (Nat.le_succ n))))
        (ConcreteCategory.hom (τ.app (Opposite.op (n + 1))) (unitPt (Opposite.op (n + 1)))))) = _
    rw [U.el_map]
    exact congrArg U_shift (classify_nat (f := τ) ((homOfLE (Nat.le_succ n)).op)).symm

  private lemma U_shift_map_succ {n : ℕ} (F : (Over n)ᵒᵖ ⥤ Type i) {b : ℕ} (φ : (b + 1) ⟶ (n + 1)) :
      (U_shift F).map
          (Opposite.op (Over.homMk φ) : Opposite.op (Over.mk (𝟙 (n + 1))) ⟶ Opposite.op (Over.mk φ)) =
        F.map (Opposite.op (Over.homMk (homOfLE (Nat.le_of_succ_le_succ (leOfHom φ))))) := by
    rfl

  private lemma thin_hom_eqToHom4 {C D : Type*} [Category C] [Category D] [Quiver.IsThin C]
      (F : C ⥤ D) {A A' E E' : C} (χ : A ⟶ E) (φ : A' ⟶ E') (pA : A = A') (pE : E = E')
      {W X Y Z : D} (l1 : W = F.obj A) (l2 : F.obj E = X) (l3 : X = Y)
      (r1 : W = F.obj A') (r2 : F.obj E' = Z) (r3 : Z = Y) :
      (eqToHom l1 ≫ F.map χ ≫ eqToHom l2) ≫ eqToHom l3 =
        eqToHom r1 ≫ (F.map φ ≫ eqToHom r2) ≫ eqToHom r3 := by
    subst pA pE
    subst l3 r2 l2
    simp only [eqToHom_refl, Category.comp_id]
    rw [Subsingleton.elim χ φ]

  unseal U classify U_later U_later' in
  @[simp]
  lemma U_later_push {τ : 𝟙_ ℐ.{i + 1} ⟶ U.{i}}
    : classify.hom (τ ≫ next.app U ≫ MonoidalClosed.uncurry' U_later) = later.obj (classify.hom τ) := by
    rw [show (τ ≫ next.app U ≫ MonoidalClosed.uncurry' U_later) = (τ ≫ next.app U ≫ U_later')
      from by rw [U_later, MonoidalClosed.uncurry'_curry']]
    refine CategoryTheory.Functor.ext (fun j => ?_) ?_
    · cases j with | op jj =>
      cases jj with
      | zero => rfl
      | succ n =>
        exact (Functor.congr_obj (classify_nat (f := τ) ((homOfLE (Nat.le_succ n)).op))
          (Opposite.op (Over.mk (𝟙 n)))).symm
    · intro X Y f
      cases X with | op X' =>
      cases Y with | op Y' =>
      cases X' with
      | zero =>
        cases Y' with
        | zero =>
          refine ConcreteCategory.hom_ext _ _ fun u => ?_
          rfl
        | succ Y'' => exact absurd (leOfHom f.unop) (Nat.not_succ_le_zero _)
      | succ X'' =>
        cases Y' with
        | zero =>
          refine ConcreteCategory.hom_ext _ _ fun u => ?_
          rfl
        | succ Y'' =>
          refine (classify_hom_map (f := τ ≫ next.app U ≫ U_later') f).trans
            ((congrArg (· ≫ eqToHom (Functor.congr_obj
              (classify_nat (f := τ ≫ next.app U ≫ U_later') f)
              (Opposite.op (Over.mk (𝟙 (Y'' + 1))))).symm)
              (Functor.congr_hom (U_later'_el (τ := τ) X'')
                (Opposite.op (Over.homMk f.unop) :
                  Opposite.op (Over.mk (𝟙 (X'' + 1))) ⟶ Opposite.op (Over.mk f.unop)))).trans ?_)
          rw [U_shift_map_succ (F := U.el (ConcreteCategory.hom (τ.app (Opposite.op X''))
                (unitPt (Opposite.op X'')))) (φ := f.unop),
            show (later.obj (ConcreteCategory.hom classify.hom τ)).map f
                = (ConcreteCategory.hom classify.hom τ).map
                    (Opposite.op (homOfLE (Nat.le_of_succ_le_succ (leOfHom f.unop)))) from rfl,
            classify_hom_map (f := τ)
              (Opposite.op (homOfLE (Nat.le_of_succ_le_succ (leOfHom f.unop))))]
          rw [show (Quiver.Hom.unop (Opposite.op (homOfLE (Nat.le_of_succ_le_succ (leOfHom f.unop)))))
              = homOfLE (Nat.le_of_succ_le_succ (leOfHom f.unop)) from rfl]
          have : Quiver.IsThin (Over X'')ᵒᵖ :=
            fun _ _ => ⟨fun a b => Quiver.Hom.unop_inj (Over.OverMorphism.ext (Subsingleton.elim _ _))⟩
          exact thin_hom_eqToHom4 (C := (Over X'')ᵒᵖ)
            (U.el (ConcreteCategory.hom (τ.app (Opposite.op X'')) (unitPt (Opposite.op X''))))
            _ _ rfl rfl _ _ _ _ _ _

  unseal U classify U_arr U_arr' U_later U_later' U_larr in
  @[simp]
  lemma U_larr_push {τ1 τ2 : 𝟙_ ℐ.{i + 1} ⟶ U.{i}}
    : classify.hom (CartesianMonoidalCategory.lift (τ1 ≫ next.app U) (τ2 ≫ next.app U)
        ≫ MonoidalClosed.uncurry' U_larr)
      = later.obj (ℐ.parr (ConcreteCategory.hom classify.hom τ1)
          (ConcreteCategory.hom classify.hom τ2)) := by
    have hm : CartesianMonoidalCategory.lift (τ1 ≫ next.app U) (τ2 ≫ next.app U)
          ≫ MonoidalClosed.uncurry' U_larr
        = (CartesianMonoidalCategory.lift τ1 τ2 ≫ MonoidalClosed.uncurry' U_arr)
            ≫ next.app U ≫ MonoidalClosed.uncurry' U_later := by
      rw [U_larr, U_arr, U_later]
      simp only [MonoidalClosed.uncurry'_curry']
      rw [U_larr']
      have hnat := next.naturality U_arr'
      simp only [Functor.id_map] at hnat
      calc CartesianMonoidalCategory.lift (τ1 ≫ next.app U) (τ2 ≫ next.app U)
            ≫ LaxMonoidal.μ later U U ≫ later.map U_arr' ≫ U_later'
          = CartesianMonoidalCategory.lift τ1 τ2
              ≫ ((next.app U ⊗ₘ next.app U) ≫ LaxMonoidal.μ later U U)
              ≫ later.map U_arr' ≫ U_later' := by
            rw [← CartesianMonoidalCategory.lift_map]
            simp only [Category.assoc]
        _ = CartesianMonoidalCategory.lift τ1 τ2
              ≫ next.app (U ⊗ U) ≫ later.map U_arr' ≫ U_later' :=
            congrArg (fun t => CartesianMonoidalCategory.lift τ1 τ2
              ≫ t ≫ later.map U_arr' ≫ U_later') (next_μ U U)
        _ = CartesianMonoidalCategory.lift τ1 τ2
              ≫ (U_arr' ≫ next.app U) ≫ U_later' :=
            congrArg (CartesianMonoidalCategory.lift τ1 τ2 ≫ ·)
              ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ U_later') hnat.symm))
        _ = (CartesianMonoidalCategory.lift τ1 τ2 ≫ U_arr') ≫ next.app U ≫ U_later' := by
            simp only [Category.assoc]
    rw [hm, U_later_push, U_arr_push]

end constructors

end
