module

public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Equivalence

public import Mathlib.CategoryTheory.Category.Preorder

public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.OfHasFiniteProducts
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
public import Mathlib.CategoryTheory.Monoidal.Closed.Types
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

public import Mathlib.CategoryTheory.Enriched.Basic
public import Mathlib.CategoryTheory.Enriched.FunctorCategory

public import Mathlib.SetTheory.Ordinal.Basic
public import Mathlib.SetTheory.Ordinal.Topology

public import Mathlib.CategoryTheory.Sites.Sheaf

public import Mathlib.CategoryTheory.Yoneda

public import Mathlib.CategoryTheory.Adjunction.Unique

public import Mathlib.Tactic

@[expose] public section

open CategoryTheory in
abbrev ℐ.{u} : Type (u + 1) := ℕᵒᵖ ⥤ (Type u)

section Base
  open CategoryTheory
  open scoped TypeCat
  open Opposite
  open Functor
  open Limits
  open MonoidalCategory

  def discrete.{u} : Type u ⥤ ℐ.{u} := const (C := Type u) ℕᵒᵖ

  def ℐ.psum.{u} (X Y : ℐ.{u}) : ℐ.{u} where
    obj n := X.obj n ⊕ Y.obj n
    map f := ↾(Sum.map (X.map f ·) (Y.map f ·))
    map_id n := by ext a; cases a <;> simp
    map_comp f g := by ext a; cases a <;> simp

  def ℐ.parrObj.{u} (X Y : ℐ.{u}) (j : ℕ) : Type u :=
    { app : ∀ (k : ℕ), k ≤ j → (X.obj (Opposite.op k) → Y.obj (Opposite.op k)) //
      ∀ (k' k : ℕ) (g : k' ≤ k) (h : k ≤ j) (x : X.obj (Opposite.op k)),
        app k' (g.trans h) (X.map (homOfLE g).op x) = Y.map (homOfLE g).op (app k h x) }

  def ℐ.parr.{u} (X Y : ℐ.{u}) : ℐ.{u} where
    obj j := ℐ.parrObj X Y (unop j)
    map {j j'} f := ↾(fun φ => ⟨fun k h => φ.1 k (h.trans (leOfHom f.unop)),
      fun k' k g h x => φ.2 k' k g (h.trans (leOfHom f.unop)) x⟩)
    map_id n := by ext φ; rfl
    map_comp f g := by ext φ; rfl

  def ℐ.parrFunctor.{u} (X : ℐ.{u}) : ℐ.{u} ⥤ ℐ.{u} where
    obj Y := ℐ.parr X Y
    map {Y Y'} g :=
      { app := fun j => ↾(fun φ => ⟨fun k h x => ConcreteCategory.hom (g.app (Opposite.op k)) (φ.1 k h x),
          fun k' k gg h x => by
            dsimp only
            rw [φ.2 k' k gg h x]
            have := ConcreteCategory.congr_hom (g.naturality (homOfLE gg).op) (φ.1 k h x)
            simp only [CategoryTheory.comp_apply] at this
            exact this⟩)
        naturality := fun j j' f => rfl }
    map_id Y := rfl
    map_comp f g := rfl

  def ℐ.parrIso.{u} (X : ℐ.{u}) : FunctorToTypes.rightAdj X ≅ ℐ.parrFunctor X :=
    NatIso.ofComponents (fun Y => NatIso.ofComponents (fun j =>
      { hom := ↾(fun y => ⟨fun k h x => y.app (Opposite.op k) ((homOfLE h).op) x,
          fun k' k g h x => by
            have := ConcreteCategory.congr_hom
              (y.naturality (f := (homOfLE g).op) ((homOfLE h).op)) x
            simp only [CategoryTheory.comp_apply] at this
            exact this⟩)
        inv := ↾(fun φ =>
          { app := fun c f => ↾(φ.1 (unop c) (leOfHom f.unop))
            naturality := fun {c d} f a => by
              refine ConcreteCategory.hom_ext _ _ fun x => ?_
              have := φ.2 (unop d) (unop c) (leOfHom f.unop) (leOfHom a.unop) x
              simp only [CategoryTheory.comp_apply]
              exact this })
        hom_inv_id := rfl
        inv_hom_id := rfl })
      (fun {j j'} f => rfl))
      (fun {Y Y'} g => rfl)

  def ℐ.parrTranspose.{u} {X G H : ℐ.{u}} (φ : X ⊗ G ⟶ H) : G ⟶ ℐ.parr X H where
    app j := ↾(fun a => ⟨fun k h x =>
      ConcreteCategory.hom (φ.app (Opposite.op k))
        ((x, ConcreteCategory.hom (G.map (homOfLE h).op) a) : (X ⊗ G).obj (Opposite.op k)),
      fun k' k g h x => by
        have hmap : ConcreteCategory.hom ((X ⊗ G).map (homOfLE g).op)
            ((x, ConcreteCategory.hom (G.map (homOfLE h).op) a) : (X ⊗ G).obj (Opposite.op k))
          = ((ConcreteCategory.hom (X.map (homOfLE g).op) x,
              ConcreteCategory.hom (G.map (homOfLE g).op)
                (ConcreteCategory.hom (G.map (homOfLE h).op) a)) :
              (X ⊗ G).obj (Opposite.op k')) := rfl
        have hcomp : ConcreteCategory.hom (G.map (homOfLE (g.trans h)).op) a
            = ConcreteCategory.hom (G.map (homOfLE g).op)
                (ConcreteCategory.hom (G.map (homOfLE h).op) a) := by
          have := ConcreteCategory.congr_hom (G.map_comp ((homOfLE h).op) ((homOfLE g).op)) a
          simp only [CategoryTheory.comp_apply] at this
          exact this
        have hphi := ConcreteCategory.congr_hom (φ.naturality (homOfLE g).op)
          ((x, ConcreteCategory.hom (G.map (homOfLE h).op) a) : (X ⊗ G).obj (Opposite.op k))
        change ConcreteCategory.hom (φ.app (Opposite.op k'))
            (ConcreteCategory.hom ((X ⊗ G).map (homOfLE g).op)
              ((x, ConcreteCategory.hom (G.map (homOfLE h).op) a) :
                (X ⊗ G).obj (Opposite.op k))) =
          ConcreteCategory.hom (H.map (homOfLE g).op)
            (ConcreteCategory.hom (φ.app (Opposite.op k))
              ((x, ConcreteCategory.hom (G.map (homOfLE h).op) a) :
                (X ⊗ G).obj (Opposite.op k))) at hphi
        rw [hmap] at hphi
        dsimp only
        rw [hcomp]
        exact hphi⟩)
    naturality j j' f := by
      refine ConcreteCategory.hom_ext _ _ fun a => ?_
      simp only [CategoryTheory.comp_apply]
      refine Subtype.ext (funext fun k => funext fun h => funext fun x => ?_)
      show ConcreteCategory.hom (φ.app (Opposite.op k))
          ((x, ConcreteCategory.hom (G.map (homOfLE h).op) (ConcreteCategory.hom (G.map f) a)) :
            (X ⊗ G).obj (Opposite.op k))
        = ConcreteCategory.hom (φ.app (Opposite.op k))
          ((x, ConcreteCategory.hom (G.map (homOfLE (h.trans (leOfHom f.unop))).op) a) :
            (X ⊗ G).obj (Opposite.op k))
      refine congrArg _ (Prod.ext rfl ?_)
      have := ConcreteCategory.congr_hom (G.map_comp f ((homOfLE h).op)) a
      simp only [CategoryTheory.comp_apply] at this
      exact this.symm

  def ℐ.parrUntranspose.{u} {X G H : ℐ.{u}} (ψ : G ⟶ ℐ.parr X H) : X ⊗ G ⟶ H where
    app j := ↾(fun p => (ConcreteCategory.hom (ψ.app j) p.2).1 (unop j) (le_refl _) p.1)
    naturality j j' f := by
      refine ConcreteCategory.hom_ext _ _ fun p => ?_
      have hnat := ConcreteCategory.congr_hom (ψ.naturality f) p.2
      simp only [CategoryTheory.comp_apply] at hnat
      show (ConcreteCategory.hom (ψ.app j') (ConcreteCategory.hom (G.map f) p.2)).1
          (unop j') (le_refl _) (ConcreteCategory.hom (X.map f) p.1)
        = ConcreteCategory.hom (H.map f)
          ((ConcreteCategory.hom (ψ.app j) p.2).1 (unop j) (le_refl _) p.1)
      rw [hnat]
      exact (ConcreteCategory.hom (ψ.app j) p.2).2 (unop j') (unop j)
        (leOfHom f.unop) (le_refl _) p.1

  def ℐ.parrAdj.{u} (X : ℐ.{u}) : MonoidalCategory.tensorLeft X ⊣ ℐ.parrFunctor X :=
    Adjunction.mkOfHomEquiv
      { homEquiv := fun G H =>
          { toFun := fun φ => ℐ.parrTranspose φ
            invFun := fun ψ => ℐ.parrUntranspose ψ
            left_inv := fun φ => by
              refine NatTrans.ext (funext fun j => ?_)
              refine ConcreteCategory.hom_ext _ _ fun p => ?_
              change X.obj j × G.obj j at p
              change ConcreteCategory.hom (φ.app j)
                (p.1, ConcreteCategory.hom (G.map (homOfLE (le_refl (unop j))).op) p.2) =
                ConcreteCategory.hom (φ.app j) p
              exact congrArg (ConcreteCategory.hom (φ.app j)) (Prod.ext rfl
                (by rw [show (homOfLE (le_refl (unop j))).op = 𝟙 j from rfl, G.map_id]; rfl))
            right_inv := fun ψ => by
              refine NatTrans.ext (funext fun j => ?_)
              refine ConcreteCategory.hom_ext _ _ fun a => ?_
              refine Subtype.ext (funext fun k => funext fun h => funext fun x => ?_)
              simp only [ℐ.parrTranspose, ℐ.parrUntranspose, ConcreteCategory.hom_ofHom]
              have hnat := ConcreteCategory.congr_hom
                (ψ.naturality ((homOfLE h).op : j ⟶ Opposite.op k)) a
              simp only [CategoryTheory.comp_apply] at hnat
              exact congrArg (fun (t : ℐ.parrObj X H k) => t.1 k (le_refl k) x) hnat }
        homEquiv_naturality_left_symm := fun f g => rfl
        homEquiv_naturality_right := fun f g => by
          refine NatTrans.ext (funext fun j => ?_)
          refine ConcreteCategory.hom_ext _ _ fun a => ?_
          refine Subtype.ext (funext fun k => funext fun h => funext fun x => ?_)
          rfl }

  instance (priority := 1100) ℐ.closed.{u} (X : ℐ.{u}) : Closed X where
    rightAdj := ℐ.parrFunctor X
    adj := ℐ.parrAdj X

  instance (priority := 1100) ℐ.monoidalClosed.{u} : MonoidalClosed ℐ.{u} where
    closed X := ℐ.closed X

  @[simp, implicit_reducible]
  def earlier_obj.{u} (F : ℐ.{u}) : ℐ.{u} :=
  {
    obj α := F.obj (op (α.unop + 1))
    map {X Y} f := F.map (op (homOfLE (Nat.succ_le_succ (leOfHom f.unop))))
    map_id {X} := by simp; rw [<-CategoryTheory.Functor.map_id]; rfl
    map_comp {X Y Z} f g := by simp; rw [<-CategoryTheory.Functor.map_comp]; congr
  }

  @[simp]
  def earlier_arr {F G : ℐ.{u}} (h : F ⟶ G)
    : (earlier_obj F) ⟶ (earlier_obj G) :=
  {
    app x := h.app (op (x.unop + 1))
  }

  def earlier : ℐ.{u} ⥤ ℐ.{u} :=
  {
    obj F := earlier_obj F
    map {X Y} f := earlier_arr f
  }

  @[simp, implicit_reducible]
  def later_obj.{u} (F : ℐ.{u}) : ℐ.{u} :=
  {
    obj α := match α with
    | (op Nat.zero) => PUnit
    | (op (Nat.succ β)) => F.obj (op β)
    map {X Y} := match X with
    | op Nat.zero => match Y with
      | op Nat.zero => λ _ ↦ CategoryStruct.id _
      | op (Nat.succ Y') => λ f ↦ False.elim (Nat.not_succ_le_zero _ (leOfHom f.unop))
    | op (Nat.succ X') => match Y with
      | op Nat.zero => λ f ↦ ↾(fun _ : F.obj (op X') ↦ (PUnit.unit : PUnit.{u+1}))
      | op (Nat.succ Y') => λ f ↦
        F.map (op (homOfLE (Nat.le_of_succ_le_succ (leOfHom f.unop))))
    map_id {X} := match X with
    | op Nat.zero => by simp
    | op (Nat.succ X') => by simp; rw [<-CategoryTheory.Functor.map_id]; rfl
    map_comp {X Y Z} f g := match X with
    | op Nat.zero => match Y with
      | op Nat.zero => match Z with
        | op Nat.zero => by simp
        | op (Nat.succ Z') => by simp
      | op (Nat.succ Y') => match Z with
        | op Nat.zero => by
          exfalso
          apply (Nat.not_succ_le_zero _ (leOfHom f.unop))
        | op (Nat.succ Z') => by
          exfalso
          apply (Nat.not_succ_le_zero _ (leOfHom f.unop))
    | op (Nat.succ X') => match Y with
      | op Nat.zero => match Z with
        | op Nat.zero => by simp
        | op (Nat.succ Z') => by
          exfalso
          apply (Nat.not_succ_le_zero _ (leOfHom g.unop))
      | op (Nat.succ Y') => match Z with
        | op Nat.zero => by ext
        | op (Nat.succ Z') => by
          simp
          rw [<-Functor.map_comp]
          congr
  }

  @[simp]
  def later_arr {F G : ℐ.{u}} (h : F ⟶ G)
    : (later_obj F) ⟶ (later_obj G) :=
  {
    app {X} := match X with
    | op Nat.zero => CategoryStruct.id _
    | op (Nat.succ X') => h.app (op X')
    naturality {X Y} f := match X with
    | op Nat.zero => match Y with
      | op Nat.zero => by simp
      | op (Nat.succ Y') => by
        exfalso
        apply (Nat.not_succ_le_zero _ (leOfHom f.unop))
    | op (Nat.succ X') => match Y with
      | op Nat.zero => by ext; simp
      | op (Nat.succ Y') => by simp
  }

  def later : ℐ.{u} ⥤ ℐ.{u} :=
  {
    obj := later_obj
    map := later_arr
    map_id {X} := by
      simp; apply CategoryTheory.NatTrans.ext; simp
      ext x
      cases x with
      | op x => cases x with
        | zero => simp
        | succ x' => simp
    map_comp {X Y Z} f g := by
      simp; apply CategoryTheory.NatTrans.ext; simp
      ext x
      cases x with
      | op x => cases x with
        | zero => simp
        | succ x' => simp
  }

  @[simp] theorem later_obj_obj_zero.{u} (X : ℐ.{u}) :
      (later.obj X).obj (op 0) = PUnit.{u+1} := rfl
  @[simp] theorem later_obj_obj_succ.{u} (X : ℐ.{u}) (n : ℕ) :
      (later.obj X).obj (op (n + 1)) = X.obj (op n) := rfl

  @[simp]
  def unit_adj : 𝟭 (ℐ.{u}) ⟶ earlier.{u} ⋙ later.{u} :=
  {
    app x :=
    {
      app n := match n with
      | op Nat.zero => ↾(fun _ : x.obj (op 0) ↦ (PUnit.unit : PUnit.{u+1}))
      | op (Nat.succ n') => ↾(fun y : x.obj (op n'.succ) ↦ y)
      naturality {X Y} f := match X with
      | op Nat.zero => match Y with
        | op Nat.zero => by
          ext x
          change PUnit.unit = PUnit.unit
          rfl
        | op (Nat.succ Y') => by
          exfalso
          apply (Nat.not_succ_le_zero _ (leOfHom f.unop))
      | op (Nat.succ X') => match Y with
        | op Nat.zero => by
          ext x
          change PUnit.unit = PUnit.unit
          rfl
        | op (Nat.succ Y') => by
          ext x
          simp only [Functor.id_obj]
          congr 1
    }
    naturality {X Y} f := by
      apply CategoryTheory.NatTrans.ext
      ext x
      cases x with
      | op x => cases x with
        | zero =>
          change PUnit.unit = PUnit.unit
          rfl
        | succ x' =>
          congr 1
  }

  @[simp]
  def counit_adj : later.{u} ⋙ earlier.{u} ⟶ 𝟭 (ℐ.{u}) :=
  {
    app x :=
    {
      app n := match n with
      | op Nat.zero => ↾(fun y : x.obj (op 0) ↦ y)
      | op (Nat.succ n') => ↾(fun y : x.obj (op n'.succ) ↦ y)
    }
    naturality {X Y} f := by
      apply CategoryTheory.NatTrans.ext
      ext x
      cases x with
      | op x => cases x with
        | zero =>
          congr 1
        | succ x' =>
          congr 1
  }

  def earlier_later_adj : earlier.{u} ⊣ later.{u} :=
  {
    unit := unit_adj
    counit := counit_adj
    left_triangle_components X := by
      apply CategoryTheory.NatTrans.ext
      ext x a
      simp [later, earlier]
      cases x with
      | op x => cases x with
        | zero => rfl
        | succ x' => rfl
    right_triangle_components Y := by
      apply CategoryTheory.NatTrans.ext
      ext x a
      simp [later, earlier]
      cases x with
      | op x => cases x with
        | zero => exact Subsingleton.elim _ _
        | succ x' =>
          cases x' with
          | zero => rfl
          | succ x'' => rfl
  }

  @[simp]
  def next_app X : X ⟶ (later.obj X) :=
  {
    app {x} := match x with
    | op Nat.zero => ↾(fun _ : X.obj (op 0) ↦ PUnit.unit)
    | op (Nat.succ x') => X.map (op (homOfLE (Nat.le_succ _)))
    naturality {x y} f := by
      ext z; simp
      cases x with
      | op x => cases x with
        | zero => cases y with
          | op y => cases y with
            | zero => simp [later]
            | succ y' =>
              simp
              exfalso
              apply (Nat.not_succ_le_zero _ (leOfHom f.unop))
        | succ x' => cases y with
          | op y => cases y with
            | zero => simp [later]
            | succ y' =>
              show (ConcreteCategory.hom (X.map (op (homOfLE (Nat.le_succ y'))))) ((ConcreteCategory.hom (X.map f)) z) =
                (ConcreteCategory.hom (X.map (op (homOfLE (Nat.le_of_succ_le_succ (leOfHom f.unop))))))
                ((ConcreteCategory.hom (X.map (op (homOfLE (Nat.le_succ x'))))) z)
              rw [← CategoryTheory.Functor.map_comp_apply X f (op (homOfLE _))]
              rw [← CategoryTheory.Functor.map_comp_apply X (op (homOfLE _)) (op (homOfLE _))]
              congr 1
  }

  def next : 𝟭 (ℐ.{u}) ⟶ later :=
  {
    app X := next_app X
    naturality {X Y} f := by
      apply CategoryTheory.NatTrans.ext
      ext x a
      cases x with
      | op x => cases x with
        | zero => simp [later]
        | succ x =>
          simp [later]
  }

  def force_app X : (earlier.obj X) ⟶ X :=
  {
    app n := X.map (op (homOfLE (Nat.le_succ _)))
    naturality {A B} f := by
      simp [earlier]
      rw [<-X.map_comp]
      rw [<-X.map_comp]
      congr 1
  }

  def force : earlier ⟶ 𝟭 (ℐ.{u}) :=
  {
    app X := force_app X
    naturality {A B} f := by
      simp [earlier, force_app]
      apply CategoryTheory.NatTrans.ext
      ext x a
      rw [CategoryTheory.NatTrans.vcomp_app']
      rw [<-CategoryTheory.NatTrans.vcomp_app]
      cases x with
      | op x =>
        simp
  }

  def earlier_prod_app_hom A B : earlier.obj (A ⊗ B) ⟶ earlier.obj A ⊗ earlier.obj B :=
    CartesianMonoidalCategory.lift (earlier.map (CartesianMonoidalCategory.fst _ _)) (earlier.map (CartesianMonoidalCategory.snd _ _))

  def earlier_prod_app_inv A B : earlier.obj A ⊗ earlier.obj B ⟶ earlier.obj (A ⊗ B) :=
  {
    app X := ↾(id : (earlier.obj A ⊗ earlier.obj B).obj X → _)
  }

  def earlier_prod_app A B : earlier.obj (A ⊗ B) ≅ earlier.obj A ⊗ earlier.obj B :=
    eqToIso (by rfl)

  def earlier_prod_hom : tensor ℐ ⋙ earlier ⟶ prodFunctor.obj (earlier, earlier) ⋙ tensor ℐ :=
  {
    app X := eqToHom (by rfl)
    naturality {A B} f := by
      simp only [earlier, earlier_arr]
      rfl
  }

  def earlier_prod_inv : prodFunctor.obj (earlier, earlier) ⋙ tensor ℐ ⟶ tensor ℐ ⋙ earlier :=
  {
    app X := earlier_prod_app_inv X.1 X.2
    naturality {A B} f := by
      apply NatTrans.ext; ext x a
      simp only [earlier_prod_app_inv, Functor.comp_map, NatTrans.comp_app]
      rfl
  }

  def earlier_prod : tensor ℐ.{u} ⋙ earlier ≅ (prodFunctor.obj ⟨earlier, earlier⟩) ⋙ tensor ℐ.{u} :=
  {
    hom := earlier_prod_hom
    inv := earlier_prod_inv
    hom_inv_id := by
      apply NatTrans.ext; ext ⟨A, B⟩ x a
      simp only [earlier_prod_hom, earlier_prod_inv, NatTrans.comp_app,
        earlier_prod_app_inv, eqToHom_app]
      congr 1
    inv_hom_id := by
      apply NatTrans.ext; ext ⟨A, B⟩ x a
      simp only [earlier_prod_hom, earlier_prod_inv, NatTrans.comp_app,
        earlier_prod_app_inv, eqToHom_app]
      congr 1
  }

  def earlier_split_app_hom A B : earlier.obj A ⊗ B ⟶ earlier.obj (A ⊗ later.obj B) :=
  {
    app X := ↾(id : (earlier.obj A ⊗ B).obj X → _)
  }

  def earlier_split_app_inv A B : earlier.obj (A ⊗ later.obj B) ⟶ earlier.obj A ⊗ B :=
    CartesianMonoidalCategory.lift (earlier.map (CartesianMonoidalCategory.fst _ _)) (earlier.map (CartesianMonoidalCategory.snd _ _) ≫ earlier_later_adj.counit.app _)

  def earlier_split_app A B : earlier.obj A ⊗ B ≅ earlier.obj (A ⊗ later.obj B) :=
  {
    hom := earlier_split_app_hom A B
    inv := earlier_split_app_inv A B
    hom_inv_id := by
      apply NatTrans.ext; ext x a
      simp [earlier_split_app_hom, earlier_split_app_inv,
            Monoidal.fst_app, Monoidal.snd_app, later, earlier]
      cases x with
      | op x => cases x with
        | zero => rfl
        | succ x' => rfl
    inv_hom_id := by
      apply NatTrans.ext; ext x a
      simp [earlier_split_app_hom, earlier_split_app_inv,
            Monoidal.fst_app, Monoidal.snd_app, later, earlier]
      cases x with
      | op x => cases x with
        | zero => rfl
        | succ x' => rfl
  }

  def earlier_split_hom : prodFunctor.obj (earlier, 𝟭 ℐ) ⋙ tensor ℐ ⟶ prodFunctor.obj (𝟭 ℐ, later) ⋙ tensor ℐ ⋙ earlier :=
  {
    app X := earlier_split_app_hom X.1 X.2
    naturality {A B} f := by
      apply NatTrans.ext; ext x a
      simp only [earlier_split_app_hom, Functor.comp_map, NatTrans.comp_app]
      rfl
  }

  def earlier_split_inv : prodFunctor.obj (𝟭 ℐ, later) ⋙ tensor ℐ ⋙ earlier ⟶ prodFunctor.obj (earlier, 𝟭 ℐ) ⋙ tensor ℐ :=
  {
    app X := earlier_split_app_inv X.1 X.2
    naturality {A B} f := by
      apply NatTrans.ext; ext x a
      simp [earlier_split_app_inv, Monoidal.fst_app, Monoidal.snd_app,
            later, earlier]
      cases x with
      | op x => cases x with
        | zero => rfl
        | succ x' => rfl
  }

  def earlier_split : (prodFunctor.obj ⟨earlier, 𝟭 ℐ.{u}⟩) ⋙ tensor ℐ.{u} ≅ (prodFunctor.obj ⟨𝟭 ℐ.{u}, later⟩) ⋙ tensor ℐ.{u} ⋙ earlier :=
  {
    hom := earlier_split_hom
    inv := earlier_split_inv
    hom_inv_id := by
      apply NatTrans.ext; ext ⟨A, B⟩ x a
      simp only [earlier_split_hom, earlier_split_inv, NatTrans.comp_app]
      exact CategoryTheory.types_congr_hom
        (NatTrans.congr_app ((earlier_split_app A B).hom_inv_id) x) a
    inv_hom_id := by
      apply NatTrans.ext; ext ⟨A, B⟩ x a
      simp only [earlier_split_hom, earlier_split_inv, NatTrans.comp_app]
      exact CategoryTheory.types_congr_hom
        (NatTrans.congr_app ((earlier_split_app A B).inv_hom_id) x) a
  }

  def later_exp.{u} (A : ℐ.{u}) : (ihom A) ⋙ later ≅ later ⋙ (ihom (later.obj A)) :=
    ((earlier_later_adj.{u}.comp (ihom.adjunction A))).rightAdjointUniq
      ((ihom.adjunction (later.obj A)).comp (earlier_later_adj.{u}))

  instance earlier_oplax : OplaxMonoidal earlier := CategoryTheory.Functor.OplaxMonoidal.ofChosenFiniteProducts earlier

  instance later_lax : LaxMonoidal later := Adjunction.rightAdjointLaxMonoidal earlier_later_adj

  @[simp]
  theorem next_μ (A B : ℐ.{u}) :
      (next.app A ⊗ₘ next.app B) ≫ LaxMonoidal.μ later A B = next.app (A ⊗ B) := by
    refine Eq.trans (congrArg ((next.app A ⊗ₘ next.app B) ≫ ·)
      (rfl : LaxMonoidal.μ later A B = earlier_later_adj.homEquiv _ _
        (Functor.OplaxMonoidal.δ earlier _ _ ≫
          (earlier_later_adj.counit.app A ⊗ₘ earlier_later_adj.counit.app B)))) ?_
    refine Eq.trans (Adjunction.homEquiv_naturality_left _ _ _).symm ?_
    refine (earlier_later_adj.homEquiv _ _).symm.injective ?_
    refine Eq.trans (Equiv.symm_apply_apply _ _) ?_
    rw [Adjunction.homEquiv_counit, show Functor.OplaxMonoidal.δ earlier (later.obj A) (later.obj B)
        = CartesianMonoidalCategory.prodComparison earlier (later.obj A) (later.obj B) from rfl]
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_ <;>
      simp [← Functor.map_comp_assoc, - Functor.map_comp,
        ← Adjunction.counit_naturality]
    · exact congrArg (fun t => earlier.map t ≫ earlier_later_adj.counit.app A)
        (next.naturality (SemiCartesianMonoidalCategory.fst A B))
    · exact congrArg (fun t => earlier.map t ≫ earlier_later_adj.counit.app B)
        (next.naturality (SemiCartesianMonoidalCategory.snd A B))

  def later_exp_hom (A B : ℐ.{u}) : later.obj ((ihom A).obj B) ⟶ (ihom (later.obj A)).obj (later.obj B) :=
    MonoidalClosed.curry (LaxMonoidal.μ _ _ _ ≫ later.map ((ihom.ev A).app B))

  @[simp]
  theorem later_exp_app_unfold {A B : ℐ.{u}} :
    (later_exp A).hom.app B = later_exp_hom A B := by
      have key : ((((ihom.adjunction (later.obj A)).comp
            earlier_later_adj.{u}).homEquiv _ _).symm ((later_exp A).hom.app B))
          = (earlier_later_adj.{u}.comp (ihom.adjunction A)).counit.app B :=
        Adjunction.homEquiv_symm_rightAdjointUniq_hom_app
          (earlier_later_adj.{u}.comp (ihom.adjunction A))
          ((ihom.adjunction (later.obj A)).comp earlier_later_adj.{u}) B
      refine (((ihom.adjunction (later.obj A)).comp
        earlier_later_adj.{u}).homEquiv _ _).symm.injective ?_
      rw [key]
      refine NatTrans.ext (funext fun n => ?_)
      refine ConcreteCategory.hom_ext _ _ fun p => ?_
      cases n with
      | op m =>
        cases m with
        | zero => rfl
        | succ m' => rfl

  def earlier_terminal.{u} : earlier.obj.{u} (𝟙_ _) ≅ 𝟙_ _ :=
  {
    hom := earlier.map (next.app _) ≫ earlier_later_adj.counit.app _
    inv :=
    {
      app X := ↾(fun _ : (𝟙_ ℐ.{u}).obj X ↦ (PUnit.unit : PUnit.{u+1}))
    }
  }

end Base

section iter
  open CategoryTheory
  open Functor

  namespace CategoryTheory
  namespace Functor

  @[simp]
  def iter {C : Type*} [Category C] (F : C ⥤ C) (i : Nat) : C ⥤ C :=
    match i with
    | .zero => 𝟭 _
    | .succ i' => Functor.iter F i' ⋙ F

  @[simp]
  def iter' {C : Type*} [Category C] (F : C ⥤ C) (i : Nat) : C ⥤ C :=
    match i with
    | .zero => 𝟭 _
    | .succ i' => F ⋙ Functor.iter' F i'

  lemma iter'_comm {C : Type*} [Category C] {F : C ⥤ C} {i : Nat} :
    F.iter' i ⋙ F = F ⋙ F.iter' i := by
    induction i with
    | zero =>
      rfl
    | succ i' IH =>
      simp only [iter']
      rw [Functor.assoc, IH]

  lemma iter_iter' {C : Type*} [Category C] {F : C ⥤ C} {i : Nat} :
    iter F i = iter' F i := by
    induction i with
    | zero => simp
    | succ i' IH =>
      simp [IH, iter'_comm]

  lemma iter_add {C : Type*} [Category C] (F : C ⥤ C) (i j : Nat) :
      iter F (i + j) = iter F i ⋙ iter F j := by
    induction i with
    | zero => simp [Functor.id_comp]
    | succ i' IH =>
      simp only [iter, Nat.succ_add]
      rw [IH]
      simp only [CategoryTheory.Functor.assoc]
      congr 1
      rw [iter_iter' (F := F) (i := j), iter'_comm, ← iter_iter' (F := F) (i := j)]

  lemma iter_add_comm {C : Type*} [Category C] (F : C ⥤ C) (i j : Nat) :
      iter F (i + j) = iter F (j + i) := by
    congr 1; omega

  lemma iter_add_assoc {C : Type*} [Category C] (F : C ⥤ C) (i j k : Nat) :
      iter F (i + (j + k)) = iter F (i + j + k) := by
    congr 1; omega

  lemma eqToHom_hcomp {C D E : Type*} [Category C] [Category D] [Category E]
    (F1 F2 : C ⥤ D) (G : D ⥤ E) {heq' : F1 ⋙ G = F2 ⋙ G} (heq : F1 = F2)
    : eqToHom heq' = eqToHom heq ◫ (𝟙 _) := by
    cases heq
    cases heq'
    simp

  end Functor
  end CategoryTheory

end iter
end
