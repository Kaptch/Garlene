module

public import SynthDom.Semantics.Univ.Polynomial

@[expose] public section

section constructors
  open CategoryTheory Functor MonoidalCategory CartesianMonoidalCategory

  def famArrObj {n : ℕ} (A B : (Over n)ᵒᵖ ⥤ Type i) (w : Over n) : Type i :=
    { app : ∀ (k : ℕ) (h : k ≤ w.left),
        (A.obj (Opposite.op (Over.mk (homOfLE (h.trans (leOfHom w.hom))))) →
         B.obj (Opposite.op (Over.mk (homOfLE (h.trans (leOfHom w.hom)))))) //
      ∀ (k' k : ℕ) (g : k' ≤ k) (h : k ≤ w.left)
        (x : A.obj (Opposite.op (Over.mk (homOfLE (h.trans (leOfHom w.hom)))))),
        app k' (g.trans h) (A.map (Opposite.op (Over.homMk (homOfLE g))) x)
          = B.map (Opposite.op (Over.homMk (homOfLE g))) (app k h x) }

  def famArr {n : ℕ} (A B : (Over n)ᵒᵖ ⥤ Type i) : (Over n)ᵒᵖ ⥤ Type i where
    obj w := famArrObj A B w.unop
    map {w w'} f := ↾(fun φ => ⟨fun k h => φ.1 k (h.trans (leOfHom f.unop.left)),
      fun k' k g h x => φ.2 k' k g (h.trans (leOfHom f.unop.left)) x⟩)
    map_id w := by ext φ; rfl
    map_comp f g := by ext φ; rfl

  unseal U in
  @[irreducible]
  def U_arr' : U.{i} ⊗ U.{i} ⟶ U.{i} where
    app n := ↾(fun x => U.mk (famArr (U.el x.1) (U.el x.2)))
    naturality {X Y} f := by
      refine ConcreteCategory.hom_ext _ _ fun x => ?_
      show U.mk (famArr _ _) = ConcreteCategory.hom (U.map f) (U.mk (famArr _ _))
      rw [U.map_mk]
      refine congrArg U.mk (CategoryTheory.Functor.ext (fun w => rfl) ?_)
      intro a b φ
      rfl
  @[irreducible]
  def U_arr : 𝟙_ _ ⟶ (ihom (U.{i} ⊗ U.{i})).obj U.{i} := MonoidalClosed.curry' U_arr'

  unseal U U_arr U_arr' in
  lemma U_arr_el {τ1 τ2 : 𝟙_ ℐ.{i + 1} ⟶ U.{i}} (a : ℕᵒᵖ) :
      U.el (ConcreteCategory.hom ((CartesianMonoidalCategory.lift τ1 τ2 ≫ MonoidalClosed.uncurry' U_arr).app a) (unitPt a)) =
        famArr (U.el (ConcreteCategory.hom (τ1.app a) (unitPt a)))
          (U.el (ConcreteCategory.hom (τ2.app a) (unitPt a))) := by
    rw [U_arr, MonoidalClosed.uncurry'_curry']; rfl

  private lemma subtype_congr' {α β : Sort v} {p : α → Prop} {q : β → Prop}
      (h : α = β) (hpq : ∀ (a : α) (b : β), a ≍ b → (p a ↔ q b)) : Subtype p = Subtype q := by
    subst h
    exact congrArg Subtype (funext fun a => propext (hpq a a HEq.rfl))

  private lemma heq_pi_apply {α : Sort u_1} {β γ : α → Sort v} (hβγ : ∀ a, β a = γ a)
      {f : ∀ a, β a} {g : ∀ a, γ a} (hfg : f ≍ g) (a : α) : f a ≍ g a := by
    obtain rfl := funext hβγ
    rw [eq_of_heq hfg]

  private lemma heq_apply {T1 T2 S1 S2 : Sort v} (hT : T1 = T2) (hS : S1 = S2)
      {f : T1 → S1} {g : T2 → S2} (hfg : f ≍ g) {x : T1} {y : T2} (hxy : x ≍ y) :
      f x ≍ g y := by
    subst hT; subst hS
    rw [eq_of_heq hfg, eq_of_heq hxy]

  private lemma eq_iff_heq {T S : Sort v} (h : T = S) {a b : T} {c d : S}
      (hac : a ≍ c) (hbd : b ≍ d) : a = b ↔ c = d := by
    subst h
    rw [eq_of_heq hac, eq_of_heq hbd]

  unseal classify U in
  private lemma el_obj_eq_classify_obj {τ : 𝟙_ ℐ.{i + 1} ⟶ U.{i}} {j k : ℕ} (h : k ≤ j) :
      (U.el (ConcreteCategory.hom (τ.app (Opposite.op j)) (unitPt (Opposite.op j)))).obj
          (Opposite.op (Over.mk (homOfLE h))) =
        (ConcreteCategory.hom classify.hom τ).obj (Opposite.op k) :=
    (Functor.congr_obj (classify_nat (f := τ) ((homOfLE h).op))
      (Opposite.op (Over.mk (𝟙 k)))).symm

  private lemma comp_apply' {T S R : Type v} (f : T ⟶ S) (g : S ⟶ R) (x : T) :
      ConcreteCategory.hom (f ≫ g) x = ConcreteCategory.hom g (ConcreteCategory.hom f x) := rfl

  private lemma eqToHom_apply_eq_cast {T S : Type v} (p : T = S) (x : T) :
      ConcreteCategory.hom (eqToHom p) x = cast p x := by
    subst p; simp

  unseal classify U in
  private lemma el_map_heq_classify_map {τ : 𝟙_ ℐ.{i + 1} ⟶ U.{i}} {j k' k : ℕ}
      (g : k' ≤ k) (h : k ≤ j) (x : (ConcreteCategory.hom classify.hom τ).obj (Opposite.op k)) :
      ConcreteCategory.hom ((ConcreteCategory.hom classify.hom τ).map (homOfLE g).op) x
        ≍ ConcreteCategory.hom
            ((U.el (ConcreteCategory.hom (τ.app (Opposite.op j)) (unitPt (Opposite.op j)))).map
              (Opposite.op (Over.homMk (homOfLE g) :
                (Over.mk (homOfLE (g.trans h)) : Over j) ⟶ Over.mk (homOfLE h))))
            (cast (el_obj_eq_classify_obj (τ := τ) h).symm x) := by
    have hcm := ConcreteCategory.congr_hom (classify_hom_map (f := τ) ((homOfLE g).op)) x
    have happ := ConcreteCategory.congr_hom
      (Functor.congr_hom (classify_nat (f := τ) ((homOfLE h).op))
        (Opposite.op (Over.homMk ((homOfLE g).op.unop) :
          (Over.mk ((homOfLE g).op.unop) : Over k) ⟶ Over.mk (𝟙 k)))) x
    refine (heq_of_eq hcm).trans ?_
    refine (heq_of_eq (comp_apply' _ _ x)).trans ?_
    refine (heq_of_eq (eqToHom_apply_eq_cast _ _)).trans ?_
    refine (cast_heq _ _).trans ?_
    refine (heq_of_eq happ).trans ?_
    refine (heq_of_eq (comp_apply' _ _ x)).trans ?_
    refine (heq_of_eq (comp_apply' _ _ _)).trans ?_
    refine (heq_of_eq (eqToHom_apply_eq_cast _ _)).trans ?_
    refine (cast_heq _ _).trans ?_
    erw [eqToHom_apply_eq_cast]
    exact HEq.rfl

  private lemma subtype_heq {α β : Sort v} {p : α → Prop} {q : β → Prop}
      (h : α = β) (hpq : p ≍ q) {a : Subtype p} {b : Subtype q}
      (hab : a.1 ≍ b.1) : a ≍ b := by
    subst h
    cases eq_of_heq hpq
    exact heq_of_eq (Subtype.ext (eq_of_heq hab))

  private lemma subtype_val_heq {α β : Sort v} {p : α → Prop} {q : β → Prop}
      (h : α = β) (hpq : p ≍ q) {a : Subtype p} {b : Subtype q}
      (hab : a ≍ b) : a.1 ≍ b.1 := by
    subst h
    cases eq_of_heq hpq
    exact heq_of_eq (congrArg Subtype.val (eq_of_heq hab))

  unseal classify U in
  private lemma famArrObj_carrier_eq_parrObj {τ1 τ2 : 𝟙_ ℐ.{i + 1} ⟶ U.{i}} {n : ℕ} (w : Over n) :
      (∀ (k : ℕ) (h : k ≤ w.left),
        ((U.el (ConcreteCategory.hom (τ1.app (Opposite.op n)) (unitPt (Opposite.op n)))).obj
            (Opposite.op (Over.mk (homOfLE (h.trans (leOfHom w.hom))))) →
          (U.el (ConcreteCategory.hom (τ2.app (Opposite.op n)) (unitPt (Opposite.op n)))).obj
            (Opposite.op (Over.mk (homOfLE (h.trans (leOfHom w.hom)))))))
      = (∀ (k : ℕ), k ≤ w.left →
          ((ConcreteCategory.hom classify.hom τ1).obj (Opposite.op k) →
            (ConcreteCategory.hom classify.hom τ2).obj (Opposite.op k))) := by
    refine pi_congr fun k => ?_
    refine pi_congr fun hk => ?_
    exact (congrArg (· → _) (el_obj_eq_classify_obj (τ := τ1) (hk.trans (leOfHom w.hom)))).trans
      (congrArg (_ → ·) (el_obj_eq_classify_obj (τ := τ2) (hk.trans (leOfHom w.hom))))

  unseal classify U in
  private lemma famArr_pred_iff {τ1 τ2 : 𝟙_ ℐ.{i + 1} ⟶ U.{i}} {n : ℕ} (w : Over n)
      (a : ∀ (k : ℕ) (h : k ≤ w.left),
        ((U.el (ConcreteCategory.hom (τ1.app (Opposite.op n)) (unitPt (Opposite.op n)))).obj
            (Opposite.op (Over.mk (homOfLE (h.trans (leOfHom w.hom))))) →
          (U.el (ConcreteCategory.hom (τ2.app (Opposite.op n)) (unitPt (Opposite.op n)))).obj
            (Opposite.op (Over.mk (homOfLE (h.trans (leOfHom w.hom)))))))
      (b : ∀ (k : ℕ), k ≤ w.left →
          ((ConcreteCategory.hom classify.hom τ1).obj (Opposite.op k) →
            (ConcreteCategory.hom classify.hom τ2).obj (Opposite.op k)))
      (hab : a ≍ b) :
      (∀ (k' k : ℕ) (g : k' ≤ k) (h : k ≤ w.left)
        (x : (U.el (ConcreteCategory.hom (τ1.app (Opposite.op n)) (unitPt (Opposite.op n)))).obj
          (Opposite.op (Over.mk (homOfLE (h.trans (leOfHom w.hom)))))),
        a k' (g.trans h)
            ((U.el (ConcreteCategory.hom (τ1.app (Opposite.op n)) (unitPt (Opposite.op n)))).map
              (Opposite.op (Over.homMk (homOfLE g))) x)
          = (U.el (ConcreteCategory.hom (τ2.app (Opposite.op n)) (unitPt (Opposite.op n)))).map
              (Opposite.op (Over.homMk (homOfLE g))) (a k h x))
      ↔ (∀ (k' k : ℕ) (g : k' ≤ k) (h : k ≤ w.left)
          (x : (ConcreteCategory.hom classify.hom τ1).obj (Opposite.op k)),
          b k' (g.trans h) ((ConcreteCategory.hom classify.hom τ1).map (homOfLE g).op x)
            = (ConcreteCategory.hom classify.hom τ2).map (homOfLE g).op (b k h x)) := by
    have hcomp2 : ∀ (k : ℕ) (hk : k ≤ w.left), a k hk ≍ b k hk := fun k hk =>
      heq_pi_apply (fun hk' =>
          (congrArg (· → _) (el_obj_eq_classify_obj (τ := τ1) (hk'.trans (leOfHom w.hom)))).trans
            (congrArg (_ → ·) (el_obj_eq_classify_obj (τ := τ2) (hk'.trans (leOfHom w.hom)))))
        (heq_pi_apply (fun k' => pi_congr fun hk' =>
            (congrArg (· → _) (el_obj_eq_classify_obj (τ := τ1) (hk'.trans (leOfHom w.hom)))).trans
              (congrArg (_ → ·) (el_obj_eq_classify_obj (τ := τ2) (hk'.trans (leOfHom w.hom)))))
          hab k) hk
    have hval : ∀ (k : ℕ) (hk : k ≤ w.left)
        (x : (ConcreteCategory.hom classify.hom τ1).obj (Opposite.op k)),
        a k hk (cast (el_obj_eq_classify_obj (τ := τ1) (hk.trans (leOfHom w.hom))).symm x)
          ≍ b k hk x := fun k hk x =>
      heq_apply (el_obj_eq_classify_obj (τ := τ1) (hk.trans (leOfHom w.hom)))
        (el_obj_eq_classify_obj (τ := τ2) (hk.trans (leOfHom w.hom)))
        (hcomp2 k hk) (cast_heq _ _)
    have hR : ∀ (k' k : ℕ) (g : k' ≤ k) (hk : k ≤ w.left)
        (x : (ConcreteCategory.hom classify.hom τ1).obj (Opposite.op k)),
        ConcreteCategory.hom
            ((U.el (ConcreteCategory.hom (τ2.app (Opposite.op n)) (unitPt (Opposite.op n)))).map
              (Opposite.op (Over.homMk (homOfLE g) :
                (Over.mk (homOfLE ((g.trans hk).trans (leOfHom w.hom))) : Over n) ⟶
                  Over.mk (homOfLE (hk.trans (leOfHom w.hom))))))
            (a k hk (cast (el_obj_eq_classify_obj (τ := τ1) (hk.trans (leOfHom w.hom))).symm x))
          ≍ ConcreteCategory.hom
              ((ConcreteCategory.hom classify.hom τ2).map (homOfLE g).op) (b k hk x) := by
      intro k' k g hk x
      have hpoint : a k hk (cast (el_obj_eq_classify_obj (τ := τ1) (hk.trans (leOfHom w.hom))).symm x)
          = cast (el_obj_eq_classify_obj (τ := τ2) (hk.trans (leOfHom w.hom))).symm (b k hk x) :=
        eq_of_heq ((hval k hk x).trans (cast_heq _ _).symm)
      refine HEq.trans (heq_of_eq (congrArg
        (ConcreteCategory.hom
          ((U.el (ConcreteCategory.hom (τ2.app (Opposite.op n)) (unitPt (Opposite.op n)))).map
            (Opposite.op (Over.homMk (homOfLE g) :
              (Over.mk (homOfLE ((g.trans hk).trans (leOfHom w.hom))) : Over n) ⟶
                Over.mk (homOfLE (hk.trans (leOfHom w.hom)))))))
        hpoint)) ?_
      exact (el_map_heq_classify_map (τ := τ2) g (hk.trans (leOfHom w.hom)) (b k hk x)).symm
    constructor
    · intro hp k' k g hk x
      exact (eq_iff_heq (el_obj_eq_classify_obj (τ := τ2) ((g.trans hk).trans (leOfHom w.hom)))
        (heq_apply (el_obj_eq_classify_obj (τ := τ1) ((g.trans hk).trans (leOfHom w.hom)))
          (el_obj_eq_classify_obj (τ := τ2) ((g.trans hk).trans (leOfHom w.hom)))
          (hcomp2 k' (g.trans hk))
          (el_map_heq_classify_map (τ := τ1) g (hk.trans (leOfHom w.hom)) x).symm)
        (hR k' k g hk x)).mp
        (hp k' k g hk (cast (el_obj_eq_classify_obj (τ := τ1) (hk.trans (leOfHom w.hom))).symm x))
    · intro hq k' k g hk x''
      have hxx : cast (el_obj_eq_classify_obj (τ := τ1) (hk.trans (leOfHom w.hom))).symm
          (cast (el_obj_eq_classify_obj (τ := τ1) (hk.trans (leOfHom w.hom))) x'') = x'' :=
        eq_of_heq ((cast_heq _ _).trans (cast_heq _ _))
      exact hxx ▸ (eq_iff_heq (el_obj_eq_classify_obj (τ := τ2) ((g.trans hk).trans (leOfHom w.hom)))
        (heq_apply (el_obj_eq_classify_obj (τ := τ1) ((g.trans hk).trans (leOfHom w.hom)))
          (el_obj_eq_classify_obj (τ := τ2) ((g.trans hk).trans (leOfHom w.hom)))
          (hcomp2 k' (g.trans hk))
          (el_map_heq_classify_map (τ := τ1) g (hk.trans (leOfHom w.hom))
            (cast (el_obj_eq_classify_obj (τ := τ1) (hk.trans (leOfHom w.hom))) x'')).symm)
        (hR k' k g hk (cast (el_obj_eq_classify_obj (τ := τ1) (hk.trans (leOfHom w.hom))) x''))).mpr
        (hq k' k g hk (cast (el_obj_eq_classify_obj (τ := τ1) (hk.trans (leOfHom w.hom))) x''))

  unseal classify U in
  private lemma famArr_pred_heq {τ1 τ2 : 𝟙_ ℐ.{i + 1} ⟶ U.{i}} {n : ℕ} (w : Over n) :
      (fun a : ∀ (k : ℕ) (h : k ≤ w.left),
          ((U.el (ConcreteCategory.hom (τ1.app (Opposite.op n)) (unitPt (Opposite.op n)))).obj
              (Opposite.op (Over.mk (homOfLE (h.trans (leOfHom w.hom))))) →
            (U.el (ConcreteCategory.hom (τ2.app (Opposite.op n)) (unitPt (Opposite.op n)))).obj
              (Opposite.op (Over.mk (homOfLE (h.trans (leOfHom w.hom)))))) =>
        ∀ (k' k : ℕ) (g : k' ≤ k) (h : k ≤ w.left)
          (x : (U.el (ConcreteCategory.hom (τ1.app (Opposite.op n)) (unitPt (Opposite.op n)))).obj
            (Opposite.op (Over.mk (homOfLE (h.trans (leOfHom w.hom)))))),
          a k' (g.trans h)
              ((U.el (ConcreteCategory.hom (τ1.app (Opposite.op n)) (unitPt (Opposite.op n)))).map
                (Opposite.op (Over.homMk (homOfLE g))) x)
            = (U.el (ConcreteCategory.hom (τ2.app (Opposite.op n)) (unitPt (Opposite.op n)))).map
                (Opposite.op (Over.homMk (homOfLE g))) (a k h x))
      ≍ (fun b : ∀ (k : ℕ), k ≤ w.left →
            ((ConcreteCategory.hom classify.hom τ1).obj (Opposite.op k) →
              (ConcreteCategory.hom classify.hom τ2).obj (Opposite.op k)) =>
          ∀ (k' k : ℕ) (g : k' ≤ k) (h : k ≤ w.left)
            (x : (ConcreteCategory.hom classify.hom τ1).obj (Opposite.op k)),
            b k' (g.trans h) ((ConcreteCategory.hom classify.hom τ1).map (homOfLE g).op x)
              = (ConcreteCategory.hom classify.hom τ2).map (homOfLE g).op (b k h x)) :=
    Function.hfunext (famArrObj_carrier_eq_parrObj w) fun a b hab =>
      heq_of_eq (propext (famArr_pred_iff w a b hab))

  unseal classify U in
  private lemma famArrObj_eq_parrObj {τ1 τ2 : 𝟙_ ℐ.{i + 1} ⟶ U.{i}} {n : ℕ} (w : Over n) :
      famArrObj (U.el (ConcreteCategory.hom (τ1.app (Opposite.op n)) (unitPt (Opposite.op n))))
        (U.el (ConcreteCategory.hom (τ2.app (Opposite.op n)) (unitPt (Opposite.op n)))) w
      = ℐ.parrObj (ConcreteCategory.hom classify.hom τ1)
          (ConcreteCategory.hom classify.hom τ2) w.left :=
    subtype_congr' (famArrObj_carrier_eq_parrObj w) (famArr_pred_iff w)

  unseal classify U in
  private lemma famArr_shrink_heq {τ1 τ2 : 𝟙_ ℐ.{i + 1} ⟶ U.{i}} {n m : ℕ} (hmn : m ≤ n)
      (s : famArrObj (U.el (ConcreteCategory.hom (τ1.app (Opposite.op n)) (unitPt (Opposite.op n))))
        (U.el (ConcreteCategory.hom (τ2.app (Opposite.op n)) (unitPt (Opposite.op n))))
        (Over.mk (homOfLE (le_refl n))))
      (r : ℐ.parrObj (ConcreteCategory.hom classify.hom τ1)
        (ConcreteCategory.hom classify.hom τ2) n)
      (hsr : s ≍ r) :
      ConcreteCategory.hom
          ((famArr (U.el (ConcreteCategory.hom (τ1.app (Opposite.op n)) (unitPt (Opposite.op n))))
              (U.el (ConcreteCategory.hom (τ2.app (Opposite.op n)) (unitPt (Opposite.op n))))).map
            (Opposite.op (Over.homMk (homOfLE hmn) :
              (Over.mk (homOfLE (hmn.trans (le_refl n))) : Over n) ⟶
                Over.mk (homOfLE (le_refl n)))))
          s
        ≍ ConcreteCategory.hom
            ((ℐ.parr (ConcreteCategory.hom classify.hom τ1)
                (ConcreteCategory.hom classify.hom τ2)).map (homOfLE hmn).op) r := by
    have hvals := subtype_val_heq
      (famArrObj_carrier_eq_parrObj (τ1 := τ1) (τ2 := τ2) (Over.mk (homOfLE (le_refl n))))
      (famArr_pred_heq (τ1 := τ1) (τ2 := τ2) (Over.mk (homOfLE (le_refl n)))) hsr
    have hcomp : ∀ (k : ℕ) (hk : k ≤ n), s.1 k hk ≍ r.1 k hk := fun k hk =>
      heq_pi_apply (fun hk' =>
          (congrArg (· → _) (el_obj_eq_classify_obj (τ := τ1)
            (hk'.trans (leOfHom (Over.mk (homOfLE (le_refl n))).hom)))).trans
            (congrArg (_ → ·) (el_obj_eq_classify_obj (τ := τ2)
              (hk'.trans (leOfHom (Over.mk (homOfLE (le_refl n))).hom)))))
        (heq_pi_apply (fun k' => pi_congr fun hk' =>
            (congrArg (· → _) (el_obj_eq_classify_obj (τ := τ1)
              (hk'.trans (leOfHom (Over.mk (homOfLE (le_refl n))).hom)))).trans
              (congrArg (_ → ·) (el_obj_eq_classify_obj (τ := τ2)
                (hk'.trans (leOfHom (Over.mk (homOfLE (le_refl n))).hom)))))
          hvals k) hk
    refine subtype_heq
      (famArrObj_carrier_eq_parrObj (τ1 := τ1) (τ2 := τ2) (Over.mk (homOfLE hmn)))
      (famArr_pred_heq (τ1 := τ1) (τ2 := τ2) (Over.mk (homOfLE hmn))) ?_
    refine Function.hfunext rfl fun k k' hkk => ?_
    cases eq_of_heq hkk
    refine Function.hfunext rfl fun h h' hh => ?_
    exact hcomp k (h.trans hmn)

  unseal classify U U_arr U_arr' in
  @[simp]
  lemma U_arr_push {τ1 τ2 : 𝟙_ ℐ.{i + 1} ⟶ U.{i}}
    : classify.hom (CartesianMonoidalCategory.lift τ1 τ2 ≫ MonoidalClosed.uncurry' U_arr)
      = ℐ.parr (ConcreteCategory.hom classify.hom τ1) (ConcreteCategory.hom classify.hom τ2) := by
    refine CategoryTheory.Functor.ext (fun j => ?_) ?_
    · exact Eq.trans (Functor.congr_obj (U_arr_el (τ1 := τ1) (τ2 := τ2) j)
        (Opposite.op (Over.mk (𝟙 (Opposite.unop j)))))
        (famArrObj_eq_parrObj (τ1 := τ1) (τ2 := τ2) (Over.mk (𝟙 (Opposite.unop j))))
    · intro X Y f
      refine ConcreteCategory.hom_ext _ _ fun t => ?_
      have hL := el_map_heq_classify_map
        (τ := CartesianMonoidalCategory.lift τ1 τ2 ≫ MonoidalClosed.uncurry' U_arr)
        (leOfHom f.unop) (le_refl (Opposite.unop X)) t
      have happ := ConcreteCategory.congr_hom
        (Functor.congr_hom (U_arr_el (τ1 := τ1) (τ2 := τ2) X)
          (Opposite.op (Over.homMk (homOfLE (leOfHom f.unop)) :
            (Over.mk (homOfLE ((leOfHom f.unop).trans (le_refl (Opposite.unop X)))) :
              Over (Opposite.unop X)) ⟶ Over.mk (homOfLE (le_refl (Opposite.unop X))))))
        (cast (el_obj_eq_classify_obj
          (τ := CartesianMonoidalCategory.lift τ1 τ2 ≫ MonoidalClosed.uncurry' U_arr)
          (le_refl (Opposite.unop X))).symm t)
      simp only [comp_apply', eqToHom_apply_eq_cast] at happ ⊢
      refine eq_of_heq (hL.trans ?_)
      refine ((heq_of_eq happ).trans (cast_heq _ _)).trans ?_
      refine HEq.trans ?_ (cast_heq _ _).symm
      refine famArr_shrink_heq (leOfHom f.unop) _ _ ?_
      exact ((cast_heq _ _).trans (cast_heq _ _)).trans (cast_heq _ _).symm

end constructors

end
