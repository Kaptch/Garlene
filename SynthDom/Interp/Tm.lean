module

public import SynthDom.Syntax.Expr.Core
public import SynthDom.Interp.Base

@[expose] public section

section ctx
  open CategoryTheory
  open Opposite
  open Functor
  open CartesianMonoidalCategory
  open MonoidalCategory
  open Logic

  attribute [local implicit_reducible] Functor.iter List.drop List.take

  def n_force : earlier.iter i ⟶ 𝟭 (ℐ.{u}) :=
    match i with
    | .zero => 𝟙 _
    | .succ i' => NatTrans.hcomp (n_force (i := i')) force

  def nm_force_cut (H : i ≤ j) : earlier.iter j ⟶ earlier.iter i :=
    match j with
    | .zero =>
      match i with
      | .zero => 𝟙 _
      | .succ i' => by exfalso; simp at H
    | .succ j' =>
      match i with
      | .zero => n_force
      | .succ i' => NatTrans.hcomp (nm_force_cut (Nat.succ_le_succ_iff.mp H)) (𝟙 _)

  def n_force_cut (H : 0 < i) : earlier.iter i ⟶ earlier :=
    match i with
    | .zero => by exfalso; simp at H
    | .succ i' => NatTrans.hcomp (n_force (i := i')) (𝟙 _)

  lemma nm_force_cut_id (H : i ≤ i) : nm_force_cut H = 𝟙 _ := by
    induction i with
    | zero =>
      simp [nm_force_cut]
    | succ i IHi =>
      simp [nm_force_cut]
      rw [IHi (Nat.succ_le_succ_iff.mp H)]
      simp

  lemma nm_force_zero (H : 0 ≤ i) : nm_force_cut H = n_force := by
    induction i <;> simp [nm_force_cut, n_force]

  lemma nm_force_cut_one (i : Nat) : nm_force_cut (Nat.le_succ i) = NatTrans.hcomp (F := earlier.iter i) (H := earlier) (G := earlier.iter i) (I := 𝟭 ℐ) (𝟙 _) (force) := by
    induction i with
    | zero =>
      simp [nm_force_cut, n_force]
    | succ i IH =>
      simp [nm_force_cut]
      rw [IH]
      rfl

  lemma nm_force_cut_decomp (H : i ≤ j)
    : n_force (i := j) = nm_force_cut H ≫ n_force (i := i) := by
    induction j generalizing i with
    | zero =>
      simp at H
      subst H
      simp [nm_force_cut]
    | succ j IHj =>
      simp [n_force]
      induction i with
      | zero =>
        simp [n_force, nm_force_cut]
      | succ i IHi =>
        simp only [n_force, nm_force_cut]
        rw [IHj (Nat.succ_le_succ_iff.mp H)]
        erw [← NatTrans.exchange]
        simp [Category.id_comp]

  lemma n_force_cut_nm (H1 : 0 < i) (H2 : 0 < j) (H3 : i ≤ j) :
    n_force_cut H2 = nm_force_cut H3 ≫ n_force_cut H1 := by
    induction j generalizing i with
    | zero =>
      simp at H2
    | succ j IHj =>
      cases i with
      | zero =>
        simp at H1
      | succ i =>
        simp only [n_force_cut, nm_force_cut]
        erw [← NatTrans.exchange]
        simp only [Category.comp_id]
        congr 1
        exact nm_force_cut_decomp (Nat.succ_le_succ_iff.mp H3)

  lemma nm_force_cut_trans {i j k : Nat} (H1 : i ≤ j) (H2 : j ≤ k) :
    nm_force_cut H2 ≫ nm_force_cut H1 = nm_force_cut (le_trans H1 H2) := by
    induction k generalizing j i with
    | zero =>
      simp at H2
      subst H2
      simp at H1
      subst H1
      simp [nm_force_cut]
    | succ k IHk =>
      cases j with
      | zero =>
        simp at H1
        subst H1
        rfl
      | succ j' =>
        cases i with
        | zero =>
          rw [nm_force_zero]
          erw [←nm_force_cut_decomp]
          symm
          apply nm_force_zero
        | succ i' =>
          simp only [nm_force_cut]
          erw [← NatTrans.exchange]
          simp only [Category.comp_id]
          congr 1
          exact IHk (Nat.succ_le_succ_iff.mp H1) (Nat.succ_le_succ_iff.mp H2)

  lemma n_force_cut_nm_force_cut {i : Nat} (Hn : 0 < i) :
    n_force_cut Hn = nm_force_cut (i := 1) (j := i) (by grind only) := by
    induction i with
    | zero => exfalso; simp at Hn
    | succ i IH =>
      by_cases h : 0 = i
      . cases h
        simp [n_force_cut, nm_force_cut, n_force]
      . have Hn' : 0 < i := by grind only
        rw [n_force_cut_nm Hn' Hn (by grind only)]
        rw [IH Hn']
        erw [nm_force_cut_trans]

  lemma n_force_comm {i j : Nat}
    : n_force (i := i + j) = (eqToHom (iter_add_comm _ i j)) ≫ n_force (i := j + i) := by
    generalize_proofs p
    revert p
    set t1 := i + j
    set t2 := j + i
    have heq : t1 = t2 := by subst t1; subst t2; rw [Nat.add_comm]
    clear_value t1 t2
    cases heq
    intro p; cases p
    simp

  lemma nm_force_cut_comm {i j k : Nat} (H1 : k ≤ i + j) (H2 : k ≤ j + i)
    : nm_force_cut (i := k) (j := i + j) H1 = (eqToHom (iter_add_comm _ i j)) ≫ nm_force_cut (i := k) (j := j + i) H2 := by
    generalize_proofs p
    revert p H1 H2
    set t1 := i + j
    set t2 := j + i
    have heq : t1 = t2 := by subst t1; subst t2; rw [Nat.add_comm]
    clear_value t1 t2
    cases heq
    intro H1 H2 p; cases p
    simp

  lemma n_force_assoc {i j k : Nat}
    : n_force (i := i + (j + k)) = (eqToHom (iter_add_assoc _ i j k)) ≫ n_force (i := i + j + k) := by
    generalize_proofs p
    revert p
    set t1 := i + (j + k)
    set t2 := i + j + k
    have heq : t1 = t2 := by subst t1; subst t2; omega
    clear_value t1 t2
    cases heq
    intro p; cases p
    simp

  lemma nm_force_cut_assoc {i j k m : Nat} (H1 : i ≤ j + (k + m)) (H2 : i ≤ j + k + m)
    : nm_force_cut (i := i) (j := j + (k + m)) H1 = (eqToHom (iter_add_assoc _ j k m)) ≫ nm_force_cut (i := i) (j := j + k + m) H2 := by
    induction m generalizing i with
    | zero =>
      simp
    | succ m IH =>
      simp
      cases i with
      | zero =>
        rw [nm_force_zero, nm_force_zero]
        apply n_force_assoc
      | succ i =>
        simp [nm_force_cut]
        specialize (@IH i (by grind only) (by grind only))
        rw [IH]
        rw [CategoryTheory.Functor.whiskerRight_comp]
        congr 1
        clear IH H1 H2 i
        rw [←hcomp_id]
        generalize_proofs p1 p2
        rw [eqToHom_hcomp _ _ _ p1]

  lemma force_push.{u} (a : ℐ.{u}) :
      force.app (earlier.obj a) = earlier.map (force.app a) := by
    ext ⟨n⟩
    simp [force, force_app, earlier, earlier_obj, earlier_arr]

  lemma map_eqToHom_conj.{u} (G : ℐ.{u} ⥤ ℐ.{u}) {X Y X' Y' : ℐ.{u}} (f : X ⟶ Y)
      (h₁ : X' = X) (h₂ : Y = Y') :
      G.map (eqToHom h₁ ≫ f ≫ eqToHom h₂)
      = eqToHom (congrArg G.obj h₁) ≫ G.map f ≫ eqToHom (congrArg G.obj h₂) := by
    cases h₁; cases h₂; simp

  lemma force_app_conj.{u} {W V : ℐ.{u}} (h : W = earlier.obj V) :
      force.app W = eqToHom (congrArg earlier.obj h) ≫ earlier.map (force.app V) ≫ eqToHom h.symm := by
    subst h; simp [force_push]

  lemma eqToHom_conj_merge.{u} {X₀ X₁ X₂ Y₀ Y₁ Y₂ : ℐ.{u}} (f : X₂ ⟶ Y₀)
      (h₁ : X₀ = X₁) (h₂ : X₁ = X₂) (h₃ : Y₀ = Y₁) (h₄ : Y₁ = Y₂)
      (h₁₂ : X₀ = X₂) (h₃₄ : Y₀ = Y₂) :
      eqToHom h₁ ≫ (eqToHom h₂ ≫ f ≫ eqToHom h₃) ≫ eqToHom h₄
      = eqToHom h₁₂ ≫ f ≫ eqToHom h₃₄ := by
    cases h₁; cases h₂; cases h₃; cases h₄; simp

  lemma nm_force_cut_push.{u} {i j : Nat} (Hn : i ≤ j) (a : ℐ.{u})
    (heq : earlier ⋙ earlier.iter j = earlier.iter j ⋙ earlier)
    (heq' : earlier.iter i ⋙ earlier = earlier ⋙ earlier.iter i)
    : (nm_force_cut Hn).app (earlier.obj a)
    = eqToHom (congr_obj heq a)
      ≫ earlier.map ((nm_force_cut Hn).app a)
      ≫ eqToHom (congr_obj heq' a) := by
    induction j generalizing i a with
    | zero =>
      simp at Hn
      subst Hn
      rfl
    | succ j IHj =>
      have hj : earlier ⋙ earlier.iter j = earlier.iter j ⋙ earlier := by
        rw [iter_iter', iter'_comm]
      cases i with
      | zero =>
        have IH := IHj (Nat.zero_le j) a hj (by rw [iter_iter', iter'_comm])
        rw [nm_force_zero] at IH
        have hobj : (earlier.iter j).obj (earlier.obj a) = earlier.obj ((earlier.iter j).obj a) :=
          congr_obj hj a
        have hOut : earlier.obj ((earlier.iter j).obj (earlier.obj a))
            = earlier.obj (earlier.obj ((earlier.iter j).obj a)) := congrArg earlier.obj hobj
        calc force_app ((earlier.iter j).obj (earlier.obj a)) ≫ (n_force (i := j)).app (earlier.obj a)
            = force_app ((earlier.iter j).obj (earlier.obj a))
                ≫ eqToHom hobj ≫ earlier.map ((n_force (i := j)).app a) := whisker_eq _ IH
          _ = (force_app ((earlier.iter j).obj (earlier.obj a)) ≫ eqToHom hobj)
                ≫ earlier.map ((n_force (i := j)).app a) := (Category.assoc _ _ _).symm
          _ = (eqToHom hOut ≫ earlier.map (force_app ((earlier.iter j).obj a)))
                ≫ earlier.map ((n_force (i := j)).app a) := by
                apply congrArg (· ≫ earlier.map ((n_force (i := j)).app a))
                calc force_app ((earlier.iter j).obj (earlier.obj a)) ≫ eqToHom hobj
                    = (eqToHom hOut ≫ earlier.map (force_app ((earlier.iter j).obj a))
                        ≫ eqToHom hobj.symm) ≫ eqToHom hobj :=
                      congrArg (· ≫ eqToHom hobj) (force_app_conj hobj)
                  _ = eqToHom hOut ≫ earlier.map (force_app ((earlier.iter j).obj a)) := by
                      simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
          _ = eqToHom hOut ≫ earlier.map (force_app ((earlier.iter j).obj a))
                ≫ earlier.map ((n_force (i := j)).app a) := Category.assoc _ _ _
          _ = eqToHom hOut
                ≫ earlier.map (force_app ((earlier.iter j).obj a) ≫ (n_force (i := j)).app a) :=
              whisker_eq _ (earlier.map_comp _ _).symm
      | succ i =>
        exact (congrArg (fun t => earlier.map t)
          (IHj (Nat.succ_le_succ_iff.mp Hn) a hj (by rw [iter_iter', iter'_comm]))).trans
          (map_eqToHom_conj earlier _ _ _)

  lemma nm_force_cut_natural.{u} {i j k : Nat} (Hn : i ≤ j) (a : ℐ.{u})
  (heq : earlier.iter k ⋙ earlier.iter j = earlier.iter j ⋙ earlier.iter k)
  (heq' : earlier.iter i ⋙ earlier.iter k = earlier.iter k ⋙ earlier.iter i)
  : (nm_force_cut Hn).app ((earlier.iter k).obj a)
    = eqToHom (congr_obj heq a)
      ≫ (earlier.iter k).map ((nm_force_cut Hn).app a)
      ≫ eqToHom (congr_obj heq' a) := by
    induction k generalizing i j with
    | zero =>
      rfl
    | succ k IHk =>
      have hpush : earlier ⋙ earlier.iter j = earlier.iter j ⋙ earlier := by
        rw [iter_iter', iter'_comm]
      have hpush' : earlier.iter i ⋙ earlier = earlier ⋙ earlier.iter i := by
        rw [iter_iter', iter'_comm]
      have hk : earlier.iter k ⋙ earlier.iter j = earlier.iter j ⋙ earlier.iter k := by
        rw [← iter_add, ← iter_add, Nat.add_comm]
      have hk' : earlier.iter i ⋙ earlier.iter k = earlier.iter k ⋙ earlier.iter i := by
        rw [← iter_add, ← iter_add, Nat.add_comm]
      show (nm_force_cut Hn).app (earlier.obj ((earlier.iter k).obj a)) = _
      rw [nm_force_cut_push Hn ((earlier.iter k).obj a) hpush hpush']
      rw [IHk Hn hk hk']
      exact (congrArg
          (fun t => eqToHom (congr_obj hpush ((earlier.iter k).obj a))
            ≫ t ≫ eqToHom (congr_obj hpush' ((earlier.iter k).obj a)))
          (map_eqToHom_conj earlier ((earlier.iter k).map ((nm_force_cut Hn).app a))
            (congr_obj hk a) (congr_obj hk' a))).trans
        (eqToHom_conj_merge _ _ _ _ _ _ _)

  def n_earlier_terminal.{u} {i : Nat} : (earlier.iter i).obj (𝟙_ (ℐ.{u})) ≅ 𝟙_ (ℐ.{u}) :=
    match i with
    | .zero => Iso.refl _
    | .succ i' => earlier.mapIso (n_earlier_terminal (i := i')) ≪≫ earlier_terminal

  def n_earlier_split : prodFunctor.obj (earlier.iter i, 𝟭 ℐ) ⋙ tensor ℐ
    ≅ prodFunctor.obj (𝟭 ℐ, later.iter' i) ⋙ tensor ℐ ⋙ earlier.iter i :=
  match i with
  | .zero => Iso.refl _
  | .succ i' => NatIso.ofComponents
    (app := fun X => (earlier_split.app ⟨(earlier.iter i').obj X.1, X.2⟩) ≪≫ earlier.mapIso ((n_earlier_split (i := i')).app ⟨X.1, (later.obj X.2)⟩))
    (by
      intros X Y f
      calc (prodFunctor.obj (earlier, 𝟭 ℐ) ⋙ tensor ℐ).map
            (⟨(earlier.iter i').map f.1, f.2⟩ :
              (((earlier.iter i').obj X.1, X.2) : ℐ × ℐ) ⟶ ((earlier.iter i').obj Y.1, Y.2))
          ≫ (earlier_split.hom.app ⟨(earlier.iter i').obj Y.1, Y.2⟩
              ≫ earlier.map ((n_earlier_split (i := i')).hom.app ⟨Y.1, later.obj Y.2⟩))
          = ((prodFunctor.obj (earlier, 𝟭 ℐ) ⋙ tensor ℐ).map
              (⟨(earlier.iter i').map f.1, f.2⟩ :
                (((earlier.iter i').obj X.1, X.2) : ℐ × ℐ) ⟶ ((earlier.iter i').obj Y.1, Y.2))
              ≫ earlier_split.hom.app ⟨(earlier.iter i').obj Y.1, Y.2⟩)
              ≫ earlier.map ((n_earlier_split (i := i')).hom.app ⟨Y.1, later.obj Y.2⟩) :=
          (Category.assoc _ _ _).symm
        _ = (earlier_split.hom.app ⟨(earlier.iter i').obj X.1, X.2⟩
              ≫ (prodFunctor.obj (𝟭 ℐ, later) ⋙ tensor ℐ ⋙ earlier).map
                (⟨(earlier.iter i').map f.1, f.2⟩ :
                  (((earlier.iter i').obj X.1, X.2) : ℐ × ℐ) ⟶ ((earlier.iter i').obj Y.1, Y.2)))
              ≫ earlier.map ((n_earlier_split (i := i')).hom.app ⟨Y.1, later.obj Y.2⟩) :=
          congrArg (· ≫ earlier.map ((n_earlier_split (i := i')).hom.app ⟨Y.1, later.obj Y.2⟩))
            (earlier_split.hom.naturality _)
        _ = earlier_split.hom.app ⟨(earlier.iter i').obj X.1, X.2⟩
              ≫ (earlier.map ((prodFunctor.obj (earlier.iter i', 𝟭 ℐ) ⋙ tensor ℐ).map
                  (⟨f.1, later.map f.2⟩ :
                    ((X.1, later.obj X.2) : ℐ × ℐ) ⟶ (Y.1, later.obj Y.2)))
                ≫ earlier.map ((n_earlier_split (i := i')).hom.app ⟨Y.1, later.obj Y.2⟩)) :=
          Category.assoc _ _ _
        _ = earlier_split.hom.app ⟨(earlier.iter i').obj X.1, X.2⟩
              ≫ earlier.map ((prodFunctor.obj (earlier.iter i', 𝟭 ℐ) ⋙ tensor ℐ).map
                  (⟨f.1, later.map f.2⟩ :
                    ((X.1, later.obj X.2) : ℐ × ℐ) ⟶ (Y.1, later.obj Y.2))
                ≫ (n_earlier_split (i := i')).hom.app ⟨Y.1, later.obj Y.2⟩) :=
          whisker_eq _ (earlier.map_comp _ _).symm
        _ = earlier_split.hom.app ⟨(earlier.iter i').obj X.1, X.2⟩
              ≫ earlier.map ((n_earlier_split (i := i')).hom.app ⟨X.1, later.obj X.2⟩
                ≫ (prodFunctor.obj (𝟭 ℐ, later.iter' i') ⋙ tensor ℐ ⋙ earlier.iter i').map
                  (⟨f.1, later.map f.2⟩ :
                    ((X.1, later.obj X.2) : ℐ × ℐ) ⟶ (Y.1, later.obj Y.2))) :=
          whisker_eq _ (congrArg earlier.map ((n_earlier_split (i := i')).hom.naturality _))
        _ = earlier_split.hom.app ⟨(earlier.iter i').obj X.1, X.2⟩
              ≫ (earlier.map ((n_earlier_split (i := i')).hom.app ⟨X.1, later.obj X.2⟩)
                ≫ earlier.map ((prodFunctor.obj (𝟭 ℐ, later.iter' i') ⋙ tensor ℐ ⋙ earlier.iter i').map
                  (⟨f.1, later.map f.2⟩ :
                    ((X.1, later.obj X.2) : ℐ × ℐ) ⟶ (Y.1, later.obj Y.2)))) :=
          whisker_eq _ (earlier.map_comp _ _)
        _ = (earlier_split.hom.app ⟨(earlier.iter i').obj X.1, X.2⟩
              ≫ earlier.map ((n_earlier_split (i := i')).hom.app ⟨X.1, later.obj X.2⟩))
              ≫ earlier.map ((prodFunctor.obj (𝟭 ℐ, later.iter' i') ⋙ tensor ℐ ⋙ earlier.iter i').map
                  (⟨f.1, later.map f.2⟩ :
                    ((X.1, later.obj X.2) : ℐ × ℐ) ⟶ (Y.1, later.obj Y.2))) :=
          (Category.assoc _ _ _).symm)

  def interp_ctx_split.{i} (Γ : CTX.{i}) : ⟦Γ⟧ₛ ≅ (earlier.iter i).obj ⟦(Γ.drop i)⟧ₛ ⊗ ⟦(Γ.take i)⟧ₛ :=
    match Γ with
    | .nil =>
      match i with
      | .zero => Iso.symm $ ρ_ _
      | .succ i' => Iso.symm $ (ρ_ (earlier.obj $ (earlier.iter i').obj (𝟙_ ℐ)))
          ≪≫ earlier.mapIso n_earlier_terminal
    | .cons x xs =>
      match i with
      | .zero => Iso.symm $ ρ_ _
      | .succ i' => (whiskerLeftIso ⟦x⟧ₒ $ (earlier.mapIso $ interp_ctx_split (Γ := xs) (i := i')) ≪≫ earlier_prod.app ⟨((earlier.iter i').obj ⟦List.drop i' xs⟧ₛ), ⟦List.take i' xs⟧ₛ⟩)
          ≪≫ (Iso.symm (α_ _ _ _))
          ≪≫ whiskerRightIso (β_ _ _) (earlier.obj ⟦List.take i' xs⟧ₛ)
          ≪≫ (α_ _ _ _)

  @[simp]
  lemma interp_ctx_split_zero (Γ : CTX.{i}) :
    interp_ctx_split Γ (i := 0) = Iso.symm (ρ_ _) := by
    cases Γ <;> rfl

  @[simp]
  lemma interp_ctx_split_nil (i : Nat) :
    interp_ctx_split [] (i := i) = Iso.symm (ρ_ _)
      ≪≫ (MonoidalCategory.tensorIso
        (Iso.symm (eqToIso (congr_arg ((earlier.iter i).obj) (by simp; rfl)) ≪≫ n_earlier_terminal (i := i)))
        (eqToIso (by simp; rfl))) := by
    cases i <;> rfl

  lemma interp_ctx_split_swap (Γ : CTX.{i}) (i j : Nat)
    : (interp_ctx_split Γ (i := j + i)).hom
    = (interp_ctx_split Γ (i := i + j)).hom
    ≫ (whiskerRight (eqToHom (congr_obj (iter_add_comm earlier i j) _)) _)
    ≫ ((earlier.iter (j + i)).map (eqToHom (by rw [Nat.add_comm])) ⊗ₘ (eqToHom (by rw [Nat.add_comm]))) := by
    generalize_proofs p1 p2 p3
    revert p1 p2 p3
    set k := i + j
    have heq : k = j + i := Nat.add_comm i j
    clear_value k
    cases heq
    intro p1 p2 p3
    cases p3; cases p2; cases p1
    simp

  lemma cart_tail_chase {C : Type*} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]
      (W X Y : C) :
      (α_ W X Y).inv ≫ (β_ W X).hom ▷ Y ≫ (α_ X W Y).hom ≫ fst X (W ⊗ Y)
      = snd W (X ⊗ Y) ≫ fst X Y := by
    simp only [associator_hom_fst]
    rw [whiskerRight_fst_assoc, braiding_hom_fst, associator_inv_fst_snd]

  lemma cart_tail_chase_assoc {C : Type*} [Category C] [CartesianMonoidalCategory C]
      [BraidedCategory C] {Z : C} (W X Y : C) (g : X ⟶ Z) :
      (α_ W X Y).inv ≫ (β_ W X).hom ▷ Y ≫ (α_ X W Y).hom ≫ fst X (W ⊗ Y) ≫ g
      = snd W (X ⊗ Y) ≫ fst X Y ≫ g := by
    simp only [associator_hom_fst_assoc]
    rw [whiskerRight_fst_assoc, braiding_hom_fst_assoc, associator_inv_fst_snd_assoc]

  lemma snd_push_gen {D A B : ℐ} {W : ℐ} (φ : D ⟶ A ⊗ B) (X : ℐ)
      (g : earlier.obj A ⊗ earlier.obj B ⟶ W) :
      X ◁ earlier.map φ ≫ X ◁ earlier_prod.hom.app (A, B)
        ≫ snd X (earlier.obj A ⊗ earlier.obj B) ≫ g
      = snd X (earlier.obj D) ≫ earlier.map φ ≫ earlier_prod.hom.app (A, B) ≫ g := by
    rw [← Category.assoc (X ◁ earlier.map φ),
        ← MonoidalCategory.whiskerLeft_comp, ← Category.assoc,
        show X ◁ (earlier.map φ ≫ earlier_prod.hom.app (A, B))
              ≫ snd X (earlier.obj A ⊗ earlier.obj B)
            = snd X (earlier.obj D) ≫ (earlier.map φ ≫ earlier_prod.hom.app (A, B))
          from whiskerLeft_snd X _]
    exact Category.assoc _ _ _

  lemma prod_fst_earlier (A B : ℐ) :
      earlier_prod.hom.app (A, B) ≫ fst (earlier.obj A) (earlier.obj B) = earlier.map (fst A B) :=
    rfl

  lemma prod_fst_earlier_assoc {W : ℐ} (A B : ℐ) (g : earlier.obj A ⟶ W) :
      earlier_prod.hom.app (A, B) ≫ fst (earlier.obj A) (earlier.obj B) ≫ g
      = earlier.map (fst A B) ≫ g :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ g) (prod_fst_earlier A B))

  lemma snd_force_chase {D A B W : ℐ} (X : ℐ) (φ : D ⟶ A ⊗ B) (g : A ⟶ W) :
      (X ◁ earlier.map φ ≫ X ◁ earlier_prod.hom.app (A, B))
          ≫ (α_ X (earlier.obj A) (earlier.obj B)).inv
          ≫ (β_ X (earlier.obj A)).hom ▷ earlier.obj B
          ≫ (α_ (earlier.obj A) X (earlier.obj B)).hom
          ≫ fst (earlier.obj A) (X ⊗ earlier.obj B)
          ≫ force.app A ≫ g
        = snd X (earlier.obj D) ≫ force.app D ≫ φ ≫ fst A B ≫ g := by
    have hnat := force.naturality (φ ≫ fst A B)
    dsimp only [Functor.id_obj, Functor.id_map] at hnat
    calc (X ◁ earlier.map φ ≫ X ◁ earlier_prod.hom.app (A, B))
            ≫ (α_ X (earlier.obj A) (earlier.obj B)).inv
            ≫ (β_ X (earlier.obj A)).hom ▷ earlier.obj B
            ≫ (α_ (earlier.obj A) X (earlier.obj B)).hom
            ≫ fst (earlier.obj A) (X ⊗ earlier.obj B)
            ≫ force.app A ≫ g
        = (X ◁ earlier.map φ ≫ X ◁ earlier_prod.hom.app (A, B))
            ≫ snd X (earlier.obj A ⊗ earlier.obj B)
            ≫ fst (earlier.obj A) (earlier.obj B) ≫ force.app A ≫ g :=
          whisker_eq _ (cart_tail_chase_assoc X (earlier.obj A) (earlier.obj B) (force.app A ≫ g))
      _ = snd X (earlier.obj D) ≫ earlier.map φ ≫ earlier_prod.hom.app (A, B)
            ≫ fst (earlier.obj A) (earlier.obj B) ≫ force.app A ≫ g :=
          snd_push_gen φ X (fst (earlier.obj A) (earlier.obj B) ≫ force.app A ≫ g)
      _ = snd X (earlier.obj D) ≫ earlier.map φ ≫ earlier.map (fst A B) ≫ force.app A ≫ g :=
          whisker_eq _ (whisker_eq _ (prod_fst_earlier_assoc A B (force.app A ≫ g)))
      _ = snd X (earlier.obj D) ≫ earlier.map (φ ≫ fst A B) ≫ force.app A ≫ g :=
          whisker_eq _ (congrArg (· ≫ force.app A ≫ g) (earlier.map_comp φ (fst A B)).symm)
      _ = snd X (earlier.obj D) ≫ force.app D ≫ φ ≫ fst A B ≫ g :=
          whisker_eq _ (congrArg (· ≫ g) hnat)

  lemma interp_ctx_split_add (Γ Δ : CTX.{i}) (p : Nat)
    (Heq : (earlier.iter (List.length Γ)).obj ((earlier.iter p).obj ⟦List.drop p (List.drop (List.length Γ) (Γ ++ Δ))⟧ₛ)
      = (earlier.iter (List.length Γ + p)).obj ⟦List.drop (List.length Γ + p) (Γ ++ Δ)⟧ₛ)
    : (interp_ctx_split (Γ ++ Δ) (i := Γ.length + p)).hom ≫ fst _ _
      = (interp_ctx_split (Γ ++ Δ) (i := Γ.length)).hom
        ≫ fst _ _
        ≫ (earlier.iter (List.length Γ)).map ((interp_ctx_split _ (i := p)).hom ≫ fst _ _)
        ≫ eqToHom Heq := by
    rw [interp_ctx_split_swap]
    generalize_proofs p1 p2 p3
    revert p1 p2 p3 Heq
    set k := List.length Γ + p
    have heq : k = p + List.length Γ := Nat.add_comm _ _
    clear_value k
    cases heq
    set k' := p + List.length Γ
    have heq' : k' = p + List.length Γ := by subst k'; rfl
    induction Γ with
    | nil =>
      subst k'
      cases heq'
      simp [interp_ctx] at *
      change ((interp_ctx_split Δ).hom ≫ fst ((earlier.iter p).obj ⟦List.drop p Δ⟧ₛ) ⟦List.take p Δ⟧ₛ =
        (ρ_ ⟦Δ⟧ₛ).inv ≫ fst ⟦Δ⟧ₛ (𝟙_ ℐ) ≫ (interp_ctx_split Δ).hom
          ≫ fst ((earlier.iter p).obj ⟦List.drop p Δ⟧ₛ) ⟦List.take p Δ⟧ₛ)
      simp
    | cons x xs IH =>
      have heq : k' = (p + xs.length) + 1 := by subst k'; simp; rw [Nat.add_assoc]
      clear_value k'
      cases heq
      simp
      intro Heq
      simp [interp_ctx, interp_ctx_split]
      set AL := (earlier.iter (p + xs.length)).obj ⟦List.drop (p + xs.length) (xs ++ Δ)⟧ₛ with hAL
      set BL := (⟦List.take (p + xs.length) (xs ++ Δ)⟧ₛ : ℐ) with hBL
      set AR := (earlier.iter xs.length).obj ⟦List.drop xs.length (xs ++ Δ)⟧ₛ with hAR
      set BR := (⟦List.take xs.length (xs ++ Δ)⟧ₛ : ℐ) with hBR
      have hEnd : earlier.obj ((earlier.iter xs.length).obj
              ((earlier.iter p).obj ⟦List.drop p (List.drop xs.length (xs ++ Δ))⟧ₛ)) = earlier.obj AL := by
        rw [hAL]; congr 1; rw [iter_add]; simp; congr 2
        rw [Nat.add_comm, ← List.drop_drop]; simp
      show ⟦x⟧ₒ ◁ earlier.map (interp_ctx_split (xs ++ Δ)).hom
            ≫ ⟦x⟧ₒ ◁ earlier_prod.hom.app (AL, BL)
            ≫ (α_ ⟦x⟧ₒ (earlier.obj AL) (earlier.obj BL)).inv
            ≫ (β_ ⟦x⟧ₒ (earlier.obj AL)).hom ▷ earlier.obj BL
            ≫ (α_ (earlier.obj AL) ⟦x⟧ₒ (earlier.obj BL)).hom
            ≫ fst (earlier.obj AL) (⟦x⟧ₒ ⊗ earlier.obj BL)
            ≫ 𝟙 (earlier.obj AL)
          = ⟦x⟧ₒ ◁ earlier.map (interp_ctx_split (xs ++ Δ)).hom
            ≫ ⟦x⟧ₒ ◁ earlier_prod.hom.app (AR, BR)
            ≫ (α_ ⟦x⟧ₒ (earlier.obj AR) (earlier.obj BR)).inv
            ≫ (β_ ⟦x⟧ₒ (earlier.obj AR)).hom ▷ earlier.obj BR
            ≫ (α_ (earlier.obj AR) ⟦x⟧ₒ (earlier.obj BR)).hom
            ≫ fst (earlier.obj AR) (⟦x⟧ₒ ⊗ earlier.obj BR)
            ≫ (earlier.map ((earlier.iter xs.length).map (interp_ctx_split (List.drop xs.length (xs ++ Δ))).hom)
                ≫ earlier.map ((earlier.iter xs.length).map
                    (fst ((earlier.iter p).obj ⟦List.drop p (List.drop xs.length (xs ++ Δ))⟧ₛ)
                      ⟦List.take p (List.drop xs.length (xs ++ Δ))⟧ₛ)))
              ≫ eqToHom hEnd
      simp only [Category.comp_id, Category.assoc]
      have eqL := congrArg ((⟦x⟧ₒ ◁ earlier.map (interp_ctx_split (xs ++ Δ)).hom
          ≫ ⟦x⟧ₒ ◁ earlier_prod.hom.app (AL, BL)) ≫ ·)
          (cart_tail_chase ⟦x⟧ₒ (earlier.obj AL) (earlier.obj BL))
      have eqR := congrArg ((⟦x⟧ₒ ◁ earlier.map (interp_ctx_split (xs ++ Δ)).hom
          ≫ ⟦x⟧ₒ ◁ earlier_prod.hom.app (AR, BR)) ≫ ·)
          (cart_tail_chase_assoc ⟦x⟧ₒ (earlier.obj AR) (earlier.obj BR)
            (earlier.map ((earlier.iter xs.length).map (interp_ctx_split (List.drop xs.length (xs ++ Δ))).hom)
              ≫ earlier.map ((earlier.iter xs.length).map
                  (fst ((earlier.iter p).obj ⟦List.drop p (List.drop xs.length (xs ++ Δ))⟧ₛ)
                    ⟦List.take p (List.drop xs.length (xs ++ Δ))⟧ₛ))
              ≫ eqToHom hEnd))
      simp only [Category.assoc] at eqL eqR
      refine eqL.trans (Eq.trans ?_ eqR.symm)
      have heqIH : (earlier.iter xs.length).obj ((earlier.iter p).obj ⟦List.drop p (List.drop xs.length (xs ++ Δ))⟧ₛ)
        = (earlier.iter (p + xs.length)).obj ⟦List.drop (p + xs.length) (xs ++ Δ)⟧ₛ := by
        rw [iter_add]; simp; rw [Nat.add_comm]; simp
      have IH' := (IH (Eq.refl _) heqIH (Eq.refl _) (Eq.refl _))
      simp only [] at IH'
      refine (snd_push_gen (interp_ctx_split (xs ++ Δ) (i := p + xs.length)).hom ⟦x⟧ₒ
          (fst (earlier.obj AL) (earlier.obj BL))).trans (Eq.trans ?_
        (snd_push_gen (interp_ctx_split (xs ++ Δ) (i := xs.length)).hom ⟦x⟧ₒ
          (fst (earlier.obj AR) (earlier.obj BR)
            ≫ earlier.map ((earlier.iter xs.length).map (interp_ctx_split (List.drop xs.length (xs ++ Δ))).hom)
            ≫ earlier.map ((earlier.iter xs.length).map
                (fst ((earlier.iter p).obj ⟦List.drop p (List.drop xs.length (xs ++ Δ))⟧ₛ)
                  ⟦List.take p (List.drop xs.length (xs ++ Δ))⟧ₛ))
            ≫ eqToHom hEnd)).symm)
      erw [prod_fst_earlier, prod_fst_earlier_assoc]
      congr 1
      rw [show eqToHom hEnd = earlier.map (eqToHom heqIH) from by rw [eqToHom_map]]
      rw [← earlier.map_comp, ← earlier.map_comp, ← earlier.map_comp, ← earlier.map_comp,
          ← earlier.map_comp]
      congr 1
      simpa using (IH' trivial)
  lemma interp_ctx_split_add' (Γ Δ : CTX.{i}) (p q : Nat) (Hle : q ≤ (List.length Γ + p)) (Hle' : q ≤ p)
    : (interp_ctx_split (Γ ++ Δ) (i := Γ.length + p)).hom ≫ fst _ _ ≫ (nm_force_cut Hle).app _
      = (interp_ctx_split (Γ ++ Δ) (i := Γ.length)).hom ≫ fst _ _ ≫ n_force.app _
        ≫ ((interp_ctx_split (List.drop (List.length Γ) (Γ ++ Δ)) (i := p)).hom ≫ fst _ _
          ≫ (nm_force_cut Hle').app _ ≫ (earlier.iter q).map (eqToHom (by simp))) := by
    rw [←Category.assoc]
    have heq : (earlier.iter (List.length Γ)).obj ((earlier.iter p).obj ⟦List.drop p (List.drop (List.length Γ) (Γ ++ Δ))⟧ₛ)
      = (earlier.iter (List.length Γ + p)).obj ⟦List.drop (List.length Γ + p) (Γ ++ Δ)⟧ₛ := by
      rw [iter_add_comm]
      rw [iter_add]
      simp
    rw [interp_ctx_split_add _ _ _ heq]
    simp
    congr 1
    generalize_proofs r
    have heq := (n_force (i := (List.length Γ))).naturality ((interp_ctx_split (List.drop (List.length Γ) (Γ ++ Δ))).hom ≫
          fst ((earlier.iter p).obj ⟦List.drop p (List.drop (List.length Γ) (Γ ++ Δ))⟧ₛ)
          ⟦List.take p (List.drop (List.length Γ) (Γ ++ Δ))⟧ₛ ≫
          (nm_force_cut Hle').app ⟦List.drop p (List.drop (List.length Γ) (Γ ++ Δ))⟧ₛ ≫ (earlier.iter q).map (eqToHom r))
    dsimp at heq
    rw [←heq]; clear heq
    rw [←Category.assoc]
    rw [←(earlier.iter (List.length Γ)).map_comp]
    symm
    rw [←Category.assoc]
    rw [(earlier.iter (List.length Γ)).map_comp]
    rw [Category.assoc]
    congr 1

    revert heq r Hle Hle'
    set k := List.length Γ + p
    have heq : k = p + List.length Γ := Nat.add_comm _ _
    clear_value k
    cases heq
    set k' := p + List.length Γ
    have heq' : k' = p + List.length Γ := by subst k'; rfl
    induction Γ with
    | nil =>
      subst k'
      simp [n_force] at *
      intro Hle
      change ((nm_force_cut Hle).app ⟦List.drop p Δ⟧ₛ = (nm_force_cut _).app ⟦List.drop p Δ⟧ₛ)
      rfl
    | cons x xs IH =>
      have heq : k' = (p + xs.length) + 1 := by subst k'; simp; rw [Nat.add_assoc]
      clear_value k'
      cases heq
      simp
      intro Hle Hle' Heq p1
      rw [show Hle = le_trans Hle' (le_trans (by simp) (Nat.le_succ _)) from rfl]
      rw [←nm_force_cut_trans Hle' (le_trans (by simp) (Nat.le_succ _))]
      have r1 : (earlier.iter xs.length).obj ((earlier.iter p).obj ⟦List.drop p (List.drop xs.length (xs ++ Δ))⟧ₛ)
        = (earlier.iter (p + xs.length)).obj ⟦List.drop (p + xs.length) (xs ++ Δ)⟧ₛ := by
        rw [iter_add]
        simp
        grind only
      have IH' := (IH (Eq.refl _) (by grind only) Hle' r1 (by simp; grind only))
      simp at IH'
      simp only [n_force, NatTrans.hcomp_app, Functor.id_map, Functor.id_obj]
      rw [← earlier.map_comp_assoc]
      rw [← (earlier.iter xs.length).map_comp]
      generalize hG : (nm_force_cut Hle').app _ ≫ (earlier.iter q).map _ = G
      have hnat := force.naturality ((earlier.iter xs.length).map G)
      dsimp only [Functor.id_obj, Functor.id_map] at hnat
      erw [reassoc_of% hnat]
      have hnforce := (n_force (i := xs.length)).naturality G
      dsimp only [Functor.id_obj, Functor.id_map] at hnforce
      rw [hnforce]
      rw [← hG]
      change (force.app _ ≫
        (n_force.app ((earlier.iter p).obj ⟦List.drop p (List.drop xs.length (xs ++ Δ))⟧ₛ) ≫
          (nm_force_cut Hle').app _ ≫ (earlier.iter q).map _) = _)
      rw [IH']
      rw [nm_force_cut_trans]
      rw [← nm_force_cut_trans (by omega : q ≤ p + xs.length) (Nat.le_succ (p + xs.length))]
      rw [nm_force_cut_one]
      simp only [NatTrans.comp_app, NatTrans.hcomp_app, Functor.id_map, Functor.id_obj, NatTrans.id_app]
      erw [Category.comp_id]
      clear hnforce hnat hG G IH' IH
      have heq := force.naturality (eqToHom r1)
      dsimp only [Functor.id_obj, Functor.id_map] at heq
      rw [← Category.assoc, ← heq]
      rw [eqToHom_map]
      rfl
  lemma interp_ctx_split_add'' (Γ Δ : CTX.{i}) (p : Nat) (Hle : p ≤ (List.length Γ + p))
    : (interp_ctx_split (Γ ++ Δ) (i := Γ.length + p)).hom ≫ fst _ _ ≫ (nm_force_cut Hle).app _
      = (interp_ctx_split (Γ ++ Δ) (i := Γ.length)).hom ≫ fst _ _ ≫ n_force.app _
        ≫ ((interp_ctx_split (List.drop (List.length Γ) (Γ ++ Δ)) (i := p)).hom ≫ fst _ _
          ≫ (earlier.iter p).map (eqToHom (by simp))) := by
    rw [interp_ctx_split_add' Γ Δ p p Hle (le_refl _)]
    rw [nm_force_cut_id]
    simp

  def succFunctor : ℕ ⥤ ℕ :=
    {
      obj n := Nat.succ n
      map {A B} f := (Nat.succ_le_succ f.le).hom
      map_id A := by rfl
      map_comp {A B C} f g := by rfl
    }

  instance : Full succFunctor where
    map_surjective f := ⟨(Nat.succ_le_succ_iff.mp f.le).hom, rfl⟩

  @[simp]
  def Presieve_succFunctor (S : Presieve X) :
    Presieve (succFunctor.obj X) := fun x f => (S (Nat.pred_le_of_le_succ f.le).hom) ∨ x = 0

  @[simp]
  def Sieve_succFunctor (S : Sieve X) :
    Sieve (succFunctor.obj X) := Sieve.mk (arrows := Presieve_succFunctor S) (by
      intro Y Z f prf g
      simp
      simp at prf
      cases prf with
      | inl prf' =>
        left
        apply S.downward_closed prf' (Nat.pred_le_pred g.le).hom
      | inr heq =>
        cases heq
        right
        rw [Nat.le_zero.mp g.le]
    )

  @[simp]
  def lift_subobject_classifier_app.{i} X : (later.obj.{i} Ω).obj X ⟶ (Ω).obj X :=
    match X with
    | op Nat.zero => ↾(fun _ ↦ ULift.up ⊤)
    | op (Nat.succ _) => ↾(fun y ↦ ULift.up (Sieve_succFunctor y.down))

  def lift_subobject_classifier.{i} : later.obj.{i} Ω ⟶ Ω :=
  {
    app X := lift_subobject_classifier_app X
    naturality {A B} f := by
      cases A with
      | op a => cases a with
        | zero =>
          cases B with
          | op b => cases b with
            | zero =>
              simp [later]
              ext x Y g; simp
            | succ b' =>
              exfalso
              apply Nat.not_succ_le_zero b'
              apply leOfHom f.unop
        | succ a' =>
          cases B with
          | op b => cases b with
            | zero =>
              simp [later]
              ext x Y g
              simp [Presieve_succFunctor, Sieve.pullback]
              exact Or.inr (Nat.le_zero.mp (leOfHom g))
            | succ b' =>
              simp [later]
              ext x y g
              change (x.down.arrows _ ∨ y = 0) ↔ (x.down.arrows _ ∨ y = 0)
              constructor <;> rintro (h | h)
              · left
                convert h using 1
                apply Subsingleton.elim
              · exact Or.inr h
              · left
                convert h using 1
                apply Subsingleton.elim
              · exact Or.inr h
  }

  def ctx_proj (Γ : CTX.{i}) (p : Nat) (Δ : OCTX.{i}) (Heq : Γ[p]? = some Δ) :
    ⟦Γ⟧ₛ ⟶ ⟦Δ⟧ₒ :=
    match p with
    | .zero =>
      match Γ with
      | .nil => by exfalso; simp at Heq
      | .cons Γ Γs => fst _ _ ≫ eqToHom (congr_arg interp_octx (by simp at Heq; exact Heq))
    | .succ p' =>
      match Γ with
      | .nil => by exfalso; simp at Heq
      | .cons Γ Γs => snd _ _ ≫ force.app _ ≫ ctx_proj Γs p' Δ Heq

  lemma ctx_proj_congr {Γ : CTX.{i}} {p q : Nat} {Δ : OCTX.{i}} (hpq : p = q)
      (Hp : Γ[p]? = some Δ) (Hq : Γ[q]? = some Δ) :
      ctx_proj Γ p Δ Hp = ctx_proj Γ q Δ Hq := by
    subst hpq
    rfl

  lemma ctx_proj_append (Γ : CTX.{i}) (off : Nat) (Δ : OCTX.{i}) (h : Γ[off]? = some Δ) :
      ∀ (Ψ : CTX.{i}) (H : (Ψ ++ Γ)[Ψ.length + off]? = some Δ)
        (e : ⟦List.drop Ψ.length (Ψ ++ Γ)⟧ₛ = ⟦Γ⟧ₛ),
      (interp_ctx_split (Ψ ++ Γ) (i := Ψ.length)).hom ≫ fst _ _ ≫ n_force.app _ ≫ eqToHom e
          ≫ ctx_proj Γ off Δ h
        = ctx_proj (Ψ ++ Γ) (Ψ.length + off) Δ H := by
    intro Ψ
    induction Ψ with
    | nil =>
      intro H e
      simp [n_force, interp_ctx]
      change ((ρ_ ⟦Γ⟧ₛ).inv ≫ fst ⟦Γ⟧ₛ (𝟙_ ℐ) ≫ ctx_proj Γ off Δ h = ctx_proj Γ off Δ _)
      simp
    | cons t ts IH =>
      intro H e
      have H' : (ts ++ Γ)[ts.length + off]? = some Δ := by
        simp only [List.cons_append, List.length_cons] at H
        rw [show ts.length + 1 + off = (ts.length + off) + 1 from by omega,
          List.getElem?_cons_succ] at H
        exact H
      have e' : ⟦List.drop ts.length (ts ++ Γ)⟧ₛ = ⟦Γ⟧ₛ := by simp
      rw [ctx_proj_congr (show (t :: ts).length + off = (ts.length + off) + 1 from by simp; omega)
        H (by simpa using H')]
      show _ = snd _ _ ≫ force.app _ ≫ ctx_proj (ts ++ Γ) (ts.length + off) Δ H'
      rw [← IH H' e']
      simp only [n_force]
      exact snd_force_chase ⟦t⟧ₒ (interp_ctx_split (ts ++ Γ)).hom
        (n_force.app ⟦List.drop ts.length (ts ++ Γ)⟧ₛ ≫ eqToHom e' ≫ ctx_proj Γ off Δ h)

  def ctx_proj' (Γ : CTX.{i}) (p : Nat) (Hlt : p < Γ.length) :
    ⟦Γ⟧ₛ ⟶ ⟦Γ[p]⟧ₒ :=
    match p with
    | .zero =>
      match Γ with
      | .nil => by exfalso; simp at Hlt
      | .cons Γ Γs => fst _ _ ≫ eqToHom (Eq.refl _)
    | .succ p' =>
      match Γ with
      | .nil => by exfalso; simp at Hlt
      | .cons Γ Γs => snd _ _ ≫ force.app _ ≫ ctx_proj' Γs p' (Nat.lt_of_succ_lt_succ Hlt)

  def octx_proj (Γ : OCTX.{i}) (p : Nat) (Δ : TYPE.{i}) (Heq : Γ[p]? = some Δ) :
    ⟦Γ⟧ₒ ⟶ ⟦Δ⟧ₜ :=
    match p with
    | .zero =>
      match Γ with
      | .nil => by exfalso; simp at Heq
      | .cons Γ Γs => fst _ _ ≫ eqToHom (congr_arg interp_ty (by simp at Heq; exact Heq))
    | .succ p' =>
      match Γ with
      | .nil => by exfalso; simp at Heq
      | .cons Γ Γs => snd _ _ ≫ octx_proj Γs p' Δ Heq

  def octx_proj' (Γ : OCTX.{i}) (p : Nat) (Hlt : p < Γ.length) :
    ⟦Γ⟧ₒ ⟶ ⟦Γ[p]⟧ₜ :=
    match p with
    | .zero =>
      match Γ with
      | .nil => by exfalso; simp at Hlt
      | .cons Γ Γs => fst _ _ ≫ eqToHom (Eq.refl _)
    | .succ p' =>
      match Γ with
      | .nil => by exfalso; simp at Hlt
      | .cons Γ Γs => snd _ _ ≫ octx_proj' Γs p' (Nat.lt_of_succ_lt_succ Hlt)

end ctx

section tm
  open CategoryTheory
  open Opposite
  open Functor
  open CartesianMonoidalCategory
  open MonoidalCategory
  open Logic

  def interp_embed {Γ : CTX.{i}} (A : Type (imax i 0)) (a : A)
    : ⟦Γ⟧ₛ ⟶ ⟦TYPE.embed A⟧ₜ :=
    {
      app X := ↾(fun _ => ULift.up a)
    }

  def interp_embed_apply {Γ : CTX.{i}} (A B : Type (imax i 0))
    (f : ⟦Γ⟧ₛ ⟶ ⟦TYPE.embed (A → B)⟧ₜ)
    (x : ⟦Γ⟧ₛ ⟶ ⟦TYPE.embed A⟧ₜ)
    : ⟦Γ⟧ₛ ⟶ ⟦TYPE.embed B⟧ₜ :=
    {
      app X := ↾(fun γ => (ConcreteCategory.hom (f.app X) γ).seq (fun _ => ConcreteCategory.hom (x.app X) γ))
      naturality X Y g := by
        ext i
        have T := types_congr_hom (f.naturality g) i
        have U := types_congr_hom (x.naturality g) i
        simp only [ConcreteCategory.hom_ofHom,
          types_comp_apply, TypeCat.Fun.toFun_apply] at T U ⊢
        change ConcreteCategory.hom (f.app Y) (ConcreteCategory.hom (⟦Γ⟧ₛ.map g) i) =
          ConcreteCategory.hom (f.app X) i at T
        change ConcreteCategory.hom (x.app Y) (ConcreteCategory.hom (⟦Γ⟧ₛ.map g) i) =
          ConcreteCategory.hom (x.app X) i at U
        change ULift.seq (ConcreteCategory.hom (f.app Y) (ConcreteCategory.hom (⟦Γ⟧ₛ.map g) i))
            (fun _ => ConcreteCategory.hom (x.app Y) (ConcreteCategory.hom (⟦Γ⟧ₛ.map g) i)) =
          ULift.seq (ConcreteCategory.hom (f.app X) i) (fun _ => ConcreteCategory.hom (x.app X) i)
        rw [T, U]
    }

  def interp_pure {Γ : CTX.{i}}
    (e : ⟦Γ⟧ₛ ⟶ ⟦TYPE.embed Prop⟧ₜ)
    : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ :=
    {
      app X := ↾(fun γ => ConcreteCategory.hom ((⌜(ConcreteCategory.hom (e.app X) γ).down⌝ᵢ).app X) γ)
      naturality X Y g := by
        ext i
        have T := types_congr_hom (e.naturality g) i
        simp only [ConcreteCategory.hom_ofHom,
          types_comp_apply, TypeCat.Fun.toFun_apply, TypeCat.Fun.mk_apply] at T ⊢
        rw [T]
        exact NatTrans.naturality_apply (⌜((ConcreteCategory.hom (e.app X) i).down)⌝ᵢ) g i
    }

  def interp_var {Γ : CTX.{i}} {Δ : OCTX.{i}} {τ : TYPE.{i}}
    (p q : Nat)
    (Heq1 : Γ[p]? = some Δ)
    (Heq2 : Δ[q]? = some τ)
    : ⟦Γ⟧ₛ ⟶ ⟦τ⟧ₜ := ctx_proj Γ p Δ Heq1 ≫ octx_proj Δ q τ Heq2

  def interp_var' {Γ : CTX.{i}}
    (p q : Nat)
    (Heq1 : p < Γ.length)
    (Heq2 : q < Γ[p].length)
    : ⟦Γ⟧ₛ ⟶ ⟦Γ[p][q]⟧ₜ := ctx_proj' Γ p Heq1 ≫ octx_proj' _ q Heq2

  def interp_app {Γ : CTX.{i}} {σ τ : TYPE.{i}}
    (e₁ : ⟦Γ⟧ₛ ⟶ ⟦TYPE.arr σ τ⟧ₜ)
    (e₂ : ⟦Γ⟧ₛ ⟶ ⟦σ⟧ₜ)
    : ⟦Γ⟧ₛ ⟶ ⟦τ⟧ₜ := lift e₂ e₁ ≫ (ihom.ev ⟦σ⟧ₜ).app ⟦τ⟧ₜ

  def interp_lam {Γ : OCTX.{i}} {Γs : CTX.{i}} {σ τ : TYPE.{i}}
    (e : ⟦(σ :: Γ) :: Γs⟧ₛ ⟶ ⟦τ⟧ₜ)
    : ⟦Γ :: Γs⟧ₛ ⟶ ⟦TYPE.arr σ τ⟧ₜ := MonoidalClosed.curry $ (α_ _ _ _).inv ≫ e

  def interp_delay {Γ : CTX.{i}} {τ : TYPE.{i}}
    (e : ⟦[] :: Γ⟧ₛ ⟶ ⟦τ⟧ₜ)
    : ⟦Γ⟧ₛ ⟶ ⟦TYPE.later τ⟧ₜ := (earlier_later_adj.homEquiv ⟦Γ⟧ₛ ⟦τ⟧ₜ).toFun ((λ_ (earlier.obj ⟦Γ⟧ₛ)).inv ≫ e)

  def interp_adv {Γ : CTX.{i}} {τ : TYPE.{i}}
    (n : Nat)
    (G : 0 < n)
    (e : ⟦Γ.drop n⟧ₛ ⟶ ⟦TYPE.later τ⟧ₜ)
    : ⟦Γ⟧ₛ ⟶ ⟦τ⟧ₜ := (interp_ctx_split Γ (i := n)).hom ≫ fst _ _ ≫ (n_force_cut G).app _ ≫ ((earlier_later_adj.homEquiv ⟦List.drop n Γ⟧ₛ ⟦τ⟧ₜ).invFun e)

  def interp_fix {Γ : OCTX.{i}} {Γs : CTX.{i}} {τ : TYPE.{i}}
    (e : ⟦(TYPE.later τ :: Γ) :: Γs⟧ₛ ⟶ ⟦τ⟧ₜ)
    : ⟦Γ :: Γs⟧ₛ ⟶ ⟦τ⟧ₜ := fixpoint $ (α_ _ _ _).inv ≫ e

  def interp_pair {Γ : CTX.{i}} {σ τ : TYPE.{i}}
    (e₁ : ⟦Γ⟧ₛ ⟶ ⟦σ⟧ₜ)
    (e₂ : ⟦Γ⟧ₛ ⟶ ⟦τ⟧ₜ)
    : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prod σ τ⟧ₜ := lift e₁ e₂

  def interp_projL {Γ : CTX.{i}} {σ τ : TYPE.{i}}
    (e : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prod σ τ⟧ₜ)
    : ⟦Γ⟧ₛ ⟶ ⟦σ⟧ₜ := e ≫ fst _ _

  def interp_projR {Γ : CTX.{i}} {σ τ : TYPE.{i}}
    (e : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prod σ τ⟧ₜ)
    : ⟦Γ⟧ₛ ⟶ ⟦τ⟧ₜ := e ≫ snd _ _

  def ℐ.psum.inl (X Y : ℐ.{i}) : X ⟶ ℐ.psum X Y where
    app n := ↾Sum.inl
    naturality {m n} f := by ext x; simp [ℐ.psum]
  def ℐ.psum.inr (X Y : ℐ.{i}) : Y ⟶ ℐ.psum X Y where
    app n := ↾Sum.inr
    naturality {m n} f := by ext x; simp [ℐ.psum]

  def interp_inl {Γ : CTX.{i}} {A B : TYPE.{i}} (e : ⟦Γ⟧ₛ ⟶ ⟦A⟧ₜ)
    : ⟦Γ⟧ₛ ⟶ ⟦TYPE.sum A B⟧ₜ := e ≫ ℐ.psum.inl ⟦A⟧ₜ ⟦B⟧ₜ
  def interp_inr {Γ : CTX.{i}} {A B : TYPE.{i}} (e : ⟦Γ⟧ₛ ⟶ ⟦B⟧ₜ)
    : ⟦Γ⟧ₛ ⟶ ⟦TYPE.sum A B⟧ₜ := e ≫ ℐ.psum.inr ⟦A⟧ₜ ⟦B⟧ₜ

  def ihomApp {A C : TYPE.{i}} (n : ℕᵒᵖ) (cf : ((ihom ⟦A⟧ₜ).obj ⟦C⟧ₜ).obj n)
      (a : (⟦A⟧ₜ).obj n) : (⟦C⟧ₜ).obj n :=
    ((ihom.ev ⟦A⟧ₜ).app ⟦C⟧ₜ).app n (a, cf)

  lemma ihomApp_nat {A C : TYPE.{i}} {m n : ℕᵒᵖ} (φ : m ⟶ n)
      (cf : ((ihom ⟦A⟧ₜ).obj ⟦C⟧ₜ).obj m) (a : (⟦A⟧ₜ).obj m) :
      (⟦C⟧ₜ).map φ (ihomApp (A := A) (C := C) m cf a)
        = ihomApp (A := A) (C := C) n (((ihom ⟦A⟧ₜ).obj ⟦C⟧ₜ).map φ cf) ((⟦A⟧ₜ).map φ a) := by
    simp only [ihomApp]
    exact (ConcreteCategory.congr_hom (((ihom.ev ⟦A⟧ₜ).app ⟦C⟧ₜ).naturality φ)
      (show (⟦A⟧ₜ ⊗ (ihom ⟦A⟧ₜ).obj ⟦C⟧ₜ).obj m from (a, cf))).symm

  def caseMor (A C B : TYPE.{i}) :
      ((⟦TYPE.arr A C⟧ₜ) ⊗ (⟦TYPE.arr B C⟧ₜ)) ⊗ ℐ.psum ⟦A⟧ₜ ⟦B⟧ₜ ⟶ ⟦C⟧ₜ where
    app n := ↾(fun p =>
      Sum.elim (fun a => ihomApp (A := A) (C := C) n p.1.1 a)
        (fun b => ihomApp (A := B) (C := C) n p.1.2 b) p.2)
    naturality {m n} φ := by
      ext p
      obtain ⟨⟨cf, cg⟩, s⟩ := p
      cases s with
      | inl a => exact (ihomApp_nat (A := A) (C := C) φ cf a).symm
      | inr b => exact (ihomApp_nat (A := B) (C := C) φ cg b).symm

  def interp_case {Γ : CTX.{i}} {A B C : TYPE.{i}}
      (e : ⟦Γ⟧ₛ ⟶ ⟦TYPE.sum A B⟧ₜ)
      (f : ⟦Γ⟧ₛ ⟶ ⟦TYPE.arr A C⟧ₜ)
      (g : ⟦Γ⟧ₛ ⟶ ⟦TYPE.arr B C⟧ₜ)
      : ⟦Γ⟧ₛ ⟶ ⟦C⟧ₜ := lift (lift f g) e ≫ caseMor A C B

  lemma interp_case_inl {Γ : CTX.{i}} {A B C : TYPE.{i}}
      (a : ⟦Γ⟧ₛ ⟶ ⟦A⟧ₜ) (f : ⟦Γ⟧ₛ ⟶ ⟦TYPE.arr A C⟧ₜ) (g : ⟦Γ⟧ₛ ⟶ ⟦TYPE.arr B C⟧ₜ) :
      interp_case (A := A) (B := B) (C := C) (interp_inl a) f g = interp_app f a := by
    simp only [interp_case, interp_inl, interp_app]
    ext n γ
    simp only [ℐ.psum.inl, caseMor, ihomApp]
    rfl

  lemma interp_case_inr {Γ : CTX.{i}} {A B C : TYPE.{i}}
      (b : ⟦Γ⟧ₛ ⟶ ⟦B⟧ₜ) (f : ⟦Γ⟧ₛ ⟶ ⟦TYPE.arr A C⟧ₜ) (g : ⟦Γ⟧ₛ ⟶ ⟦TYPE.arr B C⟧ₜ) :
      interp_case (A := A) (B := B) (C := C) (interp_inr b) f g = interp_app g b := by
    simp only [interp_case, interp_inr, interp_app]
    ext n γ
    simp only [ℐ.psum.inr, caseMor, ihomApp]
    rfl

  def interp_or {Γ : CTX.{i}}
    (e₁ e₂ : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
    : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ := e₁ ∨ᵢ e₂

  def interp_and {Γ : CTX.{i}}
    (e₁ e₂ : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
    : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ := e₁ ∧ᵢ e₂

  def interp_impl {Γ : CTX.{i}}
    (e₁ e₂ : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
    : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ := e₁ →ᵢ e₂

  def interp_forall {Γ : OCTX.{i}} {Γs : CTX.{i}} {τ : TYPE.{i}}
    (e : ⟦(τ :: Γ) :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
    : ⟦Γ :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ := ∀ᵢ[⟦τ⟧ₜ] (α_ _ _ _).inv ≫ e

  def interp_exists {Γ : OCTX.{i}} {Γs : CTX.{i}} {τ : TYPE.{i}}
    (e : ⟦(τ :: Γ) :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
    : ⟦Γ :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ := ∃ᵢ[⟦τ⟧ₜ] (α_ _ _ _).inv ≫ e

  attribute [-instance] ℐ.closed ℐ.monoidalClosed in
  lemma interp_forall_natural {Γ Δ : OCTX.{i}} {Γs Δs : CTX.{i}} {τ : TYPE.{i}}
    (f : ⟦Δ :: Δs⟧ₛ ⟶ ⟦Γ :: Γs⟧ₛ) (e : ⟦(τ :: Γ) :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
    : interp_forall ((α_ ⟦τ⟧ₜ ⟦Δ⟧ₒ (earlier.obj ⟦Δs⟧ₛ)).hom ≫ ⟦τ⟧ₜ ◁ f
        ≫ (α_ ⟦τ⟧ₜ ⟦Γ⟧ₒ (earlier.obj ⟦Γs⟧ₛ)).inv ≫ e)
      = f ≫ interp_forall e := by
    simp only [interp_forall, Logic.all, interp_ctx, interp_octx, interp_ty] at f e ⊢
    rw [Iso.inv_hom_id_assoc, MonoidalClosed.curry_natural_left, Category.assoc]

  attribute [-instance] ℐ.closed ℐ.monoidalClosed in
  lemma interp_exists_natural {Γ Δ : OCTX.{i}} {Γs Δs : CTX.{i}} {τ : TYPE.{i}}
    (f : ⟦Δ :: Δs⟧ₛ ⟶ ⟦Γ :: Γs⟧ₛ) (e : ⟦(τ :: Γ) :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
    : interp_exists ((α_ ⟦τ⟧ₜ ⟦Δ⟧ₒ (earlier.obj ⟦Δs⟧ₛ)).hom ≫ ⟦τ⟧ₜ ◁ f
        ≫ (α_ ⟦τ⟧ₜ ⟦Γ⟧ₒ (earlier.obj ⟦Γs⟧ₛ)).inv ≫ e)
      = f ≫ interp_exists e := by
    simp only [interp_exists, Logic.exist, interp_ctx, interp_octx, interp_ty] at f e ⊢
    rw [Iso.inv_hom_id_assoc, MonoidalClosed.curry_natural_left, Category.assoc]

  def interp_lift {Γ : CTX.{i}}
    (e : ⟦Γ⟧ₛ ⟶ ⟦TYPE.later TYPE.prop⟧ₜ)
    : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ := e ≫ lift_subobject_classifier

  def interp_true {Γ : CTX.{i}}
    : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ := ⊤ᵢ

  def interp_false {Γ : CTX.{i}}
    : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ := ⊥ᵢ

  def interp_eq {Γ : CTX.{i}} {τ : TYPE.{i}}
    (e₁ e₂ : ⟦Γ⟧ₛ ⟶ ⟦τ⟧ₜ)
    : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ := e₁ ≡ᵢ e₂

end tm

section ren
  open CategoryTheory
  open Opposite
  open Functor
  open CartesianMonoidalCategory
  open MonoidalCategory

  def interp_ren_id {Γ : CTX.{i}}
    : ⟦Γ⟧ₛ ⟶ ⟦Γ⟧ₛ := 𝟙 _

  def interp_ren_comp {Γ Δ Ψ : CTX.{i}}
    (Hσ' : ⟦Ψ⟧ₛ ⟶ ⟦Δ⟧ₛ)
    (Hσ : ⟦Δ⟧ₛ ⟶ ⟦Γ⟧ₛ)
    : ⟦Ψ⟧ₛ ⟶ ⟦Γ⟧ₛ := Hσ' ≫ Hσ

  def interp_ren_local_weaken {Ψ Φ : OCTX.{i}} {Γs Δs : CTX.{i}} {τ : TYPE.{i}}
    (Hσ : ⟦Ψ :: Γs⟧ₛ ⟶ ⟦Φ :: Δs⟧ₛ)
    : ⟦(τ :: Ψ) :: Γs⟧ₛ ⟶ ⟦Φ :: Δs⟧ₛ := (α_ _ _ _).hom ≫ snd _ _ ≫ Hσ

  def interp_ren_cons {Ψ Φ : OCTX.{i}} {Γs Δs : CTX.{i}} {τ : TYPE.{i}}
    (Hσ : ⟦Ψ :: Γs⟧ₛ ⟶ ⟦Φ :: Δs⟧ₛ)
    : ⟦(τ :: Ψ) :: Γs⟧ₛ ⟶ ⟦(τ :: Φ) :: Δs⟧ₛ := (α_ _ _ _).hom ≫ ((𝟙 _) ⊗ₘ Hσ) ≫ (α_ _ _ _).inv

  def interp_ren_global_lift {Γ Δ : CTX.{i}}
    (Hσ : ⟦Γ⟧ₛ ⟶ ⟦Δ⟧ₛ)
    : ⟦[] :: Γ⟧ₛ ⟶ ⟦[] :: Δ⟧ₛ := (𝟙 _) ⊗ₘ (earlier.map Hσ)

  def interp_ren_global_shift {Γ Δ Ψ : CTX.{i}} {n : Nat}
    (_Heq : n = Ψ.length)
    (Hσ : ⟦Γ⟧ₛ ⟶ ⟦Δ⟧ₛ)
    : ⟦Ψ ++ Γ⟧ₛ ⟶ ⟦Δ⟧ₛ := ((interp_ctx_split (Γ := Ψ ++ Γ) (i := List.length Ψ)).hom ≫ fst _ _ ≫ n_force.app _ ≫ eqToHom (by simp)) ≫ Hσ

end ren

section subst
  open CategoryTheory
  open Opposite
  open Functor
  open CartesianMonoidalCategory
  open MonoidalCategory

  def interp_subst_epsilon {Γ : CTX.{i}}
    : ⟦Γ⟧ₛ ⟶ ⟦.nil⟧ₒ := (toUnit _)

  def interp_subst_cons {Γ : CTX.{i}} {Δ : OCTX.{i}} {τ : TYPE.{i}}
    (He : ⟦Γ⟧ₛ ⟶ ⟦τ⟧ₜ)
    (Hσ : ⟦Γ⟧ₛ ⟶ ⟦Δ⟧ₒ)
    : ⟦Γ⟧ₛ ⟶ ⟦τ :: Δ⟧ₒ := lift He Hσ

end subst

section ssubst
  open CategoryTheory
  open Opposite
  open Functor
  open CartesianMonoidalCategory
  open MonoidalCategory

  def interp_ssubst_single {Γ : CTX.{i}} {Δ : OCTX.{i}}
    (Hσ : ⟦Γ⟧ₛ ⟶ ⟦Δ⟧ₒ)
    : ⟦Γ⟧ₛ ⟶ ⟦[Δ]⟧ₛ := Hσ ≫ (λ_ ⟦Δ⟧ₒ).inv ≫ lift (snd _ _) (fst _ _)

  def interp_ssubst_wk {Γ Δs Ψ : CTX.{i}} {Δ : OCTX.{i}} {n : Nat}
    (Hn : 0 < n)
    (Heq : n = Ψ.length)
    (Hσs : ⟦Γ⟧ₛ ⟶ ⟦Δs⟧ₛ)
    (Hσ : ⟦Ψ ++ Γ⟧ₛ ⟶ ⟦Δ⟧ₒ)
    : ⟦Ψ ++ Γ⟧ₛ ⟶ ⟦Δ :: Δs⟧ₛ := lift Hσ ((interp_ctx_split (Γ := Ψ ++ Γ) (i := n)).hom ≫ fst _ _ ≫ (n_force_cut Hn).app _ ≫ earlier.map ((eqToHom (by rw [Heq]; simp)) ≫ Hσs))

end ssubst

section eq
  open CategoryTheory
  open Opposite
  open Functor
  open CartesianMonoidalCategory
  open MonoidalCategory
  open MonoidalClosed

  lemma lift_comp_whiskerLeft {S X Z W : ℐ.{i}} (a : X ⟶ S) (c : X ⟶ W) (m : W ⟶ Z) :
      lift a (c ≫ m) = lift a c ≫ (S ◁ m) := by
    rw [← MonoidalCategory.id_tensorHom, lift_map, Category.comp_id]

  lemma lift_curry_ev {S X Z : ℐ.{i}} (a : X ⟶ S) (h : S ⊗ X ⟶ Z) :
      lift a (MonoidalClosed.curry h) ≫ (ihom.ev S).app Z = lift a (𝟙 X) ≫ h := by
    rw [show lift a (MonoidalClosed.curry h)
        = lift a (𝟙 X) ≫ (S ◁ MonoidalClosed.curry h) by
      rw [← MonoidalCategory.id_tensorHom, lift_map, Category.comp_id, Category.id_comp],
      Category.assoc, ← MonoidalClosed.uncurry_eq, MonoidalClosed.uncurry_curry]

  theorem beta_lam {Γ : OCTX.{i}} {Γs : CTX.{i}} {σ τ : TYPE.{i}}
    (e : ⟦(σ :: Γ) :: Γs⟧ₛ ⟶ ⟦τ⟧ₜ)
    (a : ⟦Γ :: Γs⟧ₛ ⟶ ⟦σ⟧ₜ)
    : interp_app (interp_lam e) a = (lift a (𝟙 _) ≫ (α_ _ _ _).inv) ≫ e := by
    simp only [interp_app, interp_lam, interp_ctx]
    simp only [interp_ctx, interp_octx, interp_ty] at e a ⊢
    calc lift a (MonoidalClosed.curry (α_ ⟦σ⟧ₜ ⟦Γ⟧ₒ (earlier.obj ⟦Γs⟧ₛ)).inv ≫ (ihom ⟦σ⟧ₜ).map e)
          ≫ (ihom.ev ⟦σ⟧ₜ).app ⟦τ⟧ₜ
        = (lift a (MonoidalClosed.curry (α_ ⟦σ⟧ₜ ⟦Γ⟧ₒ (earlier.obj ⟦Γs⟧ₛ)).inv)
            ≫ (⟦σ⟧ₜ ◁ (ihom ⟦σ⟧ₜ).map e)) ≫ (ihom.ev ⟦σ⟧ₜ).app ⟦τ⟧ₜ :=
          congrArg (· ≫ (ihom.ev ⟦σ⟧ₜ).app ⟦τ⟧ₜ) (lift_comp_whiskerLeft a _ _)
      _ = lift a (MonoidalClosed.curry (α_ ⟦σ⟧ₜ ⟦Γ⟧ₒ (earlier.obj ⟦Γs⟧ₛ)).inv)
            ≫ ((⟦σ⟧ₜ ◁ (ihom ⟦σ⟧ₜ).map e) ≫ (ihom.ev ⟦σ⟧ₜ).app ⟦τ⟧ₜ) :=
          Category.assoc _ _ _
      _ = lift a (MonoidalClosed.curry (α_ ⟦σ⟧ₜ ⟦Γ⟧ₒ (earlier.obj ⟦Γs⟧ₛ)).inv)
            ≫ ((ihom.ev ⟦σ⟧ₜ).app ((⟦σ⟧ₜ ⊗ ⟦Γ⟧ₒ) ⊗ earlier.obj ⟦Γs⟧ₛ) ≫ e) :=
          whisker_eq _ ((ihom.ev ⟦σ⟧ₜ).naturality e)
      _ = (lift a (MonoidalClosed.curry (α_ ⟦σ⟧ₜ ⟦Γ⟧ₒ (earlier.obj ⟦Γs⟧ₛ)).inv)
            ≫ (ihom.ev ⟦σ⟧ₜ).app ((⟦σ⟧ₜ ⊗ ⟦Γ⟧ₒ) ⊗ earlier.obj ⟦Γs⟧ₛ)) ≫ e :=
          (Category.assoc _ _ _).symm
      _ = (lift a (𝟙 _) ≫ (α_ ⟦σ⟧ₜ ⟦Γ⟧ₒ (earlier.obj ⟦Γs⟧ₛ)).inv) ≫ e :=
          congrArg (· ≫ e) (lift_curry_ev a _)
  theorem beta_delay {Γ : CTX.{i}} {τ : TYPE.{i}}
    (n : Nat) (G : 0 < n)
    (e : ⟦[] :: List.drop n Γ⟧ₛ ⟶ ⟦τ⟧ₜ)
    : interp_adv n G (Γ := Γ) (interp_delay e) = ((interp_ctx_split Γ (i := n)).hom ≫ fst _ _ ≫ (n_force_cut G).app _ ≫ (λ_ _).inv) ≫ e := by
    simp [interp_adv, interp_delay]

  theorem fixpoint_unfold' {Γs : CTX.{i}} {Γ : OCTX.{i}} {τ : TYPE.{i}}
    (e : ⟦(TYPE.later τ :: Γ) :: Γs⟧ₛ ⟶ ⟦τ⟧ₜ)
    : interp_fix e = (lift (interp_fix e ≫ next.app _) (𝟙 _) ≫ (α_ _ _ _).inv) ≫ e := by
    simp only [interp_fix]
    conv =>
      lhs
      rw [fixpoint_unfold]
    rfl

  theorem beta_prod_l {Γ : CTX.{i}} {σ τ : TYPE.{i}}
    (e₁ : ⟦Γ⟧ₛ ⟶ ⟦σ⟧ₜ)
    (e₂ : ⟦Γ⟧ₛ ⟶ ⟦τ⟧ₜ)
    : interp_projL (interp_pair e₁ e₂) = e₁ := by
    simp only [interp_pair, interp_projL]
    exact lift_fst _ _

  theorem beta_prod_r {Γ : CTX.{i}} {σ τ : TYPE.{i}}
    (e₁ : ⟦Γ⟧ₛ ⟶ ⟦σ⟧ₜ)
    (e₂ : ⟦Γ⟧ₛ ⟶ ⟦τ⟧ₜ)
    : interp_projR (interp_pair e₁ e₂) = e₂ := by
    simp only [interp_pair, interp_projR]
    exact lift_snd _ _

  theorem eta_prod {Γ : CTX.{i}} {σ τ : TYPE.{i}}
    (e : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prod σ τ⟧ₜ)
    : e = interp_pair (interp_projL e) (interp_projR e) := by
    simp only [interp_pair, interp_projL, interp_projR, interp_ty] at e ⊢
    rw [← comp_lift, lift_fst_snd, Category.comp_id]

  theorem eta_delay {Γ : CTX.{i}} {τ : TYPE.{i}}
    (e : ⟦Γ⟧ₛ ⟶ ⟦TYPE.later τ⟧ₜ)
    : e = interp_delay (interp_adv 1 Nat.zero_lt_one (Γ := [] :: Γ) e) := by
    apply CategoryTheory.NatTrans.ext
    funext x
    cases x with | op n =>
    cases n with
    | zero =>
      rfl
    | succ n =>
      ext γ
      simp [interp_delay, interp_adv, n_force_cut, n_force, interp_ctx_split,
            earlier_prod, earlier_prod_hom,
            earlier_later_adj_succ, interp_ctx, interp_octx]
      simp [earlier, earlier_obj, earlier_arr, later,
            earlier_later_adj, Adjunction.homEquiv]
      repeat erw [ConcreteCategory.comp_apply]
      cases n <;> rfl
  theorem eta_lam' {Γ : OCTX.{i}} {Γs : CTX.{i}} {σ τ : TYPE.{i}}
    (e : ⟦Γ :: Γs⟧ₛ ⟶ ⟦TYPE.arr σ τ⟧ₜ)
    : e = interp_lam (interp_app ((α_ _ _ _).hom ≫ snd _ _ ≫ e) (fst _ _ ≫ fst _ _)) := by
    simp [interp_lam, interp_app, interp_octx]
    simp only [interp_ctx, interp_octx, interp_ty] at e ⊢
    symm
    apply (curry_eq_iff _ _).mpr
    symm
    rw [<-Category.comp_id (fst (⟦σ⟧ₜ ⊗ ⟦Γ⟧ₒ) (earlier.obj ⟦Γs⟧ₛ) ≫ fst ⟦σ⟧ₜ ⟦Γ⟧ₒ)]
    rw [Category.assoc]
    rw [<-lift_map]
    rw [Category.comp_id]
    rw [<-Category.assoc]
    rw [<-Category.comp_id (fst ⟦σ⟧ₜ ⟦Γ⟧ₒ)]
    simp_all only [Category.comp_id, lift_map, comp_lift, associator_inv_fst_fst,
      Iso.inv_hom_id_assoc]
    rfl

end eq

section later
  open CategoryTheory
  open Opposite
  open Functor
  open CartesianMonoidalCategory
  open MonoidalCategory
  open MonoidalClosed
  open Logic

  lemma later_intro (Φ : ⟦Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ) :
    Φ ⊢ᵢ (interp_lift (interp_delay ((λ_ _).hom ≫ force.app _ ≫ Φ))) := by
    intros n γ m f hyp
    cases n with
    | zero =>
      simp [interp_lift, interp_delay]
      simp [lift_subobject_classifier]
      erw [ConcreteCategory.comp_apply]
      erw [ConcreteCategory.hom_ofHom]
      trivial
    | succ n' =>
      simp [interp_lift, interp_delay]
      simp [lift_subobject_classifier]
      rw [Adjunction.homEquiv_naturality_right]
      rw [NatTrans.comp_app]
      simp [later, force, force_app, earlier_later_adj, Adjunction.homEquiv]
      repeat erw [ConcreteCategory.comp_apply]
      erw [NatTrans.naturality_apply]
      cases m with
      | zero =>
        erw [ConcreteCategory.hom_ofHom]
        erw [TypeCat.Fun.mk_apply]
        simp [Presieve_succFunctor]
      | succ m' =>
        left
        apply (Φ.app (op (n' + 1)) γ).down.downward_closed hyp
        simp
        apply (Nat.le_succ _).hom

  lemma later_mono {Γ : CTX.{i}} {P Q : ⟦[] :: Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ} (h : P ⊢ᵢ Q) :
      interp_lift (interp_delay P) ⊢ᵢ interp_lift (interp_delay Q) := by
    intro n γ m f hyp
    cases n with
    | zero =>
      simp_all [interp_lift, interp_delay, lift_subobject_classifier]
      erw [ConcreteCategory.comp_apply]
      erw [ConcreteCategory.hom_ofHom]
      trivial
    | succ n' =>
      simp [interp_lift, interp_delay] at hyp ⊢
      simp [lift_subobject_classifier] at hyp ⊢
      rw [Adjunction.homEquiv_naturality_right] at hyp ⊢
      rw [NatTrans.comp_app] at hyp ⊢
      simp [later, earlier_later_adj, Adjunction.homEquiv] at hyp ⊢
      rcases hyp with hP | hm
      exacts [Or.inl (h _ _ _ _ hP), Or.inr hm]

  lemma later_conj {Γ : CTX.{i}} (P Q : ⟦[] :: Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ) :
      (interp_lift (interp_delay P) ∧ᵢ interp_lift (interp_delay Q))
        ⊢ᵢ interp_lift (interp_delay (P ∧ᵢ Q)) := by
    intro n γ m f hyp
    cases n with
    | zero =>
      simp [interp_lift, interp_delay] at hyp ⊢
      simp [conj, conj_arr] at hyp ⊢
      simp [lift_subobject_classifier]
      erw [ConcreteCategory.comp_apply, ConcreteCategory.hom_ofHom]
      trivial
    | succ n' =>
      simp [interp_lift, interp_delay] at hyp ⊢
      simp [conj, conj_arr] at hyp ⊢
      rw [Adjunction.homEquiv_naturality_right] at hyp ⊢
      simp only [NatTrans.comp_app] at hyp ⊢
      simp [later] at hyp ⊢
      simp [earlier_later_adj, Adjunction.homEquiv] at hyp ⊢
      simp [lift_subobject_classifier] at hyp ⊢
      cases m with
      | zero =>
        erw [ConcreteCategory.comp_apply, ConcreteCategory.hom_ofHom, TypeCat.Fun.mk_apply]
        simp [Presieve_succFunctor]
      | succ m' =>
        obtain ⟨hP, hQ⟩ := hyp
        rcases hP with hP | hP
        · rcases hQ with hQ | hQ
          · exact Or.inl ⟨hP, hQ⟩
          · exact Or.inr hQ
        · exact Or.inr hP

  lemma later_disj {Γ : CTX.{i}} (P Q : ⟦[] :: Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ) :
      interp_lift (interp_delay (P ∨ᵢ Q))
        ⊢ᵢ (interp_lift (interp_delay P) ∨ᵢ interp_lift (interp_delay Q)) := by
    intro n γ m f hyp
    erw [disj_app]
    cases n with
    | zero =>
      left
      simp [interp_lift, interp_delay]
      simp [lift_subobject_classifier]
      erw [ConcreteCategory.comp_apply, ConcreteCategory.hom_ofHom]
      trivial
    | succ n' =>
      simp [interp_lift, interp_delay] at hyp
      rw [Adjunction.homEquiv_naturality_right] at hyp
      simp only [NatTrans.comp_app] at hyp
      simp [later] at hyp
      simp [earlier_later_adj, Adjunction.homEquiv] at hyp
      simp [lift_subobject_classifier] at hyp
      cases m with
      | zero =>
        left
        simp [interp_lift, interp_delay]
        rw [Adjunction.homEquiv_naturality_right]
        simp only [NatTrans.comp_app]
        simp [later]
        simp [earlier_later_adj, Adjunction.homEquiv]
        simp [lift_subobject_classifier]
        erw [ConcreteCategory.comp_apply, ConcreteCategory.hom_ofHom, TypeCat.Fun.mk_apply]
        simp [Presieve_succFunctor]
      | succ m' =>
        rcases hyp with hPQ | hm
        · rcases hPQ with hP | hQ
          · left
            simp [interp_lift, interp_delay]
            rw [Adjunction.homEquiv_naturality_right]
            simp only [NatTrans.comp_app]
            simp [later]
            simp [earlier_later_adj, Adjunction.homEquiv]
            simp [lift_subobject_classifier]
            exact Or.inl hP
          · right
            simp [interp_lift, interp_delay]
            rw [Adjunction.homEquiv_naturality_right]
            simp only [NatTrans.comp_app]
            simp [later]
            simp [earlier_later_adj, Adjunction.homEquiv]
            simp [lift_subobject_classifier]
            exact Or.inl hQ
        · left
          simp [interp_lift, interp_delay]
          rw [Adjunction.homEquiv_naturality_right]
          simp only [NatTrans.comp_app]
          simp [later]
          simp [earlier_later_adj, Adjunction.homEquiv]
          simp [lift_subobject_classifier]
          exact Or.inr hm

  lemma later_loeb {P : ⟦Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ} : (((interp_lift (interp_delay ((λ_ _).hom ≫ force.app _ ≫ P))) ∧ᵢ Q) ⊢ᵢ P) → (Q ⊢ᵢ P) := by
    intros H n γ m; revert γ n
    induction m with
    | zero =>
      intros n γ f hyp
      have Qn := H 0 (⟦Γs⟧ₛ.map f.op γ) 0 (CategoryStruct.id _)
      rw [NatTrans.naturality_apply] at Qn; rw [NatTrans.naturality_apply] at Qn
      apply Qn; clear Qn; rw [Logic.conj_app]; constructor
      · simp only [interp_lift, interp_delay]; cases n <;>
          (erw [ConcreteCategory.comp_apply, ConcreteCategory.hom_ofHom, TypeCat.Fun.mk_apply];
           first | simp)
      · simpa using hyp
    | succ m' IH =>
      intros n γ f hyp
      apply (H n γ (Nat.succ m') f)
      rw [Logic.conj_app]
      refine ⟨?_, by simpa using hyp⟩
      simp only [interp_lift, interp_delay]
      cases n with
      | zero =>
        erw [ConcreteCategory.comp_apply, ConcreteCategory.hom_ofHom, TypeCat.Fun.mk_apply]
        simp
      | succ n' =>
        erw [ConcreteCategory.comp_apply, ConcreteCategory.hom_ofHom, TypeCat.Fun.mk_apply]
        show (Sieve_succFunctor ((ConcreteCategory.hom (P.app (op n')))
            ((ConcreteCategory.hom (⟦Γs⟧ₛ.map (op (homOfLE (Nat.le_succ n'))))) γ)).down).arrows f
        simp only [Sieve_succFunctor, Presieve_succFunctor]
        left
        apply IH
        erw [NatTrans.naturality_apply]
        exact ((ConcreteCategory.hom (Q.app (op (n' + 1)))) γ).down.downward_closed hyp
          ((Nat.le_succ m').hom)

section prf
  open CategoryTheory
  open Opposite
  open Functor
  open CartesianMonoidalCategory
  open MonoidalCategory
  open MonoidalClosed
  open Logic

  def poctx (Ψs : List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)) : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ :=
    match Ψs with
    | .nil => true
    | .cons Ψ Ψs => conj Ψ (poctx Ψs)

  def pctx (Ψs : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ :=
    match Ψs with
    | .nil => true
    | .cons Ψ Ψs => conj (poctx Ψ) (pctx Ψs)

  theorem interp_poctx_split (Ψs : List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))
    : poctx Ψs = conj (poctx (Ψs.drop i)) (poctx (Ψs.take i)) :=
    match Ψs with
    | .nil =>
      match i with
      | .zero => by
        simp only [List.drop_nil, List.take_nil, poctx]; ext x a
        simp only [TypeCat.Fun.toFun_apply, Logic.conj_app, Logic.true_app, inf_top_eq]
        rfl
      | .succ i' => by
        simp only [List.drop_nil, List.take_nil, poctx]; ext x a
        simp only [TypeCat.Fun.toFun_apply, Logic.conj_app, Logic.true_app, inf_top_eq]
        rfl
    | .cons x xs =>
      match i with
      | .zero => by
        simp only [poctx, List.drop_zero, List.take_zero]; ext x a
        simp only [TypeCat.Fun.toFun_apply, Logic.conj_app, Logic.true_app, inf_top_eq]
        rfl
      | .succ i' => by
        simp only [poctx, List.drop_succ_cons, List.take_succ_cons]; ext x a
        simp only [TypeCat.Fun.toFun_apply, Logic.conj_app]
        rw [NatTrans.congr_app (interp_poctx_split xs (i := i')) x]
        simp only [Logic.conj_app]
        congr 1; rw [inf_left_comm]
  theorem interp_pctx_split (Ψs : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)))
    : pctx Ψs = conj (pctx (Ψs.drop i)) (pctx (Ψs.take i)) :=
    match Ψs with
    | .nil =>
      match i with
      | .zero => by
        simp only [List.drop_nil, List.take_nil, pctx]; ext x a
        simp only [TypeCat.Fun.toFun_apply, Logic.conj_app, Logic.true_app, inf_top_eq]
        rfl
      | .succ i' => by
        simp only [List.drop_nil, List.take_nil, pctx]; ext x a
        simp only [TypeCat.Fun.toFun_apply, Logic.conj_app, Logic.true_app, inf_top_eq]
        rfl
    | .cons x xs =>
      match i with
      | .zero => by
        simp only [pctx, List.drop_zero, List.take_zero]; ext x a
        simp only [TypeCat.Fun.toFun_apply, Logic.conj_app, Logic.true_app, inf_top_eq]
        rfl
      | .succ i' => by
        simp only [pctx, List.drop_succ_cons, List.take_succ_cons]; ext x a
        simp only [TypeCat.Fun.toFun_apply, Logic.conj_app]
        rw [NatTrans.congr_app (interp_pctx_split xs (i := i')) x]
        simp only [Logic.conj_app]
        congr 1; rw [inf_left_comm]
  lemma pure_sound.{i} {P : ⟦([[]] : CTX.{i})⟧ₛ ⟶ ⟦TYPE.embed Prop⟧ₜ} (n : ℕ) : (pctx [[]] ⊢ᵢ interp_pure P) → (P.app (op n) ⟨PUnit.unit, PUnit.unit⟩).down := by
    intros prf
    specialize (prf n ⟨PUnit.unit, PUnit.unit⟩ n (𝟙 n))
    apply prf
    have hpctx : (⊤ᵢ : ⟦([[]] : CTX.{i})⟧ₛ ⟶ Ω) ⊢ᵢ pctx [[]] := by
      simp only [pctx, poctx]
      exact conj_intro true_intro true_intro
    exact hpctx n ⟨PUnit.unit, PUnit.unit⟩ n (𝟙 n) ⟨⟩
  lemma eq_sound (e e' : ⟦Γ⟧ₛ ⟶ ⟦τ⟧ₜ) : (pctx [[]] ⊢ᵢ interp_eq e e') → e = e' := by
    intros prf
    simp [pctx, poctx, interp_eq] at prf
    apply soundness_eq
    apply entails_trans; swap
    . apply prf
    . apply conj_intro <;> apply true_intro
  lemma intro_asm {n m : Nat} (eq1 : Ψs[n]? = some Ψ) (eq2 : Ψ[m]? = some Φ) : pctx Ψs ⊢ᵢ Φ := by
    obtain ⟨Hn, he1⟩ := List.getElem?_eq_some_iff.mp eq1
    obtain ⟨Hm, he2⟩ := List.getElem?_eq_some_iff.mp eq2
    rw [interp_pctx_split Ψs (i := n)]
    apply entails_trans
    . apply conj_elim_l
    . rw [show List.drop n Ψs = Ψ :: List.drop (n + 1) Ψs by
        rw [List.drop_eq_getElem_cons Hn, he1]]
      simp [pctx]
      apply entails_trans
      . apply conj_elim_l
      . exact he2 ▸ (show poctx Ψ ⊢ᵢ Ψ[m] by
          rw [interp_poctx_split Ψ (i := m)]
          apply entails_trans
          · exact conj_elim_l
          · exact List.drop_eq_getElem_cons Hm ▸ (conj_elim_l : poctx (Ψ[m] :: List.drop (m + 1) Ψ) ⊢ᵢ Ψ[m]))
  lemma intro_true : pctx Ψs ⊢ᵢ interp_true := true_intro
  lemma elim_false : (pctx Ψs ⊢ᵢ interp_false) → (pctx Ψs ⊢ᵢ Φ) := false_elim' _ _
  lemma intro_and : (pctx Ψs ⊢ᵢ Φ₁) → (pctx Ψs ⊢ᵢ Φ₂) → (pctx Ψs ⊢ᵢ (interp_and Φ₁ Φ₂)) :=
    conj_intro
  lemma elim_and_l : (pctx Ψs ⊢ᵢ (interp_and Φ₁ Φ₂)) → (pctx Ψs ⊢ᵢ Φ₁) := conj_elim_l' _ _ _
  lemma elim_and_r : (pctx Ψs ⊢ᵢ (interp_and Φ₁ Φ₂)) → (pctx Ψs ⊢ᵢ Φ₂) := conj_elim_r' _ _ _
  lemma intro_or_l : (pctx Ψs ⊢ᵢ Φ₁) → (pctx Ψs ⊢ᵢ (interp_or Φ₁ Φ₂)) := disj_intro_l' _ _ _
  lemma intro_or_r : (pctx Ψs ⊢ᵢ Φ₂) → (pctx Ψs ⊢ᵢ (interp_or Φ₁ Φ₂)) := disj_intro_r' _ _ _
  lemma elim_or : (pctx (Ψ :: Ψs) ⊢ᵢ (interp_or Φ₁ Φ₂)) →
      (pctx ((Φ₁ :: Ψ) :: Ψs) ⊢ᵢ Φ) → (pctx ((Φ₂ :: Ψ) :: Ψs) ⊢ᵢ Φ) →
      (pctx (Ψ :: Ψs) ⊢ᵢ Φ) := by
    intros h_or prf1 prf2
    apply disj_elim_ctx h_or
    · apply entails_trans _ _ _ ?_ prf1
      simp only [pctx, poctx]
      apply conj_intro
      · apply conj_intro
        · exact conj_elim_r
        · exact entails_trans _ _ _ conj_elim_l conj_elim_l
      · exact entails_trans _ _ _ conj_elim_l conj_elim_r
    · apply entails_trans _ _ _ ?_ prf2
      simp only [pctx, poctx]
      apply conj_intro
      · apply conj_intro
        · exact conj_elim_r
        · exact entails_trans _ _ _ conj_elim_l conj_elim_l
      · exact entails_trans _ _ _ conj_elim_l conj_elim_r
  lemma snd_lw_inv_app {X Y Z : ℐ.{i}} (n : ℕ) (a : X.obj (op n)) (g : (Y ⊗ Z).obj (op n)) :
      ((α_ X Y Z).hom ≫ snd _ _ ≫ 𝟙 _).app (op n) ((α_ X Y Z).inv.app (op n) (a, g)) = g := by
    change Y.obj (op n) × Z.obj (op n) at g
    rfl

  lemma fst_assoc_inv_app {X Y Z : ℐ.{i}} (n : ℕ) (a : X.obj (op n)) (g : (Y ⊗ Z).obj (op n)) :
      ((α_ X Y Z).hom ≫ fst _ _).app (op n) ((α_ X Y Z).inv.app (op n) (a, g)) = a := by
    change Y.obj (op n) × Z.obj (op n) at g
    rfl

  lemma elim_sum {G ExtA ExtB A B : ℐ.{i}}
      (e : G ⟶ ℐ.psum A B) (RA : ExtA ⟶ G) (vA : ExtA ⟶ A) (RB : ExtB ⟶ G) (vB : ExtB ⟶ B)
      (Φ Ψ : G ⟶ Ω)
      (surjA : ∀ (n : ℕ) (γ : G.obj (op n)) (a : A.obj (op n)),
          ∃ x : ExtA.obj (op n), RA.app (op n) x = γ ∧ vA.app (op n) x = a)
      (surjB : ∀ (n : ℕ) (γ : G.obj (op n)) (b : B.obj (op n)),
          ∃ x : ExtB.obj (op n), RB.app (op n) x = γ ∧ vB.app (op n) x = b)
      (Hinl : (((RA ≫ e) ≡ᵢ (vA ≫ ℐ.psum.inl A B)) ∧ᵢ (RA ≫ Ψ)) ⊢ᵢ (RA ≫ Φ))
      (Hinr : (((RB ≫ e) ≡ᵢ (vB ≫ ℐ.psum.inr A B)) ∧ᵢ (RB ≫ Ψ)) ⊢ᵢ (RB ≫ Φ))
      : Ψ ⊢ᵢ Φ := by
    intro n γ m f hΨ
    rcases hsum : e.app (op n) γ with a | b
    · obtain ⟨x, hRx, hvx⟩ := surjA n γ a
      have key := Hinl n x m f ⟨by
          show (ℐ.psum A B).map f.op ((RA ≫ e).app (op n) x)
              = (ℐ.psum A B).map f.op ((vA ≫ ℐ.psum.inl A B).app (op n) x)
          rw [show (RA ≫ e).app (op n) x = Sum.inl a by
                show e.app (op n) (RA.app (op n) x) = Sum.inl a
                rw [hRx, hsum],
              show (vA ≫ ℐ.psum.inl A B).app (op n) x = Sum.inl a by
                show (ℐ.psum.inl A B).app (op n) (vA.app (op n) x) = Sum.inl a
                rw [hvx]; rfl], by
          show (Ψ.app (op n) (RA.app (op n) x)).down.arrows f
          rw [hRx]; exact hΨ⟩
      rw [show (RA ≫ Φ).app (op n) x = Φ.app (op n) γ by
        show Φ.app (op n) (RA.app (op n) x) = Φ.app (op n) γ; rw [hRx]] at key
      exact key
    · obtain ⟨x, hRx, hvx⟩ := surjB n γ b
      have key := Hinr n x m f ⟨by
          show (ℐ.psum A B).map f.op ((RB ≫ e).app (op n) x)
              = (ℐ.psum A B).map f.op ((vB ≫ ℐ.psum.inr A B).app (op n) x)
          rw [show (RB ≫ e).app (op n) x = Sum.inr b by
                show e.app (op n) (RB.app (op n) x) = Sum.inr b
                rw [hRx, hsum],
              show (vB ≫ ℐ.psum.inr A B).app (op n) x = Sum.inr b by
                show (ℐ.psum.inr A B).app (op n) (vB.app (op n) x) = Sum.inr b
                rw [hvx]; rfl], by
          show (Ψ.app (op n) (RB.app (op n) x)).down.arrows f
          rw [hRx]; exact hΨ⟩
      rw [show (RB ≫ Φ).app (op n) x = Φ.app (op n) γ by
        show Φ.app (op n) (RB.app (op n) x) = Φ.app (op n) γ; rw [hRx]] at key
      exact key

  lemma intro_impl : (pctx ((Φ₁ :: Ψ) :: Ψs) ⊢ᵢ Φ₂) → (pctx (Ψ :: Ψs) ⊢ᵢ (interp_impl Φ₁ Φ₂)) := by
    intros prf
    apply impl_intro
    apply entails_trans; swap
    . apply prf
    . simp [pctx, poctx]
      apply entails_trans
      . apply conj_comm
      . apply conj_intro
        . apply conj_intro
          . apply conj_elim_l
          . apply entails_trans
            . apply conj_elim_r
            . apply conj_elim_l
        . apply entails_trans
          . apply conj_elim_r
          . apply conj_elim_r
  lemma elim_impl : (pctx Ψs ⊢ᵢ (interp_impl Φ₁ Φ₂)) → (pctx Ψs ⊢ᵢ Φ₁) → (pctx Ψs ⊢ᵢ Φ₂) := by
    intros prf1 prf2
    apply entails_trans; swap
    . apply impl_elim
      apply Φ₁
    . apply intro_and
      . apply prf1
      . apply prf2
  lemma intro_pure : P → (pctx Ψs ⊢ᵢ interp_pure (interp_embed _ P)) := by
    intros prf
    simp [interp_pure, interp_embed]
    exact pure_intro prf
  lemma intro_eq : (e = e') → (pctx Ψs ⊢ᵢ (interp_eq e e')) := by
    intros prf
    cases prf
    simp [interp_eq]
    exact entails_trans _ _ _ true_intro (eq_refl _)
  lemma elim_eq (e e' : ⟦Γ :: Γs⟧ₛ ⟶ ⟦τ⟧ₜ) (Φ : ⟦(τ :: Γ) :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
    : (pctx Ψs ⊢ᵢ (interp_eq e e')) → (pctx Ψs ⊢ᵢ ((lift e (𝟙 _) ≫ (α_ _ _ _).inv) ≫ Φ)) → (pctx Ψs ⊢ᵢ ((lift e' (𝟙 _) ≫ (α_ _ _ _).inv) ≫ Φ)) := by
    intros eq prf
    simp [interp_eq] at eq
    have prf' : pctx Ψs ⊢ᵢ ((lift e (𝟙 ⟦Γ :: Γs⟧ₛ) ≫ (α_ ⟦τ⟧ₜ ⟦Γ⟧ₒ (earlier.obj ⟦Γs⟧ₛ)).inv) ≡ᵢ (lift e' (𝟙 ⟦Γ :: Γs⟧ₛ) ≫ (α_ ⟦τ⟧ₜ ⟦Γ⟧ₒ (earlier.obj ⟦Γs⟧ₛ)).inv)) := by
      apply entails_trans; swap
      . apply Logic.eq_subst
      . simp [interp_ctx]
        clear prf
        intros n γ m f hyp
        let ⟨γ1, γ2⟩ := γ
        specialize (eq n ⟨γ1, γ2⟩ m f hyp)
        exact congrArg₂ Prod.mk eq rfl
    apply entails_trans; swap
    . apply eq_coerce (lift e (𝟙 ⟦Γ :: Γs⟧ₛ) ≫ (α_ ⟦τ⟧ₜ ⟦Γ⟧ₒ (earlier.obj ⟦Γs⟧ₛ)).inv ≫ Φ)
    . rw [←Category.assoc]
      apply conj_intro
      . apply entails_trans; swap
        . apply Logic.eq_subst
        . apply prf'
      . apply prf
  lemma intro_all (Ψs : List (List (⟦Γ :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ : ⟦(τ :: Γ) :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
    : ((interp_ren_local_weaken interp_ren_id ≫ pctx Ψs) ⊢ᵢ Φ) → (pctx Ψs ⊢ᵢ (interp_forall Φ)) := by
    intros prf
    apply all_intro
    simp [interp_ren_local_weaken, interp_ren_id] at prf
    simp only [interp_ctx, interp_octx] at prf
    simp [interp_ctx]
    intros n γ m f
    simp
    specialize (prf n ((α_ ⟦τ⟧ₜ ⟦Γ⟧ₒ (earlier.obj ⟦Γs⟧ₛ)).inv.app (op n) γ) m f)
    simp at prf
    apply prf
  lemma intro_all_points.{i} {Γ : OCTX.{i}} {Γs : CTX.{i}} {A : Type (imax i 0)}
      (Ψs : List (List (⟦Γ :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)))
      (Φ : ⟦((TYPE.embed A) :: Γ) :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
      (h : ∀ a : A, pctx Ψs ⊢ᵢ ((lift (interp_embed A a) (𝟙 _) ≫ (α_ _ _ _).inv) ≫ Φ)) :
      pctx Ψs ⊢ᵢ interp_forall Φ := by
    apply all_intro
    intro n x m f hf
    exact h x.1.down n x.2 m f hf

  lemma elim_all (Ψs : List (List (⟦Γ :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ : ⟦(τ :: Γ) :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
    : (pctx Ψs ⊢ᵢ (interp_forall Φ)) → (e : ⟦Γ :: Γs⟧ₛ ⟶ ⟦τ⟧ₜ) → (pctx Ψs ⊢ᵢ ((lift e (𝟙 _) ≫ (α_ _ _ _).inv) ≫ Φ)) := by
    intro prf typ
    apply entails_trans _ _ _ prf (all_elim ((α_ ⟦τ⟧ₜ ⟦Γ⟧ₒ (earlier.obj ⟦Γs⟧ₛ)).inv ≫ Φ) typ)

  lemma entails_precomp {X Y : ℐ.{i}} (g : X ⟶ Y) {P Q : Y ⟶ ⟦TYPE.prop⟧ₜ} (h : P ⊢ᵢ Q) :
      (g ≫ P) ⊢ᵢ (g ≫ Q) := by
    intro n γ m f hm
    exact h n ((ConcreteCategory.hom (g.app (op n))) γ) m f hm

  lemma conj_precomp {X Y : ℐ.{i}} (g : X ⟶ Y) (P Q : Y ⟶ ⟦TYPE.prop⟧ₜ) :
      g ≫ (P ∧ᵢ Q) = ((g ≫ P) ∧ᵢ (g ≫ Q)) := by
    simp only [Logic.conj, ← Category.assoc, comp_lift]

  lemma intro_ex (Ψs : List (List (⟦Γ :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ : ⟦(τ :: Γ) :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
      (e : ⟦Γ :: Γs⟧ₛ ⟶ ⟦τ⟧ₜ)
    : (pctx Ψs ⊢ᵢ ((lift e (𝟙 _) ≫ (α_ _ _ _).inv) ≫ Φ)) → (pctx Ψs ⊢ᵢ (interp_exists Φ)) := by
    intros prf
    refine entails_trans _ _ _ prf ?_
    rw [Category.assoc]
    exact exist_intro ((α_ ⟦τ⟧ₜ ⟦Γ⟧ₒ (earlier.obj ⟦Γs⟧ₛ)).inv ≫ Φ) e

  lemma elim_ex (Ψs : List (List (⟦Γ :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)))
      (Φ : ⟦(τ :: Γ) :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ) (Qi : ⟦Γ :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
    : (pctx Ψs ⊢ᵢ interp_exists Φ)
    → ((Φ ∧ᵢ (interp_ren_local_weaken interp_ren_id ≫ pctx Ψs))
        ⊢ᵢ (interp_ren_local_weaken interp_ren_id ≫ Qi))
    → (pctx Ψs ⊢ᵢ Qi) := by
    intros hex hbr
    have key : (((α_ ⟦τ⟧ₜ ⟦Γ⟧ₒ (earlier.obj ⟦Γs⟧ₛ)).inv ≫ Φ) ∧ᵢ
        ((snd ⟦τ⟧ₜ (⟦Γ⟧ₒ ⊗ earlier.obj ⟦Γs⟧ₛ)) ≫ pctx Ψs))
        ⊢ᵢ ((snd ⟦τ⟧ₜ (⟦Γ⟧ₒ ⊗ earlier.obj ⟦Γs⟧ₛ)) ≫ Qi) := by
      intro n γ m f hm
      obtain ⟨h1, h2⟩ := hm
      have hsnd := snd_lw_inv_app (X := ⟦τ⟧ₜ) (Y := ⟦Γ⟧ₒ) (Z := earlier.obj ⟦Γs⟧ₛ) n γ.1 γ.2
      have hb'' : ((ConcreteCategory.hom (Qi.app (op n)))
          ((ConcreteCategory.hom ((interp_ren_local_weaken interp_ren_id).app (op n)))
            ((α_ ⟦τ⟧ₜ ⟦Γ⟧ₒ (earlier.obj ⟦Γs⟧ₛ)).inv.app (op n) γ))).down.arrows f :=
        hbr n ((α_ ⟦τ⟧ₜ ⟦Γ⟧ₒ (earlier.obj ⟦Γs⟧ₛ)).inv.app (op n) γ) m f ⟨h1, by
          show ((ConcreteCategory.hom ((pctx Ψs).app (op n)))
              ((ConcreteCategory.hom ((interp_ren_local_weaken interp_ren_id).app (op n)))
                ((α_ ⟦τ⟧ₜ ⟦Γ⟧ₒ (earlier.obj ⟦Γs⟧ₛ)).inv.app (op n) γ))).down.arrows f
          have : (ConcreteCategory.hom ((interp_ren_local_weaken interp_ren_id).app (op n)))
              ((α_ ⟦τ⟧ₜ ⟦Γ⟧ₒ (earlier.obj ⟦Γs⟧ₛ)).inv.app (op n) γ) = γ.2 := hsnd
          rw [this]
          exact h2⟩
      rw [show (ConcreteCategory.hom ((interp_ren_local_weaken interp_ren_id).app (op n)))
          ((α_ ⟦τ⟧ₜ ⟦Γ⟧ₒ (earlier.obj ⟦Γs⟧ₛ)).inv.app (op n) γ) = γ.2 from hsnd] at hb''
      exact hb''
    exact entails_trans _ _ _ (conj_intro hex (entails_refl _))
      (Logic.exist_elim (P := (α_ ⟦τ⟧ₜ ⟦Γ⟧ₒ (earlier.obj ⟦Γs⟧ₛ)).inv ≫ Φ)
        (R := pctx Ψs) (Q := Qi) key)
  lemma intro_lift : (pctx Ψs ⊢ᵢ Φ) → (pctx Ψs ⊢ᵢ (interp_lift (interp_delay ((λ_ _).hom ≫ force.app _ ≫ Φ)))) := by
    intro prf
    exact entails_trans _ _ _ prf (later_intro _)
  lemma loeb_ind : (pctx (((interp_lift (interp_delay ((λ_ _).hom ≫ force.app _ ≫ Φ))) :: Ψ) :: Ψs) ⊢ᵢ Φ) → (pctx (Ψ :: Ψs) ⊢ᵢ Φ) := by
    simp [pctx, poctx]
    intros prf
    apply later_loeb
    apply entails_trans; swap
    . apply prf
    . apply conj_intro
      . apply conj_intro
        . apply conj_elim_l
        . apply entails_trans
          . apply conj_elim_r
          . apply conj_elim_l
      . apply entails_trans
        . apply conj_elim_r
        . apply conj_elim_r

end prf

section interp
  open CategoryTheory
  open CartesianMonoidalCategory
  open Logic

  @[simp]
  def expr_interp (Γ : CTX.{i}) (e : EXPR.{i}) (τ : TYPE.{i}) : Part (⟦Γ⟧ₛ ⟶ ⟦τ⟧ₜ) :=
    match Γ, e, τ with
    | _, .embed A a, TYPE.embed A' =>
      Part.assert (A = A') $ fun Heq =>
      pure (interp_embed A' (cast Heq a))
    | Γ, .embed_apply A B e1 e2, TYPE.embed B' => do
      let e1' ← expr_interp Γ e1 (TYPE.embed (A → B'))
      let e2' ← expr_interp Γ e2 (TYPE.embed A)
      Part.assert (B = B') $ fun _Heq =>
      Pure.pure (interp_embed_apply _ _ e1' e2')
    | Γ, .pure e, TYPE.prop => do
      let e' ← expr_interp Γ e (TYPE.embed Prop)
      pure (interp_pure e')
    | Γ, .var' n m, τ => do
      Part.assert (n < Γ.length) $ fun Hn =>
      Part.assert ((Γ[n]'Hn)[m]? = some τ) $ fun Hm =>
      pure (interp_var n m (getElem?_pos Γ n Hn) Hm)
    | Γ, .app σ e1 e2, τ => do
      let e1' ← expr_interp Γ e1 (TYPE.arr σ τ)
      let e2' ← expr_interp Γ e2 σ
      pure (interp_app e1' e2')
    | Γ :: Γs, .lam' _ e, TYPE.arr τ1 τ2 => do
      let e' ← expr_interp ((τ1 :: Γ) :: Γs) e τ2
      pure (interp_lam e')
    | Γ, .delay e, TYPE.later A => do
      let e' ← expr_interp ([] :: Γ) e A
      pure (interp_delay e')
    | Γ, .adv n e, A =>
      Part.assert (0 < n) $ fun Hlt => do
      let e' ← expr_interp (Γ.drop n) e (TYPE.later A)
      pure (interp_adv n Hlt e')
    | Γ :: Γs, .fix' (TYPE.later _) e, A' => do
      let e' ← expr_interp ((TYPE.later A' :: Γ) :: Γs) e A'
      pure (interp_fix e')
    | Γ, .pair e1 e2, TYPE.prod A B => do
      let e1' ← expr_interp Γ e1 A
      let e2' ← expr_interp Γ e2 B
      pure (interp_pair e1' e2')
    | Γ, .proj B e .L, A => do
      let e' ← expr_interp Γ e (TYPE.prod A B)
      pure (interp_projL e')
    | Γ, .proj A e .R, B => do
      let e' ← expr_interp Γ e (TYPE.prod A B)
      pure (interp_projR e')
    | Γ, .inl Br e, TYPE.sum A B =>
      Part.assert (Br = B) $ fun _ => do
        let e' ← expr_interp Γ e A
        pure (interp_inl (B := B) e')
    | Γ, .inr Al e, TYPE.sum A B =>
      Part.assert (Al = A) $ fun _ => do
        let e' ← expr_interp Γ e B
        pure (interp_inr (A := A) e')
    | Γ, .case A B e f g, C => do
      let e' ← expr_interp Γ e (TYPE.sum A B)
      let f' ← expr_interp Γ f (TYPE.arr A C)
      let g' ← expr_interp Γ g (TYPE.arr B C)
      pure (interp_case e' f' g')
    | Γ, .and e1 e2, TYPE.prop => do
      let e1' ← expr_interp Γ e1 TYPE.prop
      let e2' ← expr_interp Γ e2 TYPE.prop
      pure (interp_and e1' e2')
    | Γ, .or e1 e2, TYPE.prop => do
      let e1' ← expr_interp Γ e1 TYPE.prop
      let e2' ← expr_interp Γ e2 TYPE.prop
      pure (interp_or e1' e2')
    | Γ, .impl e1 e2, TYPE.prop => do
      let e1' ← expr_interp Γ e1 TYPE.prop
      let e2' ← expr_interp Γ e2 TYPE.prop
      pure (interp_impl e1' e2')
    | Γ :: Γs, .forall' A e, TYPE.prop => do
      let e' ← expr_interp ((A :: Γ) :: Γs) e TYPE.prop
      pure (interp_forall e')
    | Γ :: Γs, .exists' A e, TYPE.prop => do
      let e' ← expr_interp ((A :: Γ) :: Γs) e TYPE.prop
      pure (interp_exists e')
    | Γ, .lift e, TYPE.prop => do
      let e' ← expr_interp Γ e (TYPE.later TYPE.prop)
      pure (interp_lift e')
    | _, .true, TYPE.prop =>
      pure interp_true
    | _, .false, TYPE.prop =>
      pure interp_false
    | Γ, .eq A e1 e2, TYPE.prop => do
      let e1' ← expr_interp Γ e1 A
      let e2' ← expr_interp Γ e2 A
      pure (interp_eq e1' e2')
    | Γ, .ax A f, A' =>
      Part.assert (A = A') $ fun Heq => do
      pure (toUnit ⟦Γ⟧ₛ ≫ f ≫ eqToHom (congr_arg interp_ty Heq))
    | _, _, _ =>
      .none

  notation:max "⟦" Γ "," e "," τ "⟧ₑ" => expr_interp Γ e τ

  theorem expr_interp_correct (H : TYPED.{i} Γ e τ) : (expr_interp Γ e τ).Dom := by
    induction H with
    | embed Hlt =>
      simp [expr_interp, Part.assert]
    | embed_apply H1 H2 IH1 IH2 =>
      simp [expr_interp, Part.assert]
      constructor <;> assumption
    | pure H IH =>
      simp [expr_interp]
      assumption
    | var' n m H1 H2 =>
      simp [expr_interp, Part.assert]
      rw [List.getElem?_eq_some_iff] at H1
      let ⟨h, H1⟩ := H1
      exists h
      rw [H1]
      exact H2
    | app H1 H2 IH1 IH2 =>
      simp [expr_interp]
      constructor <;> assumption
    | lam' H IH =>
      simp [expr_interp]; assumption
    | delay Hln H IH =>
      simp [expr_interp]
      assumption
    | adv Hlt H IH =>
      simp [expr_interp, Part.assert]
      constructor <;> assumption
    | fix' H IH =>
      simp [expr_interp]
      assumption
    | pair H1 H2 IH1 IH2 =>
      simp [expr_interp]
      constructor <;> assumption
    | projL H IH =>
      simp [expr_interp]
      assumption
    | projR H IH =>
      simp [expr_interp]
      assumption
    | inl H IH =>
      simp [expr_interp, Part.assert]
      assumption
    | inr H IH =>
      simp [expr_interp, Part.assert]
      assumption
    | case He Hf Hg IHe IHf IHg =>
      simp [expr_interp]
      refine ⟨?_, ?_, ?_⟩ <;> assumption
    | or H1 H2 IH1 IH2 =>
      simp [expr_interp]; constructor <;> assumption
    | and H1 H2 IH1 IH2 =>
      simp [expr_interp]; constructor <;> assumption
    | impl H1 H2 IH1 IH2 =>
      simp [expr_interp]; constructor <;> assumption
    | forall' H IH =>
      simp [expr_interp]
      assumption
    | exists' H IH =>
      simp [expr_interp]
      assumption
    | lift H IH =>
      simp [expr_interp]
      assumption
    | true H =>
      simp [expr_interp]
    | false H =>
      simp [expr_interp]
    | eq H1 H2 IH1 IH2 =>
      simp [expr_interp]
      constructor <;> assumption
    | ax t f Hl =>
      simp [expr_interp, Part.assert]

  def synt_interp (e : SYNT τ) : ⟦[[]]⟧ₛ ⟶ ⟦τ⟧ₜ :=
    (expr_interp _ e.expr τ).get (expr_interp_correct e.proof)

  def interp_typed_ren {Γ Δ : CTX.{i}} {δ : REN}
    (H : TYPED_REN δ Δ Γ) : ⟦Δ⟧ₛ ⟶ ⟦Γ⟧ₛ :=
    match H with
    | .id H => interp_ren_id
    | .comp Hσ' Hσ => interp_ren_comp (interp_typed_ren Hσ) (interp_typed_ren Hσ')
    | .local_weaken _ Hσ => interp_ren_local_weaken (interp_typed_ren Hσ)
    | .cons _ Hσ => interp_ren_cons (interp_typed_ren Hσ)
    | .global_lift Hσ => interp_ren_global_lift (interp_typed_ren Hσ)
    | .global_shift _ Heq Hσ => interp_ren_global_shift Heq (interp_typed_ren Hσ)

  notation:max "⟦" e "⟧ᵣ" => interp_typed_ren e

  def interp_tsubst {Γ : CTX.{i}} {Δ : OCTX.{i}} {σ : SUBST.{i}}
    (H : TSUBST σ Γ Δ) : ⟦Γ⟧ₛ ⟶ ⟦Δ⟧ₒ :=
    match H with
    | .epsilon H => interp_subst_epsilon
    | .cons He Hσ => interp_subst_cons ((expr_interp _ _ _).get (expr_interp_correct He)) (interp_tsubst Hσ)

  notation:max "⟦" e "⟧ₛᵤ" => interp_tsubst e

  def interp_tssubst {Γ Δs : CTX.{i}} {σs : SSUBST.{i}}
    (H : TSSUBST σs Γ Δs) : ⟦Γ⟧ₛ ⟶ ⟦Δs⟧ₛ :=
    match H with
    | .single _ Hσ => interp_ssubst_single (interp_tsubst Hσ)
    | .wk _ Hn Heq Hσs Hσ => interp_ssubst_wk Hn Heq (interp_tssubst Hσs) (interp_tsubst Hσ)

  notation:max "⟦" e "⟧ₛₛ" => interp_tssubst e

  @[simp]
  lemma ren_transport_left_sem (Heq : Γ = Δ) (H : TYPED_REN σ Γ Ψ) :
    ⟦ren_transport_left Heq H⟧ᵣ = eqToHom (Eq.symm (congr_arg interp_ctx Heq)) ≫ ⟦H⟧ᵣ := by
    simp [ren_transport_left]
    cases Heq
    simp

  @[simp]
  lemma ssubst_transport_left_sem (Heq : Γ = Δ) (H : TSSUBST σ Γ Ψ) :
    ⟦ssubst_transport_left Heq H⟧ₛₛ = eqToHom (Eq.symm (congr_arg interp_ctx Heq)) ≫ ⟦H⟧ₛₛ := by
    simp [ssubst_transport_left]
    cases Heq
    simp

  @[simp]
  lemma ssubst_transport_right_sem (Heq : Γ = Δ) (H : TSSUBST σ Ψ Γ) :
    ⟦ssubst_transport_right Heq H⟧ₛₛ = ⟦H⟧ₛₛ ≫ eqToHom (congr_arg interp_ctx Heq) := by
    simp [ssubst_transport_right]
    cases Heq
    simp

end interp
