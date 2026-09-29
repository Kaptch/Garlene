module

public import SynthDom.Interp.Interp

@[expose] public section

section frames
  open CategoryTheory
  open Opposite
  open Functor
  open CartesianMonoidalCategory
  open MonoidalCategory
  open Logic

  @[simp]
  def Presieve_predFunctor {X : ℕ} (S : Presieve (X + 1)) : Presieve X :=
    fun _ f => S (Nat.succ_le_succ f.le).hom

  @[simp]
  def Sieve_predFunctor {X : ℕ} (S : Sieve (X + 1)) : Sieve X :=
    Sieve.mk (arrows := Presieve_predFunctor S) (by
      intro Y Z f prf g
      simp only [Presieve_predFunctor] at prf ⊢
      have h := S.downward_closed prf (Nat.succ_le_succ g.le).hom
      convert h using 1
      apply Subsingleton.elim)

  @[simp]
  def down_app.{i} (X : ℕᵒᵖ) : (earlier.obj.{i} Ω).obj X ⟶ (Ω).obj X :=
    ↾(fun y ↦ ULift.up (Sieve_predFunctor y.down))

  def down.{i} : earlier.obj.{i} Ω ⟶ Ω :=
  {
    app X := down_app X
    naturality {A B} f := by
      ext x
      rfl
  }

  lemma down_app_arrows {n m : ℕ} (S : (earlier.obj.{i} Ω).obj (op n)) (f : m ⟶ n) :
      ((down.app (op n)) S).down.arrows f ↔ S.down.arrows (Nat.succ_le_succ f.le).hom := by
    rfl

  def tick_prop {Γ0 : OCTX.{i}} {Γs : CTX.{i}} (P : ⟦Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
      : ⟦Γ0 :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ :=
    snd ⟦Γ0⟧ₒ (earlier.obj ⟦Γs⟧ₛ) ≫ earlier.map P ≫ down

  def earlier_prop : {Γ : CTX.{i}} → (d : Nat) → (⟦Γ.drop d⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ) → (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
    | _, 0, P => P
    | [], _ + 1, P => P
    | _ :: Γs, d + 1, P => tick_prop (earlier_prop (Γ := Γs) d P)

  @[simp]
  lemma earlier_prop_zero {Γ : CTX.{i}} (P : ⟦Γ.drop 0⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ) :
      earlier_prop 0 P = P := by
    cases Γ <;> rfl

  lemma earlier_prop_zero_fun {Γ : CTX.{i}} :
      earlier_prop (Γ := Γ) 0 = id := funext (fun P => earlier_prop_zero P)

  @[simp]
  lemma earlier_prop_succ {Γ0 : OCTX.{i}} {Γs : CTX.{i}} (d : Nat)
      (P : ⟦(Γ0 :: Γs).drop (d + 1)⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ) :
      earlier_prop (Γ := Γ0 :: Γs) (d + 1) P = tick_prop (earlier_prop (Γ := Γs) d P) := rfl

  lemma tick_prop_app {Γ0 : OCTX.{i}} {Γs : CTX.{i}} (P : ⟦Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
      (n : ℕ) (a : (⟦Γ0⟧ₒ).obj (op n)) (ν : (⟦Γs⟧ₛ).obj (op (n + 1))) {m : ℕ} (f : m ⟶ n) :
      (((tick_prop (Γ0 := Γ0) P).app (op n)) ⟨a, ν⟩).down.arrows f
        ↔ ((P.app (op (n + 1))) ν).down.arrows (Nat.succ_le_succ f.le).hom := by
    rfl

  lemma tick_prop_conj_l {Γ0 : OCTX.{i}} {Γs : CTX.{i}} (P Q : ⟦Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ) :
      tick_prop (Γ0 := Γ0) (P ∧ᵢ Q) ⊢ᵢ (tick_prop P ∧ᵢ tick_prop Q) := by
    intro n γ m f hyp
    obtain ⟨a, ν⟩ := γ
    have h := (tick_prop_app (P ∧ᵢ Q) n a ν f).mp hyp
    erw [conj_app] at h
    simp only [Sieve.inter_apply] at h
    erw [conj_app]
    simp only [Sieve.inter_apply]
    exact ⟨(tick_prop_app P n a ν f).mpr h.1, (tick_prop_app Q n a ν f).mpr h.2⟩

  lemma tick_prop_conj_r {Γ0 : OCTX.{i}} {Γs : CTX.{i}} (P Q : ⟦Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ) :
      (tick_prop (Γ0 := Γ0) P ∧ᵢ tick_prop Q) ⊢ᵢ tick_prop (P ∧ᵢ Q) := by
    intro n γ m f hyp
    obtain ⟨a, ν⟩ := γ
    erw [conj_app] at hyp
    simp only [Sieve.inter_apply] at hyp
    have h1 := (tick_prop_app P n a ν f).mp hyp.1
    have h2 := (tick_prop_app Q n a ν f).mp hyp.2
    refine (tick_prop_app (P ∧ᵢ Q) n a ν f).mpr ?_
    erw [conj_app]
    exact ⟨h1, h2⟩

  lemma tick_prop_true {Γ0 : OCTX.{i}} {Γs : CTX.{i}} {R : ⟦Γ0 :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ} :
      R ⊢ᵢ tick_prop (Γ0 := Γ0) (Γs := Γs) ⊤ᵢ := by
    intro n γ m f _
    obtain ⟨a, ν⟩ := γ
    refine (tick_prop_app ⊤ᵢ n a ν f).mpr ?_
    erw [true_app]
    trivial

  lemma tick_prop_mono {Γ0 : OCTX.{i}} {Γs : CTX.{i}} {P Q : ⟦Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ}
      (h : P ⊢ᵢ Q) : tick_prop (Γ0 := Γ0) P ⊢ᵢ tick_prop Q := by
    intro n γ m f hyp
    obtain ⟨a, ν⟩ := γ
    exact (tick_prop_app Q n a ν f).mpr (h _ _ _ _ ((tick_prop_app P n a ν f).mp hyp))

  lemma tick_prop_entails_force {Γ0 : OCTX.{i}} {Γs : CTX.{i}} (P : ⟦Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ) :
      tick_prop (Γ0 := Γ0) P ⊢ᵢ (snd ⟦Γ0⟧ₒ (earlier.obj ⟦Γs⟧ₛ) ≫ force.app ⟦Γs⟧ₛ ≫ P) := by
    intro n γ m f hyp
    obtain ⟨a, ν⟩ := γ
    have h := (tick_prop_app P n a ν f).mp hyp
    have h1 := (P.app (op (n + 1)) ν).down.downward_closed h (homOfLE (Nat.le_succ m))
    show ((P.app (op n)) ((⟦Γs⟧ₛ).map (op (homOfLE (Nat.le_succ n))) ν)).down.arrows f
    erw [NatTrans.naturality_apply]
    erw [Sieve.pullback_apply]
    convert h1 using 1
    apply Subsingleton.elim

  lemma poctx_map_tick_l {Γ0 : OCTX.{i}} {Γs : CTX.{i}} (Ψ : List (⟦Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)) :
      tick_prop (Γ0 := Γ0) (poctx Ψ) ⊢ᵢ poctx (Ψ.map tick_prop) := by
    induction Ψ with
    | nil => simp only [List.map_nil, poctx]; exact true_intro
    | cons a as IH =>
      simp only [List.map_cons, poctx]
      exact entails_trans _ _ _ (tick_prop_conj_l _ _)
        (conj_intro conj_elim_l (entails_trans _ _ _ conj_elim_r IH))

  lemma poctx_map_tick_r {Γ0 : OCTX.{i}} {Γs : CTX.{i}} (Ψ : List (⟦Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)) :
      poctx (Ψ.map (tick_prop (Γ0 := Γ0))) ⊢ᵢ tick_prop (poctx Ψ) := by
    induction Ψ with
    | nil => simp only [List.map_nil, poctx]; exact tick_prop_true
    | cons a as IH =>
      simp only [List.map_cons, poctx]
      exact entails_trans _ _ _
        (conj_intro conj_elim_l (entails_trans _ _ _ conj_elim_r IH)) (tick_prop_conj_r _ _)

  lemma pctx_map_tick_l {Γ0 : OCTX.{i}} {Γs : CTX.{i}}
      (Ψ : List (List (⟦Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) :
      tick_prop (Γ0 := Γ0) (pctx Ψ) ⊢ᵢ pctx (Ψ.map (fun fr => fr.map tick_prop)) := by
    induction Ψ with
    | nil => simp only [List.map_nil, pctx]; exact true_intro
    | cons a as IH =>
      simp only [List.map_cons, pctx]
      exact entails_trans _ _ _ (tick_prop_conj_l _ _)
        (conj_intro (entails_trans _ _ _ conj_elim_l (poctx_map_tick_l a))
          (entails_trans _ _ _ conj_elim_r IH))

  lemma pctx_map_tick_r {Γ0 : OCTX.{i}} {Γs : CTX.{i}}
      (Ψ : List (List (⟦Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) :
      pctx (Ψ.map (fun fr => fr.map (tick_prop (Γ0 := Γ0)))) ⊢ᵢ tick_prop (pctx Ψ) := by
    induction Ψ with
    | nil => simp only [List.map_nil, pctx]; exact tick_prop_true
    | cons a as IH =>
      simp only [List.map_cons, pctx]
      exact entails_trans _ _ _
        (conj_intro (entails_trans _ _ _ conj_elim_l (poctx_map_tick_r a))
          (entails_trans _ _ _ conj_elim_r IH)) (tick_prop_conj_r _ _)

  lemma later_intro' {Γs : CTX.{i}} (Q : ⟦Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ) :
      Q ⊢ᵢ interp_lift (interp_delay (tick_prop (Γ0 := []) Q)) := by
    have hd : interp_delay (tick_prop (Γ0 := []) Q)
        = (earlier_later_adj.homEquiv ⟦Γs⟧ₛ ⟦TYPE.prop⟧ₜ).toFun (earlier.map Q ≫ down) := by
      simp only [interp_delay, tick_prop]
      congr 1
    rw [hd]
    intro n γ m f hyp
    cases n with
    | zero =>
      simp [interp_lift, lift_subobject_classifier]
      erw [ConcreteCategory.comp_apply, ConcreteCategory.hom_ofHom]
      trivial
    | succ n' =>
      change ((Q.app (op (n' + 1)) γ).down.arrows _ ∨ m = 0)
      cases m with
      | zero => exact Or.inr rfl
      | succ m' => exact Or.inl hyp

  lemma later_elim_sem {Γ0 : OCTX.{i}} {Γs : CTX.{i}} {Q : ⟦Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ}
      {P : ⟦Γs⟧ₛ ⟶ ⟦TYPE.later TYPE.prop⟧ₜ} (h : Q ⊢ᵢ interp_lift P) :
      tick_prop (Γ0 := Γ0) Q ⊢ᵢ (snd ⟦Γ0⟧ₒ (earlier.obj ⟦Γs⟧ₛ)
        ≫ (earlier_later_adj.homEquiv ⟦Γs⟧ₛ ⟦TYPE.prop⟧ₜ).invFun P) := by
    intro n γ m f hyp
    obtain ⟨a, ν⟩ := γ
    have h1 := (tick_prop_app Q n a ν f).mp hyp
    have h2 := h (n + 1) ν (m + 1) (Nat.succ_le_succ f.le).hom h1
    change ((P.app (op (n + 1)) ν).down.arrows _ ∨ m + 1 = 0) at h2
    rcases h2 with h2 | h2
    · simp only [Adjunction.homEquiv, earlier_later_adj, counit_adj, earlier, earlier_arr]
      erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
      cases n <;> exact h2
    · exact absurd h2 (Nat.succ_ne_zero m)

  lemma snd_split_chase {D A B W : ℐ.{i}} (X : ℐ.{i}) (φ : D ⟶ A ⊗ B) (g : earlier.obj A ⟶ W) :
      (X ◁ earlier.map φ ≫ X ◁ earlier_prod.hom.app (A, B))
          ≫ (α_ X (earlier.obj A) (earlier.obj B)).inv
          ≫ (β_ X (earlier.obj A)).hom ▷ earlier.obj B
          ≫ (α_ (earlier.obj A) X (earlier.obj B)).hom
          ≫ fst (earlier.obj A) (X ⊗ earlier.obj B) ≫ g
        = snd X (earlier.obj D) ≫ earlier.map (φ ≫ fst A B) ≫ g := by
    calc (X ◁ earlier.map φ ≫ X ◁ earlier_prod.hom.app (A, B))
            ≫ (α_ X (earlier.obj A) (earlier.obj B)).inv
            ≫ (β_ X (earlier.obj A)).hom ▷ earlier.obj B
            ≫ (α_ (earlier.obj A) X (earlier.obj B)).hom
            ≫ fst (earlier.obj A) (X ⊗ earlier.obj B) ≫ g
        = (X ◁ earlier.map φ ≫ X ◁ earlier_prod.hom.app (A, B))
            ≫ snd X (earlier.obj A ⊗ earlier.obj B)
            ≫ fst (earlier.obj A) (earlier.obj B) ≫ g :=
          whisker_eq _ (cart_tail_chase_assoc X (earlier.obj A) (earlier.obj B) g)
      _ = snd X (earlier.obj D) ≫ earlier.map φ ≫ earlier_prod.hom.app (A, B)
            ≫ fst (earlier.obj A) (earlier.obj B) ≫ g :=
          snd_push_gen φ X (fst (earlier.obj A) (earlier.obj B) ≫ g)
      _ = snd X (earlier.obj D) ≫ earlier.map φ ≫ earlier.map (fst A B) ≫ g :=
          whisker_eq _ (whisker_eq _ (prod_fst_earlier_assoc A B g))
      _ = snd X (earlier.obj D) ≫ earlier.map (φ ≫ fst A B) ≫ g :=
          whisker_eq _ (congrArg (· ≫ g) (earlier.map_comp φ (fst A B)).symm)

  lemma split_cons_succ_fst {x : OCTX.{i}} {xs : CTX.{i}} (d : Nat) {W : ℐ.{i}}
      (g : earlier.obj ((earlier.iter d).obj ⟦xs.drop d⟧ₛ) ⟶ W) :
      (interp_ctx_split (x :: xs) (i := d + 1)).hom ≫ fst _ _ ≫ g
      = snd ⟦x⟧ₒ (earlier.obj ⟦xs⟧ₛ) ≫ earlier.map ((interp_ctx_split xs (i := d)).hom ≫ fst _ _) ≫ g := by
    simp only [interp_ctx_split, Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom,
      Functor.mapIso_hom, MonoidalCategory.whiskerLeft_comp, Category.assoc]
    exact snd_split_chase ⟦x⟧ₒ (interp_ctx_split xs (i := d)).hom g

  lemma split_cons_succ_force {x : OCTX.{i}} {xs : CTX.{i}} (d : Nat) {W : ℐ.{i}}
      (g : ⟦xs.drop d⟧ₛ ⟶ W) :
      (interp_ctx_split (x :: xs) (i := d + 1)).hom ≫ fst _ _ ≫ (n_force (i := d + 1)).app _ ≫ g
      = snd ⟦x⟧ₒ (earlier.obj ⟦xs⟧ₛ) ≫ force.app ⟦xs⟧ₛ
          ≫ (interp_ctx_split xs (i := d)).hom ≫ fst _ _ ≫ (n_force (i := d)).app _ ≫ g := by
    simp only [interp_ctx_split, n_force, Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom,
      Functor.mapIso_hom, MonoidalCategory.whiskerLeft_comp, Category.assoc,
      NatTrans.hcomp_app, Functor.id_map, Functor.comp_obj, Functor.id_obj]
    exact snd_force_chase ⟦x⟧ₒ (interp_ctx_split xs (i := d)).hom ((n_force (i := d)).app _ ≫ g)

  lemma interp_adv_one {Γ0 : OCTX.{i}} {Γs : CTX.{i}} {τ : TYPE.{i}} (h : 0 < 1)
      (P : ⟦Γs⟧ₛ ⟶ ⟦TYPE.later τ⟧ₜ) :
      interp_adv 1 h (Γ := Γ0 :: Γs) P
      = snd ⟦Γ0⟧ₒ (earlier.obj ⟦Γs⟧ₛ) ≫ (earlier_later_adj.homEquiv ⟦Γs⟧ₛ ⟦τ⟧ₜ).invFun P := by
    simp only [interp_adv]
    erw [split_cons_succ_fst 0]
    simp only [n_force_cut, n_force, interp_ctx_split_zero, Iso.symm_hom]
    erw [rightUnitor_inv_fst]
    rfl

  lemma earlier_prop_entails_nforce :
      ∀ {Γ : CTX.{i}} (d : Nat), d < Γ.length → ∀ (P : ⟦Γ.drop d⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ),
      earlier_prop d P ⊢ᵢ ((interp_ctx_split Γ (i := d)).hom ≫ fst _ _ ≫ (n_force (i := d)).app _ ≫ P)
    | Γ, 0, _, P => by
      simp only [earlier_prop_zero, interp_ctx_split_zero, Iso.symm_hom]
      intro n γ m f hyp
      exact hyp
    | [], d + 1, hd, P => by simp at hd
    | x :: xs, d + 1, hd, P => by
      erw [split_cons_succ_force, earlier_prop_succ]
      have IH := earlier_prop_entails_nforce (Γ := xs) d (by simp at hd; omega) P
      exact entails_trans _ _ _ (tick_prop_mono IH) (tick_prop_entails_force _)

  lemma local_weaken_tick {τ : TYPE.{i}} {Γ0 : OCTX.{i}} {Γs : CTX.{i}}
      (P : ⟦Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ) :
      interp_ren_local_weaken (τ := τ) (Ψ := Γ0) (Φ := Γ0) (Γs := Γs) (Δs := Γs) (𝟙 _)
        ≫ tick_prop (Γ0 := Γ0) P
      = tick_prop (Γ0 := τ :: Γ0) P := by
    simp only [interp_ren_local_weaken, tick_prop]
    erw [Category.comp_id]
    simp only [Category.assoc]
    erw [associator_hom_snd_snd_assoc]

  lemma earlier_prop_mono : ∀ {Γ : CTX.{i}} (n : Nat) {P Q : ⟦Γ.drop n⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ},
      (P ⊢ᵢ Q) → earlier_prop n P ⊢ᵢ earlier_prop n Q
    | Γ, 0, _, _, h => by cases Γ <;> exact h
    | [], _ + 1, _, _, h => h
    | _ :: _, d + 1, _, _, h => tick_prop_mono (earlier_prop_mono d h)

  lemma pctx_drop_entails {Γ : CTX.{i}} :
      ∀ (n : Nat) (V : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))), pctx V ⊢ᵢ pctx (V.drop n)
    | 0, _ => entails_refl _
    | _ + 1, [] => entails_refl _
    | n + 1, _ :: as => by
      simp only [List.drop_succ_cons, pctx]
      exact entails_trans _ _ _ conj_elim_r (pctx_drop_entails n as)

  lemma pctx_map_id_entails {Γ : CTX.{i}} (f : (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ) → (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))
      (hf : f = id) (W : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) :
      pctx (W.map (fun fr => fr.map f)) ⊢ᵢ pctx W := by
    subst hf
    simp only [List.map_id, List.map_id']
    exact entails_refl _

  lemma map_earlier_prop_succ {x : OCTX.{i}} {xs : CTX.{i}} (d : Nat)
      (fr : List (⟦(x :: xs).drop (d + 1)⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)) :
      List.map (tick_prop (Γ0 := x)) (List.map (earlier_prop (Γ := xs) d) fr)
        = List.map (earlier_prop (Γ := x :: xs) (d + 1)) fr := by
    induction fr with
    | nil => rfl
    | cons a as IH => exact congrArg (List.cons _) IH

  lemma pctx_map_earlier_r : ∀ {Γ : CTX.{i}} (n : Nat), n ≤ Γ.length →
      ∀ (W : List (List (⟦Γ.drop n⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))),
      pctx (W.map (fun fr => fr.map (earlier_prop n))) ⊢ᵢ earlier_prop n (pctx W)
    | _, 0, _, W => by
      rw [earlier_prop_zero]
      exact pctx_map_id_entails _ earlier_prop_zero_fun W
    | [], _ + 1, h, _ => by simp at h
    | x :: xs, d + 1, h, W => by
      have IH := pctx_map_earlier_r (Γ := xs) d (by simp at h; omega) W
      have h1 := pctx_map_tick_r (Γ0 := x) (W.map (fun fr => fr.map (earlier_prop d)))
      have h2 := tick_prop_mono (Γ0 := x) IH
      rw [earlier_prop_succ]
      refine entails_trans _ _ _ ?_ (entails_trans _ _ _ h1 h2)
      simp only [List.map_map, Function.comp_def, map_earlier_prop_succ]
      exact entails_refl _

  lemma interp_adv_succ_frame {x : OCTX.{i}} {xs : CTX.{i}} {τ : TYPE.{i}} (n : Nat) (h : 0 < n + 1)
      (P : ⟦xs.drop n⟧ₛ ⟶ ⟦TYPE.later τ⟧ₜ) :
      interp_adv (n + 1) h (Γ := x :: xs) P
      = snd ⟦x⟧ₒ (earlier.obj ⟦xs⟧ₛ) ≫ (earlier_later_adj.homEquiv ⟦xs⟧ₛ ⟦τ⟧ₜ).invFun
          ((interp_ctx_split xs (i := n)).hom ≫ fst _ _ ≫ (n_force (i := n)).app _ ≫ P) := by
    simp only [interp_adv]
    erw [split_cons_succ_fst n]

  lemma earlier_prop_later_elim : ∀ {Γ : CTX.{i}} (n : Nat) (hn : 0 < n), n < Γ.length →
      ∀ {Q : ⟦Γ.drop n⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ} {P : ⟦Γ.drop n⟧ₛ ⟶ ⟦TYPE.later TYPE.prop⟧ₜ},
      (Q ⊢ᵢ interp_lift P) → earlier_prop n Q ⊢ᵢ interp_adv n hn P
    | [], _, _, hΓ, _, _, _ => by simp at hΓ
    | _ :: _, 0, hn, _, _, _, _ => absurd hn (Nat.lt_irrefl 0)
    | _ :: xs, n + 1, hn, hΓ, Q, P, h => by
      erw [interp_adv_succ_frame n hn]
      rw [earlier_prop_succ]
      apply later_elim_sem
      refine entails_trans _ _ _ (earlier_prop_entails_nforce (Γ := xs) n (by simp at hΓ; omega) Q) ?_
      simp only [interp_lift, Category.assoc]
      exact entails_subst _ _ _ (entails_subst _ _ _ (entails_subst _ _ _ h))

end frames
