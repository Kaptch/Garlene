module

public import SynthDom.Syntax.Prf.Core

@[expose] public section

section interp
  open CategoryTheory
  open Opposite
  open Functor
  open CartesianMonoidalCategory
  open MonoidalCategory

  attribute [local implicit_reducible] Functor.iter List.drop List.take

  @[reassoc (attr := simp)]
  private lemma rightUnitor_inv_fst_drop_zero (Γ : CTX.{i}) :
      (ρ_ ⟦Γ⟧ₛ).inv ≫ fst ⟦List.drop 0 Γ⟧ₛ (𝟙_ ℐ) = 𝟙 ⟦Γ⟧ₛ := by
    change ((ρ_ ⟦Γ⟧ₛ).inv ≫ fst ⟦Γ⟧ₛ (𝟙_ ℐ) = 𝟙 ⟦Γ⟧ₛ)
    exact rightUnitor_inv_fst _

  @[reassoc (attr := simp)]
  private lemma rightUnitor_inv_fst_cons (Γ : OCTX.{i}) (Γs : CTX.{i}) :
      (ρ_ (⟦Γ⟧ₒ ⊗ earlier.obj ⟦Γs⟧ₛ)).inv
        ≫ fst ⟦List.drop 0 (Γ :: Γs)⟧ₛ (𝟙_ ℐ) = 𝟙 _ := by
    change ((ρ_ (⟦Γ⟧ₒ ⊗ earlier.obj ⟦Γs⟧ₛ)).inv
      ≫ fst (⟦Γ⟧ₒ ⊗ earlier.obj ⟦Γs⟧ₛ) (𝟙_ ℐ) = 𝟙 _)
    exact rightUnitor_inv_fst _

  private lemma rightUnitor_inv_fst_single (Γ : OCTX.{i}) :
      (ρ_ (⟦Γ⟧ₒ ⊗ earlier.obj (𝟙_ ℐ))).inv
        ≫ fst ⟦List.drop 0 [Γ]⟧ₛ (𝟙_ ℐ) = 𝟙 _ := by
    exact rightUnitor_inv_fst _

  private lemma interp_delay_naturality { Δ Γ : CTX.{i} } {τ : TYPE.{i}}
      (f : ⟦Δ⟧ₛ ⟶ ⟦Γ⟧ₛ) (e : ⟦[] :: Γ⟧ₛ ⟶ ⟦τ⟧ₜ) :
      interp_delay (interp_ren_global_lift f ≫ e) = f ≫ interp_delay e := by
    unfold interp_delay interp_ren_global_lift
    simp only [interp_ctx, interp_octx]
    refine Eq.trans (congrArg (earlier_later_adj.homEquiv ⟦Δ⟧ₛ ⟦τ⟧ₜ) ?_)
      (earlier_later_adj.homEquiv_naturality_left f
        ((λ_ (earlier.obj ⟦Γ⟧ₛ)).inv ≫ e))
    simp only [id_tensorHom]
    rw [← leftUnitor_inv_naturality_assoc]

  private lemma interp_var_congr {Γ : CTX.{i}} {Ψ Ψ' : OCTX.{i}} {τ : TYPE.{i}} {a a' b b' : Nat}
    (ha : a = a') (hb : b = b') (hΨ : Ψ = Ψ')
    (h1 : Γ[a]? = some Ψ) (h2 : Ψ[b]? = some τ)
    {h1' : Γ[a']? = some Ψ'} {h2' : Ψ'[b']? = some τ} :
    interp_var a b h1 h2 = interp_var a' b' h1' h2' := by
    cases ha; cases hb; cases hΨ; rfl

  private lemma whiskerLeft_reassoc_fst_fst {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {A B B' X X' T : C} (f : B ⊗ X ⟶ B' ⊗ X') (g : B' ⟶ T) (g' : B ⟶ T)
    (hyp : f ≫ fst B' X' ≫ g = fst B X ≫ g') :
    (α_ A B X).hom ≫ A ◁ f ≫ (α_ A B' X').inv ≫ fst (A ⊗ B') X' ≫ snd A B' ≫ g
    = fst (A ⊗ B) X ≫ snd A B ≫ g' := by
    calc (α_ A B X).hom ≫ A ◁ f ≫ (α_ A B' X').inv ≫ fst (A ⊗ B') X' ≫ snd A B' ≫ g
        = (α_ A B X).hom ≫ A ◁ f ≫ snd A (B' ⊗ X') ≫ fst B' X' ≫ g := by
          rw [associator_inv_fst_snd_assoc]
      _ = (α_ A B X).hom ≫ snd A (B ⊗ X) ≫ f ≫ fst B' X' ≫ g := by
          rw [whiskerLeft_snd_assoc]
      _ = (α_ A B X).hom ≫ snd A (B ⊗ X) ≫ fst B X ≫ g' := by
          rw [hyp]
      _ = fst (A ⊗ B) X ≫ snd A B ≫ g' := by
          rw [associator_hom_snd_fst_assoc]

  private lemma whiskerLeft_reassoc_fst_snd {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {A B B' X X' T : C} (f : B ⊗ X ⟶ B' ⊗ X') (g : B' ⟶ T) (w : X ⟶ T)
    (hyp : f ≫ fst B' X' ≫ g = snd B X ≫ w) :
    (α_ A B X).hom ≫ A ◁ f ≫ (α_ A B' X').inv ≫ fst (A ⊗ B') X' ≫ snd A B' ≫ g
    = snd (A ⊗ B) X ≫ w := by
    calc (α_ A B X).hom ≫ A ◁ f ≫ (α_ A B' X').inv ≫ fst (A ⊗ B') X' ≫ snd A B' ≫ g
        = (α_ A B X).hom ≫ A ◁ f ≫ snd A (B' ⊗ X') ≫ fst B' X' ≫ g := by
          rw [associator_inv_fst_snd_assoc]
      _ = (α_ A B X).hom ≫ snd A (B ⊗ X) ≫ f ≫ fst B' X' ≫ g := by
          rw [whiskerLeft_snd_assoc]
      _ = (α_ A B X).hom ≫ snd A (B ⊗ X) ≫ snd B X ≫ w := by
          rw [hyp]
      _ = snd (A ⊗ B) X ≫ w := by
          rw [associator_hom_snd_snd_assoc]

  private lemma whiskerLeft_reassoc_snd_fst {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {A B B' X X' T : C} (f : B ⊗ X ⟶ B' ⊗ X') (w' : X' ⟶ T) (g' : B ⟶ T)
    (hyp : f ≫ snd B' X' ≫ w' = fst B X ≫ g') :
    (α_ A B X).hom ≫ A ◁ f ≫ (α_ A B' X').inv ≫ snd (A ⊗ B') X' ≫ w'
    = fst (A ⊗ B) X ≫ snd A B ≫ g' := by
    calc (α_ A B X).hom ≫ A ◁ f ≫ (α_ A B' X').inv ≫ snd (A ⊗ B') X' ≫ w'
        = (α_ A B X).hom ≫ A ◁ f ≫ snd A (B' ⊗ X') ≫ snd B' X' ≫ w' := by
          rw [associator_inv_snd_assoc]
      _ = (α_ A B X).hom ≫ snd A (B ⊗ X) ≫ f ≫ snd B' X' ≫ w' := by
          rw [whiskerLeft_snd_assoc]
      _ = (α_ A B X).hom ≫ snd A (B ⊗ X) ≫ fst B X ≫ g' := by
          rw [hyp]
      _ = fst (A ⊗ B) X ≫ snd A B ≫ g' := by
          rw [associator_hom_snd_fst_assoc]

  private lemma whiskerLeft_reassoc_snd_snd {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {A B B' X X' T : C} (f : B ⊗ X ⟶ B' ⊗ X') (w' : X' ⟶ T) (w : X ⟶ T)
    (hyp : f ≫ snd B' X' ≫ w' = snd B X ≫ w) :
    (α_ A B X).hom ≫ A ◁ f ≫ (α_ A B' X').inv ≫ snd (A ⊗ B') X' ≫ w'
    = snd (A ⊗ B) X ≫ w := by
    calc (α_ A B X).hom ≫ A ◁ f ≫ (α_ A B' X').inv ≫ snd (A ⊗ B') X' ≫ w'
        = (α_ A B X).hom ≫ A ◁ f ≫ snd A (B' ⊗ X') ≫ snd B' X' ≫ w' := by
          rw [associator_inv_snd_assoc]
      _ = (α_ A B X).hom ≫ snd A (B ⊗ X) ≫ f ≫ snd B' X' ≫ w' := by
          rw [whiskerLeft_snd_assoc]
      _ = (α_ A B X).hom ≫ snd A (B ⊗ X) ≫ snd B X ≫ w := by
          rw [hyp]
      _ = snd (A ⊗ B) X ≫ w := by
          rw [associator_hom_snd_snd_assoc]

  private lemma snd_force_naturality {P Q T : ℐ.{u}} (f : P ⟶ Q) (u : Q ⟶ T) (v : P ⟶ T) (hyp : f ≫ u = v) :
    (𝟙 (𝟙_ ℐ.{u}) ⊗ₘ earlier.map f) ≫ snd (𝟙_ ℐ.{u}) (earlier.obj Q) ≫ force.app Q ≫ u
    = snd (𝟙_ ℐ.{u}) (earlier.obj P) ≫ force.app P ≫ v := by
    have hnat := force.naturality f
    dsimp only [Functor.id_obj, Functor.id_map] at hnat
    have e1 : (𝟙 (𝟙_ ℐ.{u}) ⊗ₘ earlier.map f) ≫ snd (𝟙_ ℐ.{u}) (earlier.obj Q)
        = snd (𝟙_ ℐ.{u}) (earlier.obj P) ≫ earlier.map f := tensorHom_snd _ _
    calc (𝟙 (𝟙_ ℐ.{u}) ⊗ₘ earlier.map f) ≫ snd (𝟙_ ℐ.{u}) (earlier.obj Q) ≫ force.app Q ≫ u
        = ((𝟙 (𝟙_ ℐ.{u}) ⊗ₘ earlier.map f) ≫ snd (𝟙_ ℐ.{u}) (earlier.obj Q)) ≫ force.app Q ≫ u :=
          (Category.assoc _ _ _).symm
      _ = (snd (𝟙_ ℐ.{u}) (earlier.obj P) ≫ earlier.map f) ≫ force.app Q ≫ u :=
          congrArg (· ≫ force.app Q ≫ u) e1
      _ = snd (𝟙_ ℐ.{u}) (earlier.obj P) ≫ earlier.map f ≫ force.app Q ≫ u :=
          Category.assoc _ _ _
      _ = snd (𝟙_ ℐ.{u}) (earlier.obj P) ≫ force.app P ≫ v :=
          whisker_eq _ (by
            calc earlier.map f ≫ force.app Q ≫ u
                = (earlier.map f ≫ force.app Q) ≫ u := (Category.assoc _ _ _).symm
              _ = (force.app P ≫ f) ≫ u := congrArg (· ≫ u) hnat
              _ = force.app P ≫ f ≫ u := Category.assoc _ _ _
              _ = force.app P ≫ v := whisker_eq _ hyp)

  theorem eq_weak_var {σ : REN} {Γ Δ : CTX.{i}} (Ψ Ψ' : OCTX.{i}) (τ : TYPE.{i})
  (n m : Nat)
  (Hσ : TYPED_REN σ Γ Δ)
  (Hn : Δ[n]? = some Ψ) (Hm : Ψ[m]? = some τ)
  (Hn' : Γ[(weaken_var' σ n m).fst]? = some Ψ')(Hm' : Ψ'[(weaken_var' σ n m).snd]? = some τ)
  : ⟦Hσ⟧ᵣ ≫ (interp_var n m Hn Hm) =
    (interp_var (τ := τ) (weaken_var' σ n m).fst (weaken_var' σ n m).snd Hn' Hm') := by
    revert n m τ Ψ Ψ' Hn Hm Hn' Hm'
    induction Hσ with
    | id _ =>
      intro Ψ Ψ' τ n m Hn Hm Hn' Hm'
      simp [interp_var, interp_typed_ren, interp_ren_id]
      simp at Hn' Hm'
      have HEQ1 : Ψ = Ψ' := by
        rw [Hn'] at Hn; simp at Hn; symm; assumption
      cases HEQ1
      rfl
    | @comp σ' _ _ σ _ H1 H2 IH1 IH2 =>
      intro Ψ Ψ' τ n m Hn Hm Hn' Hm'
      simp [interp_typed_ren, interp_ren_comp]
      simp [weaken_var'] at Hn' Hm'
      obtain ⟨P1, ⟨P2, P3⟩⟩ := weaken_var'_correct σ' n m H1 _ _ Hn Hm
      rw [IH1 _ _ _ _ _ Hn Hm P2 P3]
      rw [IH2]
    | @local_weaken σ' Ψ'' Δ' Ψ''' Γ' τ' Hσ IH =>
      intro Ψ Ψ' τ n m Hn Hm Hn' Hm'
      simp only [weaken_var']
      simp at Hn' Hm'
      obtain ⟨P1, ⟨P2, P3⟩⟩ := weaken_var'_correct σ' n m Hσ _ _ Hn Hm
      simp [interp_typed_ren, interp_ren_local_weaken]
      have hlt1 : (weaken_var' σ' n m).1 < ((τ' :: Ψ'') :: Δ').length := by
        rw [getElem?_eq_some_iff] at Hn'
        exact Hn'.fst
      have heq1 : ((τ' :: Ψ'') :: Δ')[(weaken_var' σ' n m).1] = Ψ' := by
        apply Option.some_inj.mp
        rw [←Hn']
        simp
      cases heq1
      generalize_proofs
      revert Hn' Hm' hlt1
      cases h : (weaken_var' σ' n m) with | mk p1 p2 =>
      have h1 : p1 = (weaken_var' σ' n m).1 := by rw [h]
      have h2 : p2 = (weaken_var' σ' n m).2 := by rw [h]
      simp
      intro hlt1 Hm'
      cases p1 with
      | zero =>
        simp; simp at Hm'
        have IH' : ⟦Hσ⟧ᵣ ≫ interp_var n m Hn Hm = interp_var 0 p2 (Eq.refl _) Hm' :=
          (IH _ _ _ _ _ Hn Hm P2 P3).trans
            (interp_var_congr h1.symm h2.symm
              (by apply Option.some_inj.mp; rw [←P2, ←h1]; simp) P2 P3)
        refine Eq.trans (whisker_eq _ (whisker_eq _ IH')) ?_
        exact associator_hom_snd_fst_assoc ⟦τ'⟧ₜ ⟦Ψ''⟧ₒ (earlier.obj ⟦Δ'⟧ₛ)
          (octx_proj Ψ'' p2 τ Hm')
      | succ p1' =>
        simp; simp at Hm'
        have IH' : ⟦Hσ⟧ᵣ ≫ interp_var n m Hn Hm = interp_var (p1' + 1) p2 (by simp) Hm' :=
          (IH _ _ _ _ _ Hn Hm P2 P3).trans
            (interp_var_congr h1.symm h2.symm
              (by apply Option.some_inj.mp; rw [←P2, ←h1]; simp) P2 P3)
        refine Eq.trans (whisker_eq _ (whisker_eq _ IH')) ?_
        exact associator_hom_snd_snd_assoc ⟦τ'⟧ₜ ⟦Ψ''⟧ₒ (earlier.obj ⟦Δ'⟧ₛ)
          (force.app ⟦Δ'⟧ₛ ≫ ctx_proj Δ' p1' (Δ'[p1']) (by simp) ≫ octx_proj (Δ'[p1']) p2 τ Hm')
    | @cons σ' Ψ' Δ' Ψ'' Δ'' τ' Hσ IH =>
      intro Ψ''' Ψ'''' τ n m Hn Hm Hn' Hm'
      simp only [interp_typed_ren, interp_ren_cons]
      cases n with
      | zero =>
        simp
        simp at Hn
        cases Hn
        cases m with
        | zero =>
          simp
          simp [weaken_var'] at Hn'
          cases Hn'
          simp at Hm
          cases Hm
          simp [weaken_var'] at Hm'
          cases Hm'
          rfl
        | succ m' =>
          simp
          generalize_proofs hp1 hp2
          revert hp1 hp2
          cases h : (weaken_var' σ' 0 m') with | mk p1 p2 =>
          have h1 : p1 = (weaken_var' σ' 0 m').1 := by rw [h]
          have h2 : p2 = (weaken_var' σ' 0 m').2 := by rw [h]
          simp
          cases h3 : p1 with
          | zero =>
            simp
            intro hp1; cases hp1
            simp at Hm Hm' Hn'
            simp
            revert Hn' Hm'
            rw [h]; simp
            rw [h3]; simp
            intro hp2
            have IH2 : ⟦Hσ⟧ᵣ ≫ interp_var 0 m' (Eq.refl _) Hm
                = interp_var (Γ := Ψ' :: Δ') 0 p2 (Eq.refl _) hp2 :=
              (IH Ψ'' Ψ' τ 0 m' (Eq.refl _) Hm (by rw [←h1, h3]; simp) (by rw [←h2]; exact hp2)).trans
                (interp_var_congr (h1.symm.trans h3) h2.symm rfl _ _)
            exact whiskerLeft_reassoc_fst_fst ⟦Hσ⟧ᵣ (octx_proj Ψ'' m' τ Hm) (octx_proj Ψ' p2 τ hp2) IH2
          | succ p1' =>
            simp
            intro hp1 hp2
            have IH2 : ⟦Hσ⟧ᵣ ≫ interp_var 0 m' (Eq.refl _) Hm
                = interp_var (Γ := Ψ' :: Δ') (p1' + 1) p2 (by simpa using hp1) hp2 :=
              (IH Ψ'' Ψ'''' τ 0 m' (Eq.refl _) Hm
                (by rw [←h1, h3]; simp; exact hp1) (by rw [←h2]; exact hp2)).trans
                (interp_var_congr (h1.symm.trans h3) h2.symm rfl _ _)
            exact whiskerLeft_reassoc_fst_snd ⟦Hσ⟧ᵣ (octx_proj Ψ'' m' τ Hm)
              (force.app ⟦Δ'⟧ₛ ≫ ctx_proj Δ' p1' Ψ'''' hp1 ≫ octx_proj Ψ'''' p2 τ hp2) IH2
      | succ n' =>
        simp
        generalize_proofs hp1 hp2
        revert hp1 hp2
        cases h : (weaken_var' σ' (n' + 1) m) with | mk p1 p2 =>
        have h1 : p1 = (weaken_var' σ' (n' + 1) m).1 := by rw [h]
        have h2 : p2 = (weaken_var' σ' (n' + 1) m).2 := by rw [h]
        simp
        cases h3 : p1 with
        | zero =>
          simp
          intro hp1; cases hp1
          simp at Hm Hm' Hn'
          simp
          revert Hn' Hm'
          rw [h]; simp
          rw [h3]; simp
          intro hp2
          have IH2 : ⟦Hσ⟧ᵣ ≫ interp_var (n' + 1) m Hn Hm
              = interp_var (Γ := Ψ' :: Δ') 0 p2 (Eq.refl _) hp2 :=
            (IH Ψ''' Ψ' τ (n' + 1) m Hn Hm (by rw [←h1, h3]; rfl) (by rw [←h2]; exact hp2)).trans
              (interp_var_congr (h1.symm.trans h3) h2.symm rfl _ _)
          exact whiskerLeft_reassoc_snd_fst ⟦Hσ⟧ᵣ
            (force.app ⟦Δ''⟧ₛ ≫ ctx_proj Δ'' n' Ψ''' Hn ≫ octx_proj Ψ''' m τ Hm)
            (octx_proj Ψ' p2 τ hp2) IH2
        | succ p1' =>
          simp
          intro hp1 hp2
          have IH2 : ⟦Hσ⟧ᵣ ≫ interp_var (n' + 1) m Hn Hm
              = interp_var (Γ := Ψ' :: Δ') (p1' + 1) p2 (by simpa using hp1) hp2 :=
            (IH Ψ''' Ψ'''' τ (n' + 1) m Hn Hm
              (by rw [←h1, h3]; exact hp1) (by rw [←h2]; exact hp2)).trans
              (interp_var_congr (h1.symm.trans h3) h2.symm rfl _ _)
          exact whiskerLeft_reassoc_snd_snd ⟦Hσ⟧ᵣ
            (force.app ⟦Δ''⟧ₛ ≫ ctx_proj Δ'' n' Ψ''' Hn ≫ octx_proj Ψ''' m τ Hm)
            (force.app ⟦Δ'⟧ₛ ≫ ctx_proj Δ' p1' Ψ'''' hp1 ≫ octx_proj Ψ'''' p2 τ hp2) IH2
    | @global_lift _ Γ' _ H IH =>
      intros Ψ' Ψ'' τ m p Hn Hm Hp Hk
      cases m with
      | zero =>
        simp at Hn; cases Hn
        exfalso; simp at Hm
      | succ m' =>
        exact snd_force_naturality ⟦H⟧ᵣ (interp_var m' p (by simpa using Hn) Hm) _
          (IH Ψ' Ψ'' τ m' p (by simpa using Hn) Hm (by simpa using Hp) (by simpa using Hk))
    | @global_shift _ Γ' _ Ψ n Hlen H IH =>
      intros Ψ' Ψ'' τ m p Hn Hm Hp Hk
      simp [interp_typed_ren, interp_ren_global_shift, interp_var]
      simp at Hn Hk Hp
      specialize (IH Ψ' Ψ'' τ m p Hn Hm
          (by
            rw [Hlen, List.getElem?_append_right] at Hp
            . simp at Hp; exact Hp
            . simp) Hk)
      simp [interp_var] at IH
      rw [IH]; clear IH
      repeat rw [←Category.assoc]
      congr 1; simp
      clear Hk Hm Hn
      cases Hlen
      have hdrop : ⟦List.drop (List.length Ψ) (Ψ ++ Γ')⟧ₛ = ⟦Γ'⟧ₛ :=
        congrArg interp_ctx
          (by simp : List.drop (List.length Ψ) (Ψ ++ Γ') = Γ')
      rw [← eqToHom_map (earlier.iter Ψ.length) hdrop]
      erw [reassoc_of% (n_force (i := Ψ.length)).naturality
        (eqToHom hdrop)]
      exact ctx_proj_append Γ' (weaken_var' _ m p).1 Ψ'' _ Ψ _
        hdrop

  def pctx_interp (Γ : CTX.{i}) (Ψ : PCTX.{i}) : Part (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ) :=
    let t := (Ψ.mapM (fun Ψ' => (Ψ'.mapM (fun e => expr_interp Γ e TYPE.prop))))
    let r := t.map (fun lst => pctx lst)
    r

  lemma weaken_var_expl1 (H1 : TYPED_REN σ Δ Γ) (H2 : (weaken_var' σ n m).1 < List.length Δ) (H3 : ¬n < List.length Γ)
    : False := by
    revert H2 H3 n m
    induction H1 with
    | id H =>
      intro n m H2 H3
      simp at H2
      grind only
    | comp G1 G2 IH1 IH2 =>
      intro n m H2 H3
      simp at H2
      grind only
    | local_weaken τ G IH =>
      intro n m H2 H3
      simp at H2
      grind only [= List.length_cons]
    | cons τ G IH =>
      intro n m H2 H3
      simp at H2
      grind only [= List.length_cons]
    | global_lift G IH =>
      intro n m H2 H3
      simp at H2
      grind
    | global_shift n Hl G IH =>
      intro n m H2 H3
      simp at H2
      grind only

  lemma weaken_var_first_correct (H1 : TYPED_REN σ Δ Γ) (H2 : n < List.length Γ) : (weaken_var' σ n m).1 < List.length Δ := by
    revert H2 n m
    induction H1 with
    | id H =>
      intro n m H2
      simp
      grind only
    | comp G1 G2 IH1 IH2 =>
      intro n m H2
      simp
      grind only
    | local_weaken τ G IH =>
      intro n m H2
      simp
      grind only [= List.length_cons]
    | cons τ G IH =>
      intro n m H2
      simp
      cases n with
      | zero =>
        cases m with
        | zero => simp
        | succ m' =>
          simp
          grind only [= List.length_cons]
      | succ n' =>
        simp
        grind only [= List.length_cons]
    | global_lift G IH =>
      intro n m H2
      simp
      cases n with
      | zero =>
        cases m with
        | zero =>
          simp
        | succ m' =>
          simp
      | succ n' =>
        simp
        grind only [= List.length_cons]
    | global_shift n Hl G IH =>
      intro n m H2
      simp
      grind only

  lemma weaken_var_expl2 (H1 : TYPED_REN σ Δ Γ)
  (H2 : (weaken_var' σ n m).1 < List.length Δ) (H3 : n < List.length Γ)
  (H4 : List.length Γ[n] ≤ m)
    : List.length Δ[(weaken_var' σ n m).1] ≤ (weaken_var' σ n m).2 := by
    revert H2 H3 H4 n m
    induction H1 with
    | id H =>
      intro n m H2 H3 H4
      simp_all
    | @comp _ _ Ψ _ _ G1 G2 IH1 IH2 =>
      intro n m H2 H3 H4
      simp_all
      apply IH2
      . apply IH1
        . apply H4
      . apply weaken_var_first_correct
        . assumption
        . assumption
    | @local_weaken σ' Ψ Γ' _ _ τ G IH =>
      simp
      intro n m
      generalize_proofs p q
      revert p q
      cases h : (weaken_var' σ' n m) with | mk p1 p2 =>
      intro p q H3 H4
      simp only [] at *
      revert q
      intro q
      split
      · grind only [= List.getElem_cons_zero, = List.getElem_cons, = List.length_cons]
      · grind only [= List.getElem_cons_succ, = List.getElem_cons, = List.length_cons]
    | @cons σ' _ _ _ _ τ G IH =>
      simp
      intro n m H2 H3 H4
      cases n with
      | zero =>
        simp
        cases m with
        | zero =>
          simp at H4
        | succ m' =>
          simp at H4
          simp
          generalize_proofs p
          revert p
          cases h : (weaken_var' σ' 0 m') with | mk p1 p2 =>
          cases p1 with
          | zero =>
            intro p
            simp
            grind only [= List.getElem_cons_zero, = List.getElem_cons, = List.length_cons]
          | succ p1' =>
            intro p
            simp
            grind only [= List.getElem_cons_zero, = List.getElem_cons_succ, = List.getElem_cons,
              = List.length_cons]
      | succ n' =>
        simp
        generalize_proofs p
        revert p
        cases h : (weaken_var' σ' (n' + 1) m) with | mk p1 p2 =>
        simp
        cases p1 with
        | zero =>
          intro p
          simp
          grind only [= List.getElem_cons_zero, = List.getElem_cons_succ, = List.getElem_cons,
            = List.length_cons]
        | succ p1' =>
          intro p
          simp
          grind only [= List.getElem_cons_succ, = List.getElem_cons, = List.length_cons]
    | @global_lift _ _ _ G IH =>
      intro n m H2 H3 H4
      cases n with
      | zero =>
        simp
      | succ n' =>
        cases m with
        | zero =>
          simp
          dsimp at H4
          grind only [= List.length_append, = List.getElem_append, cases Or]
        | succ m' =>
          simp
          dsimp at H4
          grind only [= List.length_append, = List.getElem_append, cases Or]
    | global_shift n Hl G IH =>
      intro n m H2 H3 H4
      simp_all

  lemma eq_weak_embed (H : TYPED_REN σ Δ Γ)
    : ⟦Δ,weaken (EXPR.embed A a) σ,τ⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦Γ,EXPR.embed A a,τ⟧ₑ := by
    simp only [weaken]
    cases τ with
    | embed A' =>
      ext γ
      simp [expr_interp, Part.map, Part.assert]
      constructor
      . intro ⟨g, G⟩; exists g
      . intro ⟨g, G⟩; exists g
    | _ => simp

  lemma eq_weak_embed_apply (H : TYPED_REN σ Δ Γ)
    (IH1 : ⟦Δ,weaken a σ,(TYPE.embed (A → B))⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦Γ,a,(TYPE.embed (A → B))⟧ₑ)
    (IH2 : ⟦Δ,weaken b σ,(TYPE.embed A)⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦Γ,b,(TYPE.embed A)⟧ₑ)
    : ⟦Δ,weaken (EXPR.embed_apply A B a b) σ,(TYPE.embed B)⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦Γ,EXPR.embed_apply A B a b,(TYPE.embed B)⟧ₑ := by
    simp only [weaken]
    simp [expr_interp, interp_embed_apply]
    rw [IH1, IH2]
    rfl

  lemma eq_weak_pure (H : TYPED_REN σ Δ Γ)
    (IH : ⟦Δ,weaken a σ,(TYPE.embed Prop)⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦Γ,a,(TYPE.embed Prop)⟧ₑ)
    : ⟦Δ,weaken (EXPR.pure a) σ,TYPE.prop⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦Γ,(EXPR.pure a),TYPE.prop⟧ₑ := by
    simp only [weaken]
    simp [expr_interp, Part.map]
    rw [IH]
    simp [Part.map, Part.bind]
    ext γ
    constructor
    . intro ⟨g, G⟩
      simp [Part.assert] at g G
      rw [←G]
      simp [Part.assert]
      exists g
    . intro ⟨g, G⟩
      simp at g
      simp
      exists g.1
      rw [←G]
      simp
      rfl

  lemma eq_weak_var' (H : TYPED_REN σ Δ Γ)
    : ⟦Δ,weaken (EXPR.var' n m) σ,τ⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦Γ,EXPR.var' n m,τ⟧ₑ := by
    simp [weaken]
    ext γ
    constructor
    . intro G
      simp at G
      let ⟨G1, ⟨G2, G3⟩⟩ := G
      rw [G3]
      by_cases J1 : n < Γ.length
      . by_cases J2 : m < Γ[n].length
        . obtain ⟨Ψ, J1, J2⟩ := weaken_var'_correct σ n m H Γ[n] Γ[n][m] (by simp) (by simp)
          obtain rfl : Γ[n][m] = τ := by
            apply Option.some_inj.mp
            rw [←J2, ←G2]
            grind
          rw [←eq_weak_var Γ[n] Δ[(weaken_var' σ n m).1] Γ[n][m] n m H (by simp) (by simp)]
          simp
          grind
        . exfalso
          have Hm : (weaken_var' σ n m).2 < Δ[(weaken_var' σ n m).1].length := by
            grind only [→ List.getElem_of_getElem?, = List.getElem?_eq_none, = getElem?_pos,
              = getElem?_neg]
          simp at J2
          have E := weaken_var_expl2 H G1 J1 J2
          grind only
      . exfalso
        apply weaken_var_expl1; assumption
        . apply G1
        . apply J1
    . intro G
      simp [Part.map, Part.assert] at G
      let ⟨⟨G1, G2⟩, G3⟩ := G
      rw [←G3]
      simp
      obtain ⟨Ψ, J1, J2⟩ := weaken_var'_correct σ n m H Γ[n] τ (by simp) G2
      exists (by grind)
      exists (by grind)
      rw [←eq_weak_var]

  lemma eq_weak_app (H : TYPED_REN σ Δ Γ)
    (IH1 : ⟦Δ,weaken a σ,(A.arr τ)⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦Γ,a,(A.arr τ)⟧ₑ)
    (IH2 : ⟦Δ,weaken b σ,A⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦Γ,b,A⟧ₑ)
    : ⟦Δ,weaken (EXPR.app A a b) σ,τ⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦Γ,EXPR.app A a b,τ⟧ₑ := by
    simp only [weaken]
    simp [expr_interp]
    rw [IH1, IH2]
    rfl

  lemma eq_weak_lam (H : TYPED_REN σ (Δ :: Δs) (Γ :: Γs))
    (IH : ⟦((B :: Δ) :: Δs),weaken a σ.cons,C⟧ₑ = Part.map (fun x ↦ ⟦H.cons B⟧ᵣ ≫ x) ⟦((B :: Γ) :: Γs),a,C⟧ₑ)
    : ⟦(Δ :: Δs),weaken (EXPR.lam' A a) σ,(TYPE.arr B C)⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦(Γ :: Γs),EXPR.lam' A a,(TYPE.arr B C)⟧ₑ := by
    simp only [weaken]
    simp [expr_interp]
    rw [IH]
    simp [interp_typed_ren, interp_ren_cons]
    ext γ
    simp
    constructor
    . intro ⟨a, ⟨G, HEQ⟩⟩
      rw [HEQ]
      exists a
      refine ⟨G, ?_⟩
      simp only [interp_lam, interp_ctx, interp_octx, Iso.inv_hom_id_assoc,
        MonoidalClosed.curry_natural_left]
    . intro ⟨a, ⟨G, HEQ⟩⟩
      rw [HEQ]
      exists a
      refine ⟨G, ?_⟩
      simp only [interp_lam, interp_ctx, interp_octx, Iso.inv_hom_id_assoc,
        MonoidalClosed.curry_natural_left]

  lemma eq_weak_delay (H : TYPED_REN σ Δ Γ)
    (IH : ⟦[] :: Δ,weaken a (REN.global_lift σ),A⟧ₑ = Part.map (fun x ↦ ⟦H.global_lift⟧ᵣ ≫ x) ⟦[] :: Γ,a,A⟧ₑ)
    : ⟦Δ,weaken (EXPR.delay a) σ,TYPE.later A⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦Γ,(EXPR.delay a),TYPE.later A⟧ₑ := by
    simp only [weaken]
    simp [expr_interp]
    rw [IH]; clear IH
    simp [interp_typed_ren, interp_ren_global_lift, Part.bind]
    simp [Part.assert]
    simp [interp_ctx, interp_octx]
    apply heq_of_eq
    funext ha
    exact interp_delay_naturality ⟦H⟧ᵣ _

  lemma interp_adv_succ (Γ : OCTX.{i}) (Γs : CTX.{i}) (τ : TYPE.{i})
    (n : Nat)
    (G : 0 < n + 1)
    (e : ⟦(Γ :: Γs).drop (n + 1)⟧ₛ ⟶ ⟦TYPE.later τ⟧ₜ)
    : interp_adv (Γ := Γ :: Γs) (τ := τ) (n + 1) G e =
      (interp_ctx_split (Γ :: Γs) (i := n + 1)).hom
      ≫ fst _ _
      ≫ earlier.map ((n_force (i := n)).app _)
      ≫ ((earlier_later_adj.homEquiv ⟦List.drop n Γs⟧ₛ ⟦τ⟧ₜ).invFun e) := by
      simp [interp_adv, n_force_cut]
      rfl

  lemma interp_adv_add (Γs : CTX.{i}) (Γs' : CTX.{i}) (τ : TYPE.{i})
    (n : Nat)
    (G : 0 < Γs.length + n)
    (e : ⟦(Γs ++ Γs').drop (Γs.length + n)⟧ₛ ⟶ ⟦TYPE.later τ⟧ₜ)
    : interp_adv (Γ := Γs ++ Γs') (τ := τ) (Γs.length + n) G e =
      (interp_ctx_split (Γs ++ Γs') (i := Γs.length + n)).hom
      ≫ fst _ _
      ≫ (n_force_cut G).app _
      ≫ ((earlier_later_adj.homEquiv _ ⟦τ⟧ₜ).invFun e) := by
      simp [interp_adv, n_force_cut]

  lemma interp_adv_succ' (Γ : OCTX.{i}) (Γs : CTX.{i}) (τ : TYPE.{i})
    (n : Nat)
    (G : 0 < 1 + n)
    (e : ⟦(Γ :: Γs).drop (1 + n)⟧ₛ ⟶ ⟦TYPE.later τ⟧ₜ)
    : interp_adv (Γ := Γ :: Γs) (τ := τ) (1 + n) G e =
      (interp_ctx_split (Γ :: Γs) (i := n + 1)).hom
      ≫ fst _ _
      ≫ earlier.map ((n_force (i := n)).app _)
      ≫ ((earlier_later_adj.homEquiv ⟦List.drop n Γs⟧ₛ ⟦τ⟧ₜ).invFun (eqToHom (congr_arg interp_ctx (by rw [Nat.add_comm]; simp)) ≫ e)) := by
      simp [interp_adv, n_force_cut]
      generalize_proofs p
      revert e G p
      set t := 1 + n
      have heq : t = n + 1 := by subst t; rw [Nat.add_comm]
      clear_value t
      revert heq
      cases t with
      | zero =>
        intro heq G; exfalso; simp at G
      | succ t =>
        simp
        intro heq e G
        subst heq
        rfl

  lemma cut_ren_typing_zero (Hσ : TYPED_REN σ Γ Δ) (G : 0 < Δ.length)
    : ⟦cut_ren_typing σ Hσ 0 G⟧ᵣ = eqToHom (by rw [offset_ren_zero]; simp) ≫ ⟦Hσ⟧ᵣ := by
    cases Hσ <;> simp [cut_ren_typing]

  private lemma split_cons_fst' (x : OCTX.{i}) (xs : CTX.{i}) (k : Nat) :
      (interp_ctx_split (x :: xs) (i := k + 1)).hom
        ≫ fst ((earlier.iter (k + 1)).obj ⟦List.drop (k + 1) (x :: xs)⟧ₛ) ⟦List.take (k + 1) (x :: xs)⟧ₛ
      = snd ⟦x⟧ₒ (earlier.obj ⟦xs⟧ₛ)
        ≫ earlier.map ((interp_ctx_split xs (i := k)).hom
            ≫ fst ((earlier.iter k).obj ⟦List.drop k xs⟧ₛ) ⟦List.take k xs⟧ₛ) := by
    show (⟦x⟧ₒ ◁ earlier.map (interp_ctx_split xs (i := k)).hom
          ≫ ⟦x⟧ₒ ◁ earlier_prod.hom.app ((earlier.iter k).obj ⟦List.drop k xs⟧ₛ, ⟦List.take k xs⟧ₛ)
          ≫ (α_ ⟦x⟧ₒ (earlier.obj ((earlier.iter k).obj ⟦List.drop k xs⟧ₛ)) (earlier.obj ⟦List.take k xs⟧ₛ)).inv
          ≫ (β_ ⟦x⟧ₒ (earlier.obj ((earlier.iter k).obj ⟦List.drop k xs⟧ₛ))).hom ▷ earlier.obj ⟦List.take k xs⟧ₛ
          ≫ (α_ (earlier.obj ((earlier.iter k).obj ⟦List.drop k xs⟧ₛ)) ⟦x⟧ₒ (earlier.obj ⟦List.take k xs⟧ₛ)).hom)
          ≫ fst (earlier.obj ((earlier.iter k).obj ⟦List.drop k xs⟧ₛ)) (⟦x⟧ₒ ⊗ earlier.obj ⟦List.take k xs⟧ₛ)
        = snd ⟦x⟧ₒ (earlier.obj ⟦xs⟧ₛ)
          ≫ earlier.map ((interp_ctx_split xs (i := k)).hom
              ≫ fst ((earlier.iter k).obj ⟦List.drop k xs⟧ₛ) ⟦List.take k xs⟧ₛ)
    have eqL := congrArg
      ((⟦x⟧ₒ ◁ earlier.map (interp_ctx_split xs (i := k)).hom
        ≫ ⟦x⟧ₒ ◁ earlier_prod.hom.app ((earlier.iter k).obj ⟦List.drop k xs⟧ₛ, ⟦List.take k xs⟧ₛ)) ≫ ·)
      (cart_tail_chase ⟦x⟧ₒ (earlier.obj ((earlier.iter k).obj ⟦List.drop k xs⟧ₛ))
        (earlier.obj ⟦List.take k xs⟧ₛ))
    simp only [Category.assoc] at eqL ⊢
    refine eqL.trans ?_; clear eqL
    refine (snd_push_gen (interp_ctx_split xs (i := k)).hom ⟦x⟧ₒ
      (fst (earlier.obj ((earlier.iter k).obj ⟦List.drop k xs⟧ₛ)) (earlier.obj ⟦List.take k xs⟧ₛ))).trans ?_
    refine congrArg (snd ⟦x⟧ₒ (earlier.obj ⟦xs⟧ₛ) ≫ ·) ?_
    refine (whisker_eq (earlier.map (interp_ctx_split xs (i := k)).hom)
      (prod_fst_earlier ((earlier.iter k).obj ⟦List.drop k xs⟧ₛ) ⟦List.take k xs⟧ₛ)).trans ?_
    rw [← earlier.map_comp]

  private lemma lw_head_strip {Z : ℐ.{i}} (τ : TYPE.{i}) (Ψ : OCTX.{i}) (Γ : CTX.{i}) (p : Nat)
      (hp : 0 < p) (heq : ⟦List.drop p ((τ :: Ψ) :: Γ)⟧ₛ = ⟦List.drop p (Ψ :: Γ)⟧ₛ)
      (h : (earlier.iter p).obj ⟦List.drop p (Ψ :: Γ)⟧ₛ ⟶ Z) :
      (interp_ctx_split ((τ :: Ψ) :: Γ) (i := p)).hom
          ≫ fst ((earlier.iter p).obj ⟦List.drop p ((τ :: Ψ) :: Γ)⟧ₛ) ⟦List.take p ((τ :: Ψ) :: Γ)⟧ₛ
          ≫ (earlier.iter p).map (eqToHom heq) ≫ h
      = (α_ ⟦τ⟧ₜ ⟦Ψ⟧ₒ (earlier.obj ⟦Γ⟧ₛ)).hom ≫ snd ⟦τ⟧ₜ ⟦Ψ :: Γ⟧ₛ
          ≫ (interp_ctx_split (Ψ :: Γ) (i := p)).hom
          ≫ fst ((earlier.iter p).obj ⟦List.drop p (Ψ :: Γ)⟧ₛ) ⟦List.take p (Ψ :: Γ)⟧ₛ ≫ h := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
    subst hk
    rw [List.drop_succ_cons, List.drop_succ_cons] at heq
    revert h
    simp only [List.take_succ_cons, Nat.succ_eq_add_one]
    intro h
    have hL : (interp_ctx_split ((τ :: Ψ) :: Γ) (i := k + 1)).hom
          ≫ fst ((earlier.iter (k + 1)).obj ⟦List.drop k Γ⟧ₛ) ⟦(τ :: Ψ) :: List.take k Γ⟧ₛ
          ≫ (earlier.iter (k + 1)).map (eqToHom heq) ≫ h
        = snd ⟦τ :: Ψ⟧ₒ (earlier.obj ⟦Γ⟧ₛ)
          ≫ earlier.map ((interp_ctx_split Γ (i := k)).hom
              ≫ fst ((earlier.iter k).obj ⟦List.drop k Γ⟧ₛ) ⟦List.take k Γ⟧ₛ) ≫ h := by
      refine (congrArg (· ≫ (earlier.iter (k + 1)).map (eqToHom heq) ≫ h)
        (split_cons_fst' (τ :: Ψ) Γ k)).trans ?_
      rw [Subsingleton.elim heq rfl, eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp]
      exact Category.assoc _ _ _
    refine hL.trans ?_; clear hL
    refine Eq.trans ?_ (congrArg
      (fun t => (α_ ⟦τ⟧ₜ ⟦Ψ⟧ₒ (earlier.obj ⟦Γ⟧ₛ)).hom ≫ snd ⟦τ⟧ₜ ⟦Ψ :: Γ⟧ₛ ≫ t ≫ h)
      (split_cons_fst' Ψ Γ k)).symm
    exact (associator_hom_snd_snd_assoc ⟦τ⟧ₜ ⟦Ψ⟧ₒ (earlier.obj ⟦Γ⟧ₛ)
      (earlier.map ((interp_ctx_split Γ (i := k)).hom
          ≫ fst ((earlier.iter k).obj ⟦List.drop k Γ⟧ₛ) ⟦List.take k Γ⟧ₛ) ≫ h)).symm

  private lemma global_lift_split_core (Ψ Γ : CTX.{i}) (m P : ℕ)
      (hP : m + 1 ≤ P)
      (p3 : m + 1 ≤ List.length Ψ + P)
      (p4 : (⟦List.drop (List.length Ψ + P) (Ψ ++ Γ)⟧ₛ : ℐ.{i}) = ⟦List.drop P Γ⟧ₛ)
      (p5 : (⟦List.drop (List.length Ψ) (Ψ ++ Γ)⟧ₛ : ℐ.{i}) = ⟦Γ⟧ₛ) :
      (((interp_ctx_split (Ψ ++ Γ) (i := List.length Ψ + P)).hom
            ≫ fst ((earlier.iter (List.length Ψ + P)).obj ⟦List.drop (List.length Ψ + P) (Ψ ++ Γ)⟧ₛ)
                ⟦List.take (List.length Ψ + P) (Ψ ++ Γ)⟧ₛ)
          ≫ (nm_force_cut p3).app ⟦List.drop (List.length Ψ + P) (Ψ ++ Γ)⟧ₛ)
        ≫ (earlier.iter (m + 1)).map (eqToHom p4)
      = ((((((interp_ctx_split (Ψ ++ Γ) (i := List.length Ψ)).hom
                  ≫ fst ((earlier.iter (List.length Ψ)).obj ⟦List.drop (List.length Ψ) (Ψ ++ Γ)⟧ₛ)
                      ⟦List.take (List.length Ψ) (Ψ ++ Γ)⟧ₛ)
                ≫ n_force.app ⟦List.drop (List.length Ψ) (Ψ ++ Γ)⟧ₛ)
              ≫ eqToHom p5)
            ≫ (interp_ctx_split Γ (i := P)).hom)
          ≫ fst ((earlier.iter P).obj ⟦List.drop P Γ⟧ₛ) ⟦List.take P Γ⟧ₛ)
        ≫ (nm_force_cut hP).app ⟦List.drop P Γ⟧ₛ := by
    rw [show p3 = le_trans hP (le_add_left (le_refl _)) from rfl]
    rw [← nm_force_cut_trans hP (le_add_left (le_refl _))]
    rw [NatTrans.comp_app]
    rw [← Category.assoc _ ((nm_force_cut (le_add_left (le_refl _))).app
          ⟦List.drop (List.length Ψ + P) (Ψ ++ Γ)⟧ₛ)]
    rw [Category.assoc _ _ ((earlier.iter (m + 1)).map (eqToHom p4))]
    have heq : (nm_force_cut hP).app ⟦List.drop (List.length Ψ + P) (Ψ ++ Γ)⟧ₛ
          ≫ (earlier.iter (m + 1)).map (eqToHom p4)
        = eqToHom (congrArg (earlier.iter P).obj p4)
          ≫ (nm_force_cut hP).app ⟦List.drop P Γ⟧ₛ := by
      rw [← eqToHom_map (earlier.iter P) p4]
      exact ((nm_force_cut hP).naturality (eqToHom p4)).symm
    rw [heq]; clear heq
    rw [← Category.assoc _ _ ((nm_force_cut hP).app ⟦List.drop P Γ⟧ₛ)]
    congr 1
    rw [Category.assoc (interp_ctx_split (Ψ ++ Γ)).hom]
    rw [interp_ctx_split_add'' Ψ Γ P (le_add_left (le_refl _))]
    simp
    congr 1
    rw [eqToHom_map]; rw [eqToHom_trans]
    rw [← Category.assoc, ← Category.assoc]; simp
    generalize_proofs q1 q2
    clear p4
    revert q1 q2 p5
    have hlist : List.drop (List.length Ψ) (Ψ ++ Γ) = Γ := by simp
    rw [hlist]
    intro p5 q2 q1
    cases p5
    cases q2
    cases q1
    rfl

  private lemma cons_reshape_abs {C : Type*} [Category C] [CartesianMonoidalCategory C]
      {A B B' X X' T : C} (f : B ⊗ X ⟶ B' ⊗ X') (w : X' ⟶ T) :
      A ◁ f ≫ (α_ A B' X').inv ≫ snd (A ⊗ B') X' ≫ w
      = snd A (B ⊗ X) ≫ f ≫ snd B' X' ≫ w := by
    rw [associator_inv_snd_assoc, whiskerLeft_snd_assoc]

  private lemma cons_rhs_reshape {Ψ Φ : OCTX.{i}} {Γ Δ : CTX.{i}} {τ : TYPE.{i}} (k : Nat)
      (φ : ⟦Ψ :: Γ⟧ₛ ⟶ ⟦Φ :: Δ⟧ₛ) :
      ⟦τ⟧ₜ ◁ φ ≫ (α_ ⟦τ⟧ₜ ⟦Φ⟧ₒ (earlier.obj ⟦Δ⟧ₛ)).inv
        ≫ (interp_ctx_split ((τ :: Φ) :: Δ) (i := k + 1)).hom
        ≫ fst ((earlier.iter (k + 1)).obj ⟦List.drop (k + 1) ((τ :: Φ) :: Δ)⟧ₛ)
            ⟦List.take (k + 1) ((τ :: Φ) :: Δ)⟧ₛ
      = snd ⟦τ⟧ₜ (⟦Ψ⟧ₒ ⊗ earlier.obj ⟦Γ⟧ₛ) ≫ φ
        ≫ (interp_ctx_split (Φ :: Δ) (i := k + 1)).hom
        ≫ fst ((earlier.iter (k + 1)).obj ⟦List.drop (k + 1) (Φ :: Δ)⟧ₛ) ⟦List.take (k + 1) (Φ :: Δ)⟧ₛ := by
    refine Eq.trans (congrArg
      (fun t => ⟦τ⟧ₜ ◁ φ ≫ (α_ ⟦τ⟧ₜ ⟦Φ⟧ₒ (earlier.obj ⟦Δ⟧ₛ)).inv ≫ t)
      (split_cons_fst' (τ :: Φ) Δ k)) ?_
    refine Eq.trans (cons_reshape_abs φ
      (earlier.map ((interp_ctx_split Δ (i := k)).hom
        ≫ fst ((earlier.iter k).obj ⟦List.drop k Δ⟧ₛ) ⟦List.take k Δ⟧ₛ))) ?_
    exact congrArg (fun t => snd ⟦τ⟧ₜ (⟦Ψ⟧ₒ ⊗ earlier.obj ⟦Γ⟧ₛ) ≫ φ ≫ t)
      (split_cons_fst' Φ Δ k).symm

  private lemma nm_force_cut_succ_shift {m off : Nat} (H : m + 1 ≤ off + 1) (H' : m ≤ off)
      (X : ℐ.{i}) :
      (nm_force_cut H).app X = earlier.map ((nm_force_cut H').app X) := by
    show (NatTrans.hcomp (nm_force_cut H') (𝟙 earlier)).app X = _
    simp

  private lemma global_lift_whisker_abs {C : Type*} [Category C] [CartesianMonoidalCategory C]
      {A Y Z W : C} (f : Y ⟶ Z) (g : Z ⟶ W) :
      A ◁ f ≫ snd A Z ≫ g = snd A Y ≫ f ≫ g := by
    rw [whiskerLeft_snd_assoc]

  private lemma global_lift_reshape (x : OCTX.{i}) {Γ Δ : CTX.{i}} (k : Nat) (φ : ⟦Γ⟧ₛ ⟶ ⟦Δ⟧ₛ) :
      ⟦x⟧ₒ ◁ earlier.map φ ≫ (interp_ctx_split (x :: Δ) (i := k + 1)).hom
        ≫ fst ((earlier.iter (k + 1)).obj ⟦List.drop (k + 1) (x :: Δ)⟧ₛ) ⟦List.take (k + 1) (x :: Δ)⟧ₛ
      = snd ⟦x⟧ₒ (earlier.obj ⟦Γ⟧ₛ)
        ≫ earlier.map (φ ≫ (interp_ctx_split Δ (i := k)).hom
            ≫ fst ((earlier.iter k).obj ⟦List.drop k Δ⟧ₛ) ⟦List.take k Δ⟧ₛ) := by
    refine Eq.trans (congrArg (fun t => ⟦x⟧ₒ ◁ earlier.map φ ≫ t) (split_cons_fst' x Δ k)) ?_
    refine Eq.trans (global_lift_whisker_abs (earlier.map φ)
      (earlier.map ((interp_ctx_split Δ (i := k)).hom
        ≫ fst ((earlier.iter k).obj ⟦List.drop k Δ⟧ₛ) ⟦List.take k Δ⟧ₛ))) ?_
    exact congrArg (fun t => snd ⟦x⟧ₒ (earlier.obj ⟦Γ⟧ₛ) ≫ t) (earlier.map_comp _ _).symm

  lemma cut_ren_split_fst {σ : REN} {Δ Γ : CTX.{i}} (H : TYPED_REN σ Δ Γ) :
      ∀ (m : Nat) (G2 : m < Γ.length) (p3 : m ≤ offset_ren σ m),
      (((interp_ctx_split Δ (i := offset_ren σ m)).hom
            ≫ fst ((earlier.iter (offset_ren σ m)).obj ⟦List.drop (offset_ren σ m) Δ⟧ₛ)
              ⟦List.take (offset_ren σ m) Δ⟧ₛ)
          ≫ (nm_force_cut p3).app ⟦List.drop (offset_ren σ m) Δ⟧ₛ)
        ≫ (earlier.iter m).map ⟦cut_ren_typing σ H m G2⟧ᵣ
      = (⟦H⟧ᵣ ≫ (interp_ctx_split Γ (i := m)).hom)
        ≫ fst ((earlier.iter m).obj ⟦List.drop m Γ⟧ₛ) ⟦List.take m Γ⟧ₛ := by
    induction H with
    | id =>
      intro m
      cases m with
      | zero =>
        simp [interp_typed_ren, interp_ren_id, cut_ren_typing, nm_force_zero, n_force]
      | succ m =>
        intro p1 p2
        simp [cut_ren_typing]
        simp [interp_typed_ren, interp_ren_id, nm_force_cut_id]
    | @comp σ _ _ σ' _ H1 H2 IH1 IH2 =>
      intro m
      cases m with
      | zero =>
        simp [interp_typed_ren, interp_ren_comp, cut_ren_typing, nm_force_zero, n_force]
        intro p1; clear p1
        rfl
      | succ m =>
        intro p1 p2
        simp [cut_ren_typing]
        simp [interp_typed_ren, interp_ren_comp]
        simp at p2
        specialize (IH1 (m + 1) p1); simp at IH1
        rw [←IH1]; swap
        . exact offset_ren_ge _ _
        . clear IH1
          erw [←Category.assoc, ←Category.assoc, ←Category.assoc, ←Category.assoc, ←Category.assoc, ←Category.assoc]
          congr 1
          specialize (IH2 (offset_ren σ (m + 1)) (offset_ren_len _ H1 _ p1)
            (offset_ren_ge _ (offset_ren σ (m + 1))))
          simp at IH2
          rw [Category.assoc ⟦H2⟧ᵣ]
          rw [←IH2]; clear IH2
          simp
          congr 1
          simp only [← Category.assoc]
          congr 1
          rw [←CategoryTheory.NatTrans.comp_app]
          congr 1
          symm
          exact nm_force_cut_trans _ _
    | @local_weaken σ' Ψ Γ _ _ τ H IH' =>
      intro m
      cases m with
      | zero =>
        simp [interp_typed_ren, interp_ren_local_weaken, cut_ren_typing, nm_force_zero, n_force]
        rfl
      | succ m =>
        intro p1 p2
        simp [cut_ren_typing]
        simp [interp_typed_ren, interp_ren_local_weaken]
        specialize (IH' (m + 1) p1 p2)
        simp at IH'
        refine Eq.trans ?_ (whisker_eq _ (whisker_eq _ IH')); clear IH'
        have hpos : 0 < offset_ren σ' (m + 1) := offset_ren_pos σ' (m + 1) (by omega)
        have heq : ⟦List.drop (offset_ren σ' (m + 1)) ((τ :: Ψ) :: Γ)⟧ₛ
                 = ⟦List.drop (offset_ren σ' (m + 1)) (Ψ :: Γ)⟧ₛ := by
          obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
          rw [hk, List.drop_succ_cons, List.drop_succ_cons]
        refine Eq.trans ?_ (lw_head_strip τ Ψ Γ (offset_ren σ' (m + 1)) hpos heq
          ((nm_force_cut p2).app ⟦List.drop (offset_ren σ' (m + 1)) (Ψ :: Γ)⟧ₛ
            ≫ earlier.map ((earlier.iter m).map ⟦cut_ren_typing σ' H (m + 1) p1⟧ᵣ)))
        refine congrArg (fun t => (interp_ctx_split ((τ :: Ψ) :: Γ) (i := offset_ren σ' (m + 1))).hom
            ≫ fst ((earlier.iter (offset_ren σ' (m + 1))).obj
                ⟦List.drop (offset_ren σ' (m + 1)) ((τ :: Ψ) :: Γ)⟧ₛ)
                ⟦List.take (offset_ren σ' (m + 1)) ((τ :: Ψ) :: Γ)⟧ₛ ≫ t) ?_
        exact congrArg (· ≫ earlier.map ((earlier.iter m).map ⟦cut_ren_typing σ' H (m + 1) p1⟧ᵣ))
          ((nm_force_cut p2).naturality (eqToHom heq)).symm
    | @cons σ Ψ Γ Φ Δ τ H IH =>
      intro m
      cases m with
      | zero =>
        simp [interp_typed_ren, interp_ren_cons, cut_ren_typing, nm_force_zero, n_force]
        rfl
      | succ m =>
        intro p1 p2
        simp [cut_ren_typing]
        simp [interp_typed_ren, interp_ren_cons]
        simp at p2
        specialize (IH (m + 1) p1 p2)
        simp at IH
        refine Eq.trans ?_ (congrArg (fun t => (α_ ⟦τ⟧ₜ ⟦Ψ⟧ₒ (earlier.obj ⟦Γ⟧ₛ)).hom ≫ t)
          (cons_rhs_reshape m ⟦H⟧ᵣ)).symm
        refine Eq.trans ?_ (whisker_eq _ (whisker_eq _ IH))
        have hpos : 0 < offset_ren σ (m + 1) := offset_ren_pos σ (m + 1) (by omega)
        have heqd : ⟦List.drop (offset_ren σ (m + 1)) ((τ :: Ψ) :: Γ)⟧ₛ
                  = ⟦List.drop (offset_ren σ (m + 1)) (Ψ :: Γ)⟧ₛ := by
          obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
          rw [hk, List.drop_succ_cons, List.drop_succ_cons]
        refine Eq.trans ?_ (lw_head_strip τ Ψ Γ (offset_ren σ (m + 1)) hpos heqd
          ((nm_force_cut p2).app ⟦List.drop (offset_ren σ (m + 1)) (Ψ :: Γ)⟧ₛ
            ≫ earlier.map ((earlier.iter m).map ⟦cut_ren_typing σ H (m + 1) p1⟧ᵣ)))
        refine congrArg (fun t => (interp_ctx_split ((τ :: Ψ) :: Γ) (i := offset_ren σ (m + 1))).hom
            ≫ fst ((earlier.iter (offset_ren σ (m + 1))).obj
                ⟦List.drop (offset_ren σ (m + 1)) ((τ :: Ψ) :: Γ)⟧ₛ)
                ⟦List.take (offset_ren σ (m + 1)) ((τ :: Ψ) :: Γ)⟧ₛ ≫ t) ?_
        exact congrArg (· ≫ earlier.map ((earlier.iter m).map ⟦cut_ren_typing σ H (m + 1) p1⟧ᵣ))
          ((nm_force_cut p2).naturality (eqToHom heqd)).symm
    | @global_lift σ Γ Δ H IH =>
      intro m p1 p2
      simp [cut_ren_typing, interp_typed_ren, interp_ren_global_lift]
      cases m with
      | zero =>
        simp [interp_octx, interp_ctx, interp_ctx_split]
        simp [interp_typed_ren, interp_ren_global_lift, interp_octx]
        rw [nm_force_cut_id]; simp
        erw [rightUnitor_inv_fst_cons_assoc]
      | succ m =>
        revert p1 p2; simp
        intro p1 p2
        specialize (IH m p1 p2)
        simp at IH
        generalize_proofs pnf pcut
        refine Eq.trans ?_ (global_lift_reshape [] m ⟦H⟧ᵣ).symm
        refine Eq.trans (congrArg
          (· ≫ (nm_force_cut pnf).app ⟦List.drop (offset_ren σ m) Γ⟧ₛ
              ≫ earlier.map ((earlier.iter m).map ⟦cut_ren_typing σ H m pcut⟧ᵣ))
          (split_cons_fst' [] Γ (offset_ren σ m))) ?_
        refine Eq.trans (Category.assoc _ _ _) ?_
        refine congrArg (fun t => snd ⟦([] : OCTX)⟧ₒ (earlier.obj ⟦Γ⟧ₛ) ≫ t) ?_
        refine Eq.trans (congrArg
          (fun t => earlier.map ((interp_ctx_split Γ (i := offset_ren σ m)).hom
              ≫ fst ((earlier.iter (offset_ren σ m)).obj ⟦List.drop (offset_ren σ m) Γ⟧ₛ)
                  ⟦List.take (offset_ren σ m) Γ⟧ₛ)
            ≫ t ≫ earlier.map ((earlier.iter m).map ⟦cut_ren_typing σ H m pcut⟧ᵣ))
          (nm_force_cut_succ_shift pnf p2 ⟦List.drop (offset_ren σ m) Γ⟧ₛ)) ?_
        rw [← earlier.map_comp, ← earlier.map_comp]
        exact congrArg (earlier.map ·) IH
    | @global_shift σ Γ Δ Ψ n J H IH =>
      intro m
      cases m with
      | zero =>
        simp [interp_typed_ren, interp_ren_global_shift, cut_ren_typing, nm_force_zero, n_force]
        intro p1
        simp [interp_ctx]
      | succ m =>
        subst J
        simp [interp_typed_ren, interp_ren_global_shift, cut_ren_typing]
        intro p1 p2
        specialize (IH (m + 1) p1
          (offset_ren_ge _ (m + 1)))
        simp at IH
        rw [←IH]; clear IH
        erw [←Category.assoc, ←Category.assoc, ←Category.assoc, ←Category.assoc
          , ←Category.assoc, ←Category.assoc, ←Category.assoc, ←Category.assoc
          , ←Category.assoc]
        congr 1
        have p5' : (⟦List.drop (List.length Ψ) (Ψ ++ Γ)⟧ₛ : ℐ) = ⟦Γ⟧ₛ := by simp
        generalize_proofs p3 p4 p5
        clear H
        clear p1
        revert p2 p3 p4 p5
        set p := offset_ren σ (m + 1)
        clear_value p
        intro p2 p3 p4 p5
        rename_i hP hp
        rw [show eqToHom p5 = (earlier.iter Ψ.length).map (eqToHom p5') from by
          rw [← eqToHom_map]]
        rw [Category.assoc _ ((earlier.iter Ψ.length).map (eqToHom p5'))
          (n_force.app ⟦Γ⟧ₛ)]
        rw [(n_force (i := Ψ.length)).naturality]
        exact global_lift_split_core Ψ Γ m (offset_ren σ (m + 1)) hP p3 p4 p5'
  lemma eq_weak_adv (H : TYPED_REN σ Δ Γ)
    (G2 : n + 1 < List.length Γ)
    (IH : ⟦List.drop (offset_ren σ (n + 1)) Δ,weaken a (cut_ren σ (n + 1)),TYPE.later τ⟧ₑ
      = Part.map (fun x ↦ ⟦cut_ren_typing σ H (n + 1) G2⟧ᵣ ≫ x) ⟦Γ.drop (n + 1),a,TYPE.later τ⟧ₑ)
    : ⟦Δ,weaken (EXPR.adv (n + 1) a) σ,τ⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦Γ,EXPR.adv (n + 1) a,τ⟧ₑ := by
    simp only [weaken]
    simp only [expr_interp]
    rw [Part.assert_pos]; swap
    . apply offset_ren_pos
      simp
    . simp
      rw [Part.assert_pos]; swap
      . simp
      . simp
        rw [IH]
        . simp
          clear IH
          congr
          clear a
          ext y a; simp
          generalize_proofs p1 p2
          suffices this : interp_adv (offset_ren σ (n + 1)) p1 (⟦cut_ren_typing σ H (n + 1) G2⟧ᵣ ≫ y)
            = ⟦H⟧ᵣ ≫ interp_adv (n + 1) p2 y
          rw [this]
          clear a
          simp only [interp_adv]
          simp only [interp_ty] at y ⊢
          have heq : (earlier_later_adj.homEquiv ⟦List.drop (offset_ren σ (n + 1)) Δ⟧ₛ ⟦τ⟧ₜ).invFun
              (⟦cut_ren_typing σ H (n + 1) G2⟧ᵣ ≫ y)
              = earlier.map ⟦cut_ren_typing σ H (n + 1) G2⟧ᵣ ≫ (earlier_later_adj.homEquiv _ _).invFun y := by
              rfl
          rw [heq]; clear heq
          simp [-iter]; simp only [← Category.assoc]
          congr 1; simp [-iter]
          clear y
          have p3 := offset_ren_ge σ (n + 1)
          rw [n_force_cut_nm p2 p1 p3]
          clear p1
          simp [-iter]
          rw [←(n_force_cut p2).naturality]
          simp only [← Category.assoc]
          congr 1
          exact cut_ren_split_fst H (n + 1) G2 p3

  lemma eq_weak_adv' (H : TYPED_REN σ Δ Γ)
    (H' : TYPED Γ (EXPR.adv n a) τ)
    (G : n < List.length Γ)
    (IH : ⟦List.drop (offset_ren σ n) Δ,weaken a (cut_ren σ n),TYPE.later τ⟧ₑ
      = Part.map (fun x ↦ ⟦cut_ren_typing σ H n G⟧ᵣ ≫ x) ⟦Γ.drop n,a,TYPE.later τ⟧ₑ)
    : ⟦Δ,weaken (EXPR.adv n a) σ,τ⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦Γ,EXPR.adv n a,τ⟧ₑ := by
    obtain ⟨G1, G2⟩ := TYPED.adv_inversion H'
    cases n
    . simp at G1
    . apply eq_weak_adv H G IH

  lemma eq_weak_fix (H : TYPED_REN σ (Δ :: Δs) (Γ :: Γs))
    (IH : ⟦((τ.later :: Δ) :: Δs),weaken a σ.cons,τ⟧ₑ = Part.map (fun x ↦ ⟦H.cons τ.later⟧ᵣ ≫ x) ⟦((τ.later :: Γ) :: Γs),a,τ⟧ₑ)
    : ⟦(Δ :: Δs),weaken (EXPR.fix' (TYPE.later τ) a) σ,τ⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦(Γ :: Γs),EXPR.fix' (TYPE.later τ) a,τ⟧ₑ := by
    simp only [weaken]
    simp [expr_interp]
    rw [IH]; clear IH
    simp [interp_typed_ren, interp_ren_cons]
    ext γ
    simp
    constructor
    . intro ⟨a, ⟨G, HEQ⟩⟩
      rw [HEQ]; clear HEQ
      exists a
      refine ⟨G, ?_⟩
      simp only [interp_fix, fixpoint, interp_ctx, interp_octx, interp_ty, Iso.inv_hom_id_assoc,
        MonoidalClosed.curry_natural_left, Category.assoc]
    . intro ⟨a, ⟨G, HEQ⟩⟩
      rw [HEQ]; clear HEQ
      exists a
      refine ⟨G, ?_⟩
      simp only [interp_fix, fixpoint, interp_ctx, interp_octx, interp_ty, Iso.inv_hom_id_assoc,
        MonoidalClosed.curry_natural_left, Category.assoc]

  lemma eq_weak_pair (H : TYPED_REN σ Δ Γ)
    (IH1 : ⟦Δ,weaken a σ,τ1⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦Γ,a,τ1⟧ₑ)
    (IH2 : ⟦Δ,weaken b σ,τ2⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦Γ,b,τ2⟧ₑ)
    : ⟦Δ,weaken (EXPR.pair a b) σ,(TYPE.prod τ1 τ2)⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦Γ,(EXPR.pair a b),(TYPE.prod τ1 τ2)⟧ₑ := by
    simp only [weaken]
    simp [expr_interp]
    rw [IH1, IH2]
    rfl

  lemma eq_weak_proj1 (H : TYPED_REN σ Δ Γ)
    (IH : ⟦Δ,weaken a σ,(TYPE.prod τ1 A)⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦Γ,a,(TYPE.prod τ1 A)⟧ₑ)
    : ⟦Δ,weaken (EXPR.proj A a .L) σ,τ1⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦Γ,EXPR.proj A a .L,τ1⟧ₑ := by
    simp only [weaken]
    simp [expr_interp]
    rw [IH]
    rfl

  lemma eq_weak_proj2 (H : TYPED_REN σ Δ Γ)
    (IH : ⟦Δ,weaken a σ,(TYPE.prod A τ2)⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦Γ,a,(TYPE.prod A τ2)⟧ₑ)
    : ⟦Δ,weaken (EXPR.proj A a .R) σ,τ2⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦Γ,EXPR.proj A a .R,τ2⟧ₑ := by
    simp only [weaken]
    simp [expr_interp]
    rw [IH]
    rfl

  lemma eq_weak_inl {A B : TYPE.{i}} (H : TYPED_REN σ Δ Γ)
    (IH : ⟦Δ,weaken a σ,A⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦Γ,a,A⟧ₑ)
    : ⟦Δ,weaken (EXPR.inl B a) σ,(TYPE.sum A B)⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦Γ,(EXPR.inl B a),(TYPE.sum A B)⟧ₑ := by
    simp only [weaken]
    simp [expr_interp, interp_inl]
    rw [IH]
    rfl

  lemma eq_weak_inr {A B : TYPE.{i}} (H : TYPED_REN σ Δ Γ)
    (IH : ⟦Δ,weaken a σ,B⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦Γ,a,B⟧ₑ)
    : ⟦Δ,weaken (EXPR.inr A a) σ,(TYPE.sum A B)⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦Γ,(EXPR.inr A a),(TYPE.sum A B)⟧ₑ := by
    simp only [weaken]
    simp [expr_interp, interp_inr]
    rw [IH]
    rfl

  lemma eq_weak_case {A B C : TYPE.{i}} (H : TYPED_REN σ Δ Γ)
    (IHe : ⟦Δ,weaken e σ,(TYPE.sum A B)⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦Γ,e,(TYPE.sum A B)⟧ₑ)
    (IHf : ⟦Δ,weaken f σ,(TYPE.arr A C)⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦Γ,f,(TYPE.arr A C)⟧ₑ)
    (IHg : ⟦Δ,weaken g σ,(TYPE.arr B C)⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦Γ,g,(TYPE.arr B C)⟧ₑ)
    : ⟦Δ,weaken (EXPR.case A B e f g) σ, C⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦Γ,(EXPR.case A B e f g), C⟧ₑ := by
    simp only [weaken]
    simp [expr_interp, interp_case]
    rw [IHe, IHf, IHg]
    simp only [Part.bind_map, ← comp_lift, Category.assoc]

  lemma eq_weak_or (H : TYPED_REN σ Δ Γ)
    (IH1 : ⟦Δ,weaken a σ,TYPE.prop⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦Γ,a,TYPE.prop⟧ₑ)
    (IH2 : ⟦Δ,weaken b σ,TYPE.prop⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦Γ,b,TYPE.prop⟧ₑ)
    : ⟦Δ,weaken (EXPR.or a b) σ,TYPE.prop⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦Γ,EXPR.or a b,TYPE.prop⟧ₑ := by
    simp only [weaken]
    simp [expr_interp]
    rw [IH1, IH2]
    rfl

  lemma eq_weak_and (H : TYPED_REN σ Δ Γ)
    (IH1 : ⟦Δ,weaken a σ,TYPE.prop⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦Γ,a,TYPE.prop⟧ₑ)
    (IH2 : ⟦Δ,weaken b σ,TYPE.prop⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦Γ,b,TYPE.prop⟧ₑ)
    : ⟦Δ,weaken (EXPR.and a b) σ,TYPE.prop⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦Γ,EXPR.and a b,TYPE.prop⟧ₑ := by
    simp only [weaken]
    simp [expr_interp]
    rw [IH1, IH2]
    rfl

  lemma eq_weak_impl (H : TYPED_REN σ Δ Γ)
    (IH1 : ⟦Δ,weaken a σ,TYPE.prop⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦Γ,a,TYPE.prop⟧ₑ)
    (IH2 : ⟦Δ,weaken b σ,TYPE.prop⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦Γ,b,TYPE.prop⟧ₑ)
    : ⟦Δ,weaken (EXPR.impl a b) σ,TYPE.prop⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦Γ,EXPR.impl a b,TYPE.prop⟧ₑ := by
    simp only [weaken]
    simp [expr_interp]
    rw [IH1, IH2]
    rfl

  lemma eq_weak_forall (H : TYPED_REN σ (Δ :: Δs) (Γ :: Γs))
    (IH : ⟦((A :: Δ) :: Δs),weaken a σ.cons,TYPE.prop⟧ₑ = Part.map (fun x ↦ ⟦H.cons A⟧ᵣ ≫ x) ⟦((A :: Γ) :: Γs),a,TYPE.prop⟧ₑ)
    : ⟦(Δ :: Δs),weaken (EXPR.forall' A a) σ,TYPE.prop⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦(Γ :: Γs),EXPR.forall' A a,TYPE.prop⟧ₑ := by
    simp only [weaken]
    simp [expr_interp]
    rw [IH]
    simp [interp_typed_ren, interp_ren_cons]
    ext γ
    simp
    constructor
    . intro ⟨a, ⟨G, HEQ⟩⟩
      rw [HEQ]
      exact ⟨a, G, interp_forall_natural _ a⟩
    . intro ⟨a, ⟨G, HEQ⟩⟩
      rw [HEQ]
      exact ⟨a, G, (interp_forall_natural _ a).symm⟩

  lemma eq_weak_exist (H : TYPED_REN σ (Δ :: Δs) (Γ :: Γs))
    (IH : ⟦((A :: Δ) :: Δs),weaken a σ.cons,TYPE.prop⟧ₑ = Part.map (fun x ↦ ⟦H.cons A⟧ᵣ ≫ x) ⟦((A :: Γ) :: Γs),a,TYPE.prop⟧ₑ)
    : ⟦(Δ :: Δs),weaken (EXPR.exists' A a) σ,TYPE.prop⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦(Γ :: Γs),EXPR.exists' A a,TYPE.prop⟧ₑ := by
    simp only [weaken]
    simp [expr_interp]
    rw [IH]
    simp [interp_typed_ren, interp_ren_cons]
    ext γ
    simp
    constructor
    . intro ⟨a, ⟨G, HEQ⟩⟩
      rw [HEQ]
      exact ⟨a, G, interp_exists_natural _ a⟩
    . intro ⟨a, ⟨G, HEQ⟩⟩
      rw [HEQ]
      exact ⟨a, G, (interp_exists_natural _ a).symm⟩

  lemma eq_weak_lift (H : TYPED_REN σ Δ Γ)
    (IH : ⟦Δ,weaken a σ,TYPE.later TYPE.prop⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦Γ,a,TYPE.later TYPE.prop⟧ₑ)
    : ⟦Δ,weaken (EXPR.lift a) σ,τ⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦Γ,(EXPR.lift a),τ⟧ₑ := by
    simp only [weaken]
    cases τ with
    | prop =>
      simp [expr_interp]
      rw [IH]
      rfl
    | _ => simp

  lemma eq_weak_true (H : TYPED_REN σ Δ Γ)
    : ⟦Δ,weaken EXPR.true σ,TYPE.prop⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦Γ,EXPR.true,TYPE.prop⟧ₑ := by
    simp only [weaken]
    simp [expr_interp]
    rfl

  lemma eq_weak_false (H : TYPED_REN σ Δ Γ)
    : ⟦Δ,weaken EXPR.false σ,TYPE.prop⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦Γ,EXPR.false,TYPE.prop⟧ₑ := by
    simp only [weaken]
    simp [expr_interp]
    rfl

  lemma eq_weak_eq (H : TYPED_REN σ Δ Γ)
    (IH1 : ⟦Δ,weaken a σ,A⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦Γ,a,A⟧ₑ)
    (IH2 : ⟦Δ,weaken b σ,A⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦Γ,b,A⟧ₑ)
    : ⟦Δ,weaken (EXPR.eq A a b) σ,TYPE.prop⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦Γ,EXPR.eq A a b,TYPE.prop⟧ₑ := by
    simp only [weaken]
    simp [expr_interp]
    rw [IH1, IH2]
    rfl

  lemma eq_weak_ax (H : TYPED_REN σ Δ Γ)
    : ⟦Δ,weaken (EXPR.ax A a) σ,τ⟧ₑ = Part.map (fun x ↦ ⟦H⟧ᵣ ≫ x) ⟦Γ,EXPR.ax A a,τ⟧ₑ := by
    simp only [weaken]
    simp only [expr_interp]
    rfl

  lemma eq_weak (Γ : CTX.{i}) (e : EXPR.{i}) (τ : TYPE.{i})
    (H : TYPED_REN σ Δ Γ)
    (H' : TYPED Γ e τ)
    : expr_interp Δ (weaken e σ) τ = (expr_interp Γ e τ).map (fun x => interp_typed_ren H ≫ x) := by
    revert Δ σ Γ τ H H'
    induction e with
    | embed A a =>
      intro σ Δ Γ τ H H'
      apply eq_weak_embed
    | embed_apply A B a b IH1 IH2 =>
      intro σ Δ Γ τ H H'
      obtain ⟨G1, G2, G3⟩ := TYPED.embed_apply_inversion H'
      rw [G1]
      apply eq_weak_embed_apply
      . apply IH1; assumption
      . apply IH2; assumption
    | pure a IH =>
      intro σ Δ Γ τ H H'
      obtain ⟨G1, G2⟩ := TYPED.pure_inversion H'
      rw [G1]
      apply eq_weak_pure
      apply IH; assumption
    | var' n m =>
      intro σ Δ Γ τ H H'
      apply eq_weak_var'
    | app A a b IH1 IH2 =>
      intro σ Δ Γ τ H H'
      obtain ⟨G1, G2⟩ := TYPED.app_inversion H'
      apply eq_weak_app
      . apply IH1; assumption
      . apply IH2; assumption
    | lam' A a IH =>
      intro σ Δ Γ τ H H'
      cases Γ with
      | nil => simpa using typing_stack_len H'
      | cons Γ Γs =>
        obtain ⟨τ', G1, G2⟩ := TYPED.lam'_inversion H'
        rw [G1]
        cases Δ with
        | nil => simpa using ren_len' _ H
        | cons Δ Δs =>
          apply eq_weak_lam
          apply IH
          assumption
    | delay a IH =>
      intro σ Δ Γ τ H H'
      obtain ⟨τ', G1, G2⟩ := TYPED.delay_inversion H'
      rw [G1]
      apply eq_weak_delay
      apply IH; assumption
    | adv n a IH =>
      intro σ Δ Γ τ H H'
      obtain ⟨G1, G2⟩ := TYPED.adv_inversion H'
      apply eq_weak_adv'
      . assumption
      . apply IH; assumption
      . have J := typing_stack_len G2
        grind only [= List.length_drop, cases Or]
    | fix' A a IH =>
      intro σ Δ Γ τ H H'
      cases Γ with
      | nil => simpa using typing_stack_len H'
      | cons Γ Γs =>
        obtain ⟨G1, G2⟩ := TYPED.fix'_inversion H'
        rw [G1]
        cases Δ with
        | nil => simpa using ren_len' _ H
        | cons Δ Δs =>
          apply eq_weak_fix
          apply IH; assumption
    | pair a b IH1 IH2 =>
      intro σ Δ Γ τ H H'
      obtain ⟨τ1, τ2, G1, G2, G3⟩ := TYPED.pair_inversion H'
      rw [G1]
      apply eq_weak_pair
      . apply IH1; assumption
      . apply IH2; assumption
    | proj A a d IH =>
      intro σ Δ Γ τ H H'
      cases d with
      | L =>
        apply eq_weak_proj1
        apply IH; exact TYPED.projL_inversion H'
      | R =>
        apply eq_weak_proj2
        apply IH; exact TYPED.projR_inversion H'
    | inl B a IH =>
      intro σ Δ Γ τ H H'
      obtain ⟨A', G1, G2⟩ := TYPED.inl_inversion H'
      rw [G1]
      apply eq_weak_inl
      apply IH; assumption
    | inr A a IH =>
      intro σ Δ Γ τ H H'
      obtain ⟨B', G1, G2⟩ := TYPED.inr_inversion H'
      rw [G1]
      apply eq_weak_inr
      apply IH; assumption
    | case A B e f g IHe IHf IHg =>
      intro σ Δ Γ τ H H'
      obtain ⟨Ge, Gf, Gg⟩ := TYPED.case_inversion H'
      apply eq_weak_case
      · apply IHe; assumption
      · apply IHf; assumption
      · apply IHg; assumption
    | or a b IH1 IH2 =>
      intro σ Δ Γ τ H H'
      obtain ⟨G1, G2, G3⟩ := TYPED.or_inversion H'
      rw [G1]
      apply eq_weak_or
      . apply IH1; assumption
      . apply IH2; assumption
    | and a b IH1 IH2 =>
      intro σ Δ Γ τ H H'
      obtain ⟨G1, G2, G3⟩ := TYPED.and_inversion H'
      rw [G1]
      apply eq_weak_and
      . apply IH1; assumption
      . apply IH2; assumption
    | impl a b IH1 IH2 =>
      intro σ Δ Γ τ H H'
      obtain ⟨G1, G2, G3⟩ := TYPED.impl_inversion H'
      rw [G1]
      apply eq_weak_impl
      . apply IH1; assumption
      . apply IH2; assumption
    | forall' A a IH =>
      intro σ Δ Γ τ H H'
      cases Γ with
      | nil => simpa using typing_stack_len H'
      | cons Γ Γs =>
        obtain ⟨G1, G2⟩ := TYPED.forall'_inversion H'
        rw [G1]
        cases Δ with
        | nil => simpa using ren_len' _ H
        | cons Δ Δs =>
          apply eq_weak_forall
          apply IH; assumption
    | exists' A a IH =>
      intro σ Δ Γ τ H H'
      cases Γ with
      | nil => simpa using typing_stack_len H'
      | cons Γ Γs =>
        obtain ⟨G1, G2⟩ := TYPED.exists'_inversion H'
        rw [G1]
        cases Δ with
        | nil => simpa using ren_len' _ H
        | cons Δ Δs =>
          apply eq_weak_exist
          apply IH; assumption
    | lift a IH =>
      intro σ Δ Γ τ H H'
      obtain ⟨G1, G2⟩ := TYPED.lift_inversion H'
      rw [G1]
      apply eq_weak_lift
      apply IH; assumption
    | true =>
      intro σ Δ Γ τ H H'
      rw [TYPED.true_inversion H']
      apply eq_weak_true
    | false =>
      intro σ Δ Γ τ H H'
      rw [TYPED.false_inversion H']
      apply eq_weak_false
    | eq A a b IH1 IH2 =>
      intro σ Δ Γ τ H H'
      obtain ⟨G1, G2, G3⟩ := TYPED.eq_inversion H'
      rw [G1]
      apply eq_weak_eq
      . apply IH1; assumption
      . apply IH2; assumption
    | ax A a =>
      intro σ Δ Γ τ H H'
      apply eq_weak_ax

  lemma eq_subst_var
    {σ : SUBST} {Γ : CTX.{i}} {Δ : OCTX.{i}} (τ : TYPE.{i})
    (n m : Nat)
    (Hσ : TSUBST σ Γ Δ)
    (Hm : Δ[m]? = some τ)
    : Part.some (⟦Hσ⟧ₛᵤ ≫ (octx_proj Δ m τ Hm)) = expr_interp Γ (subst_var σ n m) τ := by
    revert τ n m
    induction Hσ with
    | @epsilon Γ HΓ =>
      intro τ n m Hm
      exfalso
      simp at Hm
    | cons Ht Hσ' IH =>
      intro τ n m Hm
      cases m with
      | zero =>
        simp
        ext a
        constructor
        . intro ⟨H1, H2⟩
          simp at Hm H2
          cases Hm
          simp only [interp_tsubst, interp_subst_cons, octx_proj
            , eqToHom_refl, Category.comp_id] at H1
          rw [←H2]
          simp [interp_tsubst, interp_subst_cons, octx_proj]
          apply Part.get_mem
        . intro ⟨H1, H2⟩
          simp at Hm H2
          cases Hm
          simp only [interp_tsubst, interp_subst_cons, octx_proj
            , eqToHom_refl, Category.comp_id]
          rw [←H2]
          simp only [interp_octx, lift_fst]
          exact Part.mem_some _
      | succ m' =>
        simp
        ext a
        constructor
        . intro ⟨H1, H2⟩
          simp at Hm
          simp [interp_tsubst, interp_subst_cons, octx_proj] at H2
          rw [←H2, ←IH]; swap
          . assumption
          . exact Part.mem_some _
        . intro ⟨H1, H2⟩
          simp at Hm
          simp [interp_tsubst, interp_subst_cons, octx_proj]
          rw [←H2]
          specialize (IH τ n m' Hm)
          symm at IH
          rw [Part.get_eq_iff_eq_some, IH]

  lemma eq_ssubst_var
    {σ : SSUBST} {Γ Δ : CTX.{i}} {Ψ : OCTX.{i}} (τ : TYPE.{i})
    (n m : Nat)
    (Hσ : TSSUBST σ Γ Δ)
    (Hn : Δ[n]? = some Ψ)
    (Hm : Ψ[m]? = some τ)
    : Part.some (⟦Hσ⟧ₛₛ ≫ (interp_var n m Hn Hm)) = expr_interp Γ (ssubst_var σ n m) τ := by
    revert n m τ Ψ
    induction Hσ with
    | single σ' Hσ' =>
      intros Ψ τ n m Hn Hm
      simp [interp_tssubst, interp_ssubst_single]
      cases n with
      | zero =>
        simp at Hn
        cases Hn
        rw [←eq_subst_var τ 0 m Hσ' Hm]
        congr 1
      | succ _ =>
        simp at Hn
    | @wk _ _ _ _ Ψ'' _ i Hlt Hlen Hσ' Hσ'' IH =>
      intros Ψ' τ n m Hn Hm
      simp [interp_tssubst, interp_ssubst_wk]
      revert Hn
      cases n with
      | zero =>
        intros Hn
        simp; simp at Hn; cases Hn
        rw [←eq_subst_var τ 0 m Hσ'' Hm]
        congr 1
      | succ n' =>
        intros Hn
        simp
        rw [eq_weak _ _ τ (TYPED_REN.global_shift i Hlen (TYPED_REN.id (ssubst_len _ Hσ')))]; swap
        . apply ssubst_var_typing
          . assumption
          . apply Hn
          . apply Hm
        . rw [←IH τ n' m Hn Hm]
          simp [interp_typed_ren, interp_ren_global_shift, interp_ren_id]
          simp [interp_var, ctx_proj]
          cases Hlen
          simp [n_force_cut]
          cases Ψ'' with
          | nil =>
            exfalso; simp at Hlt
          | cons t ts =>
            simp [n_force, reassoc_of% force.naturality, Functor.id_map]

  lemma eq_bind_var (H : TSSUBST σ Δ Γ)
    (H' : TYPED Γ (EXPR.var' n m) τ)
    : ⟦Δ,binds σ (EXPR.var' n m),τ⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦Γ,EXPR.var' n m,τ⟧ₑ := by
    simp [binds]
    ext γ
    constructor
    . intro G
      simp [Part.assert]
      let ⟨G1, G2⟩ := G
      rw [←G2]; clear G2
      obtain ⟨Ψ, H1, H2⟩ := TYPED.var'_inversion H'
      have G := eq_ssubst_var (Ψ := Γ[n]'(by grind only [→ List.getElem_of_getElem?,
        = List.getElem?_eq_none, = getElem?_pos, = getElem?_neg])) τ n m H (by grind only [→
            List.getElem_of_getElem?,
          = List.getElem?_eq_none, = getElem?_pos, = getElem?_neg]) (by grind only [→
              List.getElem_of_getElem?,
            = List.getElem?_eq_none, = getElem?_pos, = getElem?_neg])
      exists (by grind only [→ List.getElem_of_getElem?, = List.getElem?_eq_none, = getElem?_pos,
        = getElem?_neg])
      symm
      apply Part.get_eq_of_mem
      rw [←G]
      simp
    . simp [Part.assert]
      intro G1 G2 HEQ
      rw [←HEQ]
      rw [←eq_ssubst_var (Ψ := Γ[n]) τ n m H (by grind only) G2]
      simp

  lemma eq_bind_embed (H : TSSUBST σ Δ Γ)
    : ⟦Δ,binds σ (EXPR.embed A a),τ⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦Γ,EXPR.embed A a,τ⟧ₑ := by
    simp only [binds]
    cases τ with
    | embed A' =>
      ext γ
      simp [expr_interp, Part.map, Part.assert]
      constructor
      . intro ⟨g, G⟩; exists g
      . intro ⟨g, G⟩; exists g
    | _ => simp

  lemma eq_bind_embed_apply (H : TSSUBST σ Δ Γ)
    (IH1 : ⟦Δ,binds σ a,(TYPE.embed (A → B))⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦Γ,a,(TYPE.embed (A → B))⟧ₑ)
    (IH2 : ⟦Δ,binds σ b,(TYPE.embed A)⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦Γ,b,(TYPE.embed A)⟧ₑ)
    : ⟦Δ,binds σ (EXPR.embed_apply A B a b),(TYPE.embed B)⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦Γ,EXPR.embed_apply A B a b,(TYPE.embed B)⟧ₑ := by
    simp only [binds]
    simp [expr_interp, interp_embed_apply]
    rw [IH1, IH2]
    rfl

  lemma eq_bind_pure (H : TSSUBST σ Δ Γ)
    (IH : ⟦Δ,binds σ a,TYPE.embed Prop⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦Γ,a,TYPE.embed Prop⟧ₑ)
    : ⟦Δ,binds σ (EXPR.pure a),TYPE.prop⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦Γ,(EXPR.pure a),TYPE.prop⟧ₑ := by
    simp only [binds]
    simp [expr_interp, Part.map]
    rw [IH]
    simp [Part.map, Part.bind]
    ext γ
    constructor
    . intro ⟨g, G⟩
      simp [Part.assert] at g G
      rw [←G]
      simp [Part.assert]
      exists g
    . intro ⟨g, G⟩
      simp at g
      simp
      exists g.1
      rw [←G]
      simp
      rfl

  lemma eq_bind_app (H : TSSUBST σ Δ Γ)
    (IH1 : ⟦Δ,binds σ a,A.arr τ⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦Γ,a,A.arr τ⟧ₑ)
    (IH2 : ⟦Δ,binds σ b,A⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦Γ,b,A⟧ₑ)
    : ⟦Δ,binds σ (EXPR.app A a b),τ⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦Γ,EXPR.app A a b,τ⟧ₑ := by
    simp only [binds]
    simp [expr_interp]
    rw [IH1, IH2]
    rfl

  open TSUBST in
  lemma sr_compose_interp (Hσ : TSUBST σ Γs Γ) (Hδ : TYPED_REN δ Δ Γs)
    : ⟦sr_compose_typing Hσ Hδ⟧ₛᵤ = ⟦Hδ⟧ᵣ ≫ ⟦Hσ⟧ₛᵤ := by
    induction Hσ with
    | epsilon H =>
      simp [TSUBST.sr_compose_typing, interp_tsubst, interp_subst_epsilon]
    | @cons Γ e τ _ _ H Hσ IH =>
      simp [TSUBST.sr_compose_typing, interp_tsubst, interp_subst_cons]
      rw [IH]; clear IH
      simp only [interp_octx]
      congr 1
      rw [Part.get_eq_iff_eq_some]
      have HEQ' : Part.some (⟦Hδ⟧ᵣ ≫ ⟦Γ,e,τ⟧ₑ.get (expr_interp_correct H)) = (Part.map (fun x ↦ ⟦Hδ⟧ᵣ ≫ x) ⟦Γ,e,τ⟧ₑ) := by
        simp [Part.map]
        ext γ; simp
        constructor
        . intro HEQ; rw [HEQ]
          exists (expr_interp_correct H)
        . intro ⟨G, HEQ⟩; rw [←HEQ]
      rw [HEQ']; clear HEQ'
      rw [←eq_weak _ e τ Hδ H]

  lemma sext_typing_interp τ (H : TSSUBST σ (Δ' :: Δs) (Γ' :: Γs))
    : ⟦H.ext_typing (τ := τ)⟧ₛₛ = (α_ _ _ _).hom ≫ ((𝟙 ⟦τ⟧ₜ) ⊗ₘ ⟦H⟧ₛₛ) ≫ (α_ _ _ _).inv := by
    let Δ := Δ' :: Δs
    let Γ := Γ' :: Γs
    have HEQ1 : Δ = Δ' :: Δs := by rfl
    have HEQ2 : Γ = Γ' :: Γs := by rfl
    clear_value Δ
    clear_value Γ
    let H' : TSSUBST σ Δ Γ := HEQ1 ▸ HEQ2 ▸ H
    have JEQ1 : ⟦H⟧ₛₛ = eqToHom (congr_arg _ (Eq.symm HEQ1)) ≫ ⟦H'⟧ₛₛ ≫ eqToHom (congr_arg _ HEQ2) := by
      cases HEQ1; cases HEQ2; rfl
    rw [JEQ1]
    have JEQ2 : ⟦H.ext_typing⟧ₛₛ = ⟦TSSUBST.ext_typing (τ := τ) (HEQ1 ▸ HEQ2 ▸ H')⟧ₛₛ := by
      cases HEQ1; cases HEQ2; rfl
    rw [JEQ2]
    clear_value H'
    cases H' with
    | single σ Hσ =>
      simp [TSSUBST.ext_typing]
      generalize_proofs p1 p2 p3 p4
      cases p1; cases p2
      cases HEQ1; cases HEQ2
      cases p3; cases p4
      simp [TSSUBST.ext_typing']
      generalize_proofs p
      cases p with | intro p1 p2 =>
      cases p1; cases p2
      simp [SUBST.ext', interp_tssubst, interp_ssubst_single, TSUBST.ext_typing]
      simp [interp_tsubst, interp_subst_cons, interp_ctx, interp_octx]
      rw [sr_compose_interp]
      simp [interp_typed_ren, interp_ren_local_weaken, interp_ren_id]
      simp [interp_ctx, interp_octx]
      simp [interp_var, ctx_proj, octx_proj]
      simp [Part.assert]
      rfl
    | @wk _ Γ _ _ Ψ _ n Hn Hl Hσs Hσ =>
      cases Hl
      cases HEQ2
      simp_all
      cases Ψ with
      | nil => exfalso; simp at Hn
      | cons Ψ Ψs =>
        obtain rfl : Ψ = Δ' := by
          grind only [= List.cons_append, = List.length_cons]
        obtain rfl : Δs = Ψs ++ Γ := by
          grind only [= List.cons_append, = List.length_cons]
        cases HEQ1
        simp_all
        simp [TSSUBST.ext_typing]
        generalize_proofs p1 p2 p3
        cases p1; cases p2; cases p3
        simp [TSSUBST.ext_typing']
        generalize_proofs p1 p2 p3 p4
        cases p1 with | intro q1 q2 =>
        cases q1; cases q2
        have p2' := p2 rfl
        cases p2'
        cases p3
        cases p4
        simp_all
        rename_i hpair hpf2 hpf1 hpf
        cases hpair with | intro q1 q2 =>
        cases q1; cases q2
        simp [SUBST.ext', interp_tssubst, interp_ssubst_wk, TSUBST.ext_typing]
        simp [interp_tsubst, interp_subst_cons, interp_ctx, interp_octx]
        rw [sr_compose_interp]
        simp [interp_typed_ren, interp_ren_local_weaken, interp_ren_id]
        simp [interp_ctx, interp_octx]
        simp [interp_var, ctx_proj, octx_proj]
        simp [Part.assert]
        apply CartesianMonoidalCategory.hom_ext
        · apply CartesianMonoidalCategory.hom_ext
          · rfl
          · simp
        · simp
          simp only [← Category.assoc]
          erw [split_cons_fst' (τ :: Ψ) (Ψs ++ Γ) Ψs.length]
          rfl

  open TSUBST in
  lemma ext_typing_interp (Hσ : TSUBST σ (Γ :: Γs) Δ) :
    ⟦TSUBST.ext_typing (τ := τ) Hσ⟧ₛᵤ = (α_ _ _ _).hom ≫ (𝟙 _ ⊗ₘ ⟦Hσ⟧ₛᵤ) := by
    simp [TSUBST.ext_typing]
    simp [interp_tsubst, interp_subst_cons, interp_ctx, interp_octx]
    rw [sr_compose_interp]
    simp [Part.assert]
    simp [interp_var, ctx_proj, octx_proj]
    simp [interp_ctx, interp_octx]
    simp [interp_typed_ren, interp_ren_local_weaken, interp_ren_id]
    simp [interp_ctx]
    rfl

  open TSUBST in
  lemma subst_id_interp {Γ : OCTX.{i}} {Δ : CTX.{i}}
    : ⟦TSUBST.id (Δ := Δ) Γ⟧ₛᵤ = fst _ _ := by
    induction Γ with
    | nil =>
      simp [TSUBST.id, interp_tsubst, interp_subst_epsilon, interp_ctx, interp_octx]
      rfl
    | cons Γ Γs IH =>
      simp [TSUBST.id]
      erw [ext_typing_interp]
      simp
      rw [IH]; clear IH
      simp [interp_ctx, interp_octx]
      rfl

  open TSUBST in
  lemma ssubst_id_interp {Γ : CTX.{i}} (HΓ : 0 < Γ.length)
    : ⟦TSSUBST.id Γ HΓ⟧ₛₛ = 𝟙 _ := by
    cases Γ with
    | nil => exfalso; simp at HΓ
    | cons Γ Γs =>
      simp only [TSSUBST.id]
      generalize_proofs P
      cases P; simp
      clear HΓ
      induction Γs generalizing Γ with
      | nil =>
        simp [TSSUBST.id_cons, interp_ctx, interp_tssubst, interp_ssubst_single]
        rw [subst_id_interp]
        rfl
      | cons x xs IH =>
        simp [TSSUBST.id_cons, interp_tssubst, interp_ssubst_wk]
        simp [n_force_cut, n_force]
        rw [IH]; clear IH
        simp [interp_ctx_split, interp_ctx]
        rw [subst_id_interp]
        rfl

  open TSUBST in
  lemma ssubst_cons_interp (Hσs : TSSUBST σs Γs (Δ :: Δs)) (He : TYPED Γs e τ)
    : ⟦Hσs.cons He⟧ₛₛ
      = (lift ((expr_interp _ e τ).get (expr_interp_correct He)) ⟦Hσs⟧ₛₛ ≫ (α_ ⟦τ⟧ₜ ⟦Δ⟧ₒ (earlier.obj ⟦Δs⟧ₛ)).inv) := by
    simp only [TSSUBST.cons]
    cases Hσs with
    | single σ Hσ =>
      simp [interp_tssubst, interp_ssubst_single, interp_tsubst, interp_subst_cons]
      simp only [interp_octx, interp_ctx]
      cat_disch
    | wk n Hn Hneq Hσ Hσs =>
      simp [interp_tssubst, interp_ssubst_wk, interp_tsubst, interp_subst_cons]

  open TSUBST in
  lemma ssubst_single_interp (H : TYPED (Γ :: Γs) e τ)
    : ⟦TSSUBST.single_subst H⟧ₛₛ
      = (lift ((expr_interp _ e τ).get (expr_interp_correct H)) (𝟙 _) ≫ (α_ _ _ _).inv) := by
    simp only [TSSUBST.single_subst]
    erw [ssubst_cons_interp]
    rw [ssubst_id_interp]

  lemma eq_bind_lam (H : TSSUBST σ (Δ :: Δs) (Γ :: Γs))
    (IH : ⟦((B :: Δ) :: Δs),binds σ.ext' a,C⟧ₑ = Part.map (fun x ↦ ⟦TSSUBST.ext_typing H⟧ₛₛ ≫ x) ⟦((B :: Γ) :: Γs),a,C⟧ₑ)
    : ⟦(Δ :: Δs),binds σ (EXPR.lam' A a),(TYPE.arr B C)⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦(Γ :: Γs),EXPR.lam' A a,(TYPE.arr B C)⟧ₑ := by
    simp only [binds]
    simp only [expr_interp]
    rw [IH, sext_typing_interp]
    ext γ
    simp
    constructor
    . intro ⟨a, ⟨G, HEQ⟩⟩
      rw [HEQ]
      exists a
      refine ⟨G, ?_⟩
      simp only [interp_lam, interp_ctx, interp_octx, Iso.inv_hom_id_assoc,
        MonoidalClosed.curry_natural_left]
    . intro ⟨a, ⟨G, HEQ⟩⟩
      rw [HEQ]
      exists a
      refine ⟨G, ?_⟩
      simp only [interp_lam, interp_ctx, interp_octx, Iso.inv_hom_id_assoc,
        MonoidalClosed.curry_natural_left]

  lemma eq_bind_delay (H : TSSUBST σ Δ Γ)
    (G : 0 < List.length ([[]] ++ Δ))
    (IH : ⟦[] :: Δ,binds (SSUBST.wk 1 σ .epsilon) a,A⟧ₑ
      = Part.map (fun x ↦ ⟦H.wk (Ψ := [[]]) (Δ := []) (σ := .epsilon) 1 (zero_lt_one) (Eq.refl _) (.epsilon G)⟧ₛₛ ≫ x) ⟦[] :: Γ,a,A⟧ₑ)
    : ⟦Δ,binds σ (EXPR.delay a),TYPE.later A⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦Γ,(EXPR.delay a),TYPE.later A⟧ₑ := by
    simp only [binds]
    simp [expr_interp]
    simp at IH; rw [IH]; clear IH
    simp [interp_tssubst, interp_ssubst_wk, Part.bind]
    simp [Part.assert]
    simp [interp_ctx, interp_octx]
    simp [interp_delay]
    apply heq_of_eq
    funext ha
    erw [← Adjunction.homEquiv_naturality_left]
    congr 1
    simp [interp_tsubst, interp_subst_epsilon, interp_ctx, interp_octx]
    simp [n_force_cut, n_force]
    simp [interp_ctx_split]
    rfl

  lemma split_cons_fst (Δ : OCTX.{i}) (Δs : CTX.{i}) (m : ℕ) :
    (interp_ctx_split (Δ :: Δs) (i := m + 1)).hom
      ≫ fst (earlier.obj ((earlier.iter m).obj ⟦List.drop m Δs⟧ₛ)) (⟦Δ⟧ₒ ⊗ earlier.obj ⟦List.take m Δs⟧ₛ)
    = snd ⟦Δ⟧ₒ (earlier.obj ⟦Δs⟧ₛ)
      ≫ earlier.map (interp_ctx_split Δs (i := m)).hom
      ≫ earlier.map (fst ((earlier.iter m).obj ⟦List.drop m Δs⟧ₛ) ⟦List.take m Δs⟧ₛ) := by
    simp [interp_ctx_split]
    refine Eq.trans (congrArg
      ((⟦Δ⟧ₒ ◁ earlier.map (interp_ctx_split Δs (i := m)).hom
        ≫ ⟦Δ⟧ₒ ◁ earlier_prod.hom.app ((earlier.iter m).obj ⟦List.drop m Δs⟧ₛ, ⟦List.take m Δs⟧ₛ)) ≫ ·)
      (cart_tail_chase ⟦Δ⟧ₒ (earlier.obj ((earlier.iter m).obj ⟦List.drop m Δs⟧ₛ))
        (earlier.obj ⟦List.take m Δs⟧ₛ))) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (snd_push_gen (interp_ctx_split Δs (i := m)).hom ⟦Δ⟧ₒ
      (fst (earlier.obj ((earlier.iter m).obj ⟦List.drop m Δs⟧ₛ)) (earlier.obj ⟦List.take m Δs⟧ₛ))) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg
      ((snd ⟦Δ⟧ₒ (earlier.obj ⟦Δs⟧ₛ) ≫ earlier.map (interp_ctx_split Δs (i := m)).hom) ≫ ·)
      (prod_fst_earlier ((earlier.iter m).obj ⟦List.drop m Δs⟧ₛ) ⟦List.take m Δs⟧ₛ)) ?_
    exact Category.assoc _ _ _

  lemma n_force_cut_earlier {j : ℕ} (Hn : 0 < j) (U : ℐ.{u})
      (pf : (earlier.iter j).obj (earlier.obj U) = earlier.obj ((earlier.iter j).obj U)) :
      (n_force_cut Hn).app (earlier.obj U) = eqToHom pf ≫ earlier.map ((n_force_cut Hn).app U) := by
    simp only [n_force_cut_nm_force_cut]
    refine (nm_force_cut_push (i := 1) (j := j) (by omega) U
      (by rw [iter_iter', iter'_comm]) rfl).trans ?_
    generalize_proofs pA hle pT
    exact congrArg (fun z => eqToHom pf ≫ z)
      (Category.comp_id (earlier.map ((nm_force_cut hle).app U)))

  lemma nm_force_cut_hsplit1 {j p : ℕ} (Hn : 0 < j) (p3 : p + 1 ≤ j + p) (L : ℐ.{u})
    (r : (earlier.iter j).obj ((earlier.iter p).obj L) = (earlier.iter (j + p)).obj L) :
    (n_force_cut Hn).app ((earlier.iter p).obj L) = eqToHom r ≫ (nm_force_cut p3).app L := by
    have hrw2 : eqToHom r ≫ (nm_force_cut p3).app L
        = eqToHom (Eq.trans (congr_obj (Eq.symm (iter_add earlier p j)) L)
            (congr_obj (iter_add_comm earlier p j) L)) ≫ (nm_force_cut p3).app L := rfl
    rw [hrw2]; clear hrw2 r
    rw [← eqToHom_trans (congr_obj (Eq.symm (iter_add earlier p j)) L)
      (congr_obj (iter_add_comm earlier p j) L)]
    rw [Category.assoc]
    rw [←eqToHom_app (iter_add_comm earlier p j)]
    rw [←NatTrans.comp_app]
    rw [←eqToHom_app (Eq.symm (iter_add earlier p j))]
    rw [←NatTrans.comp_app]
    rw [←Category.assoc, eqToHom_trans]
    generalize_proofs P
    revert P p3 Hn
    induction p generalizing L j with
    | zero =>
      intro Hn p3 eq
      simp
      cases j with
      | zero => rfl
      | succ j =>
        simp [nm_force_cut]
        rw [nm_force_zero]
        rfl
    | succ p IH =>
      intro Hn p3 eq
      rw [NatTrans.comp_app, eqToHom_app]
      rw [nm_force_cut_assoc (by grind only) (by grind only)]
      rw [NatTrans.comp_app]
      rw [←Category.assoc]
      simp [nm_force_cut]
      have heq : ((earlier.iter p ⋙ earlier) ⋙ earlier.iter j)
        = (((earlier.iter p ⋙ earlier.iter j) ⋙ earlier)) := by
        rw [←earlier.iter_add]
        have heq := (earlier.iter_add_comm p 1)
        simp at heq
        rw [heq]; clear heq
        have heq := (earlier.iter_add_comm (p + j) 1)
        simp at heq
        rw [heq]; clear heq
        rw [←earlier.iter_add]
        rw [Nat.add_assoc]
      have heq : eqToHom (congr_obj eq L)
        = eqToHom (congr_obj heq L) ≫ (earlier.map (eqToHom (congr_obj (Eq.trans (Eq.symm (earlier.iter_add p j)) (earlier.iter_add_comm p j)) L))) := by
        rw [eqToHom_map]; exact (eqToHom_trans _ _).symm
      erw [heq]; clear heq
      erw [Category.assoc, ←earlier.map_comp]
      specialize (IH (j := j) L Hn (by omega) (Eq.trans (Eq.symm (earlier.iter_add p j)) (earlier.iter_add_comm p j)))
      rw [NatTrans.comp_app] at IH
      simp at IH
      erw [←IH]; clear IH
      clear eq p3
      generalize_proofs pf
      exact n_force_cut_earlier Hn ((earlier.iter p).obj L) pf

  lemma nm_force_cut_hsplit {j p m : ℕ} (Hn : 0 < j) (hm : m ≤ p) (pr1 : m + 1 ≤ j + p)
    (L : ℐ.{u})
    (r : (earlier.iter j).obj ((earlier.iter p).obj L) = (earlier.iter (j + p)).obj L) :
    (earlier.iter j).map ((nm_force_cut hm).app L) ≫ (n_force_cut Hn).app ((earlier.iter m).obj L)
    = eqToHom r ≫ (nm_force_cut pr1).app L := by
    rw [(n_force_cut Hn).naturality]
    have heq : earlier.map ((nm_force_cut hm).app L)
      = (nm_force_cut (i := m + 1) (j := p + 1) (Nat.succ_le_succ hm)).app L := by
      simp [nm_force_cut]
    rw [heq]; clear heq
    rw [←nm_force_cut_trans (Nat.succ_le_succ hm) (show p + 1 ≤ j + p by omega)]
    rw [NatTrans.comp_app]
    rw [←Category.assoc]
    congr 1
    exact nm_force_cut_hsplit1 Hn (show p + 1 ≤ j + p by omega) L r

  lemma bindadv_wk_core (Ψ Γ Δs : CTX.{i}) (m p : ℕ)
    (Hn : 0 < List.length Ψ) (hm : m ≤ p) (pr1 : m + 1 ≤ List.length Ψ + p)
    (pr2 : (⟦List.drop (List.length Ψ + p) (Ψ ++ Γ)⟧ₛ : ℐ.{i}) = ⟦List.drop p Γ⟧ₛ)
    (pr4 : (⟦List.drop (List.length Ψ) (Ψ ++ Γ)⟧ₛ : ℐ.{i}) = ⟦Γ⟧ₛ)
    (C : (⟦List.drop p Γ⟧ₛ : ℐ.{i}) ⟶ ⟦List.drop m Δs⟧ₛ)
    (S : (⟦Γ⟧ₛ : ℐ.{i}) ⟶ ⟦Δs⟧ₛ)
    (hIH : (interp_ctx_split Γ (i := p)).hom
        ≫ fst ((earlier.iter p).obj ⟦List.drop p Γ⟧ₛ) ⟦List.take p Γ⟧ₛ
        ≫ (nm_force_cut hm).app ⟦List.drop p Γ⟧ₛ
        ≫ (earlier.iter m).map C
      = S ≫ (interp_ctx_split Δs (i := m)).hom
        ≫ fst ((earlier.iter m).obj ⟦List.drop m Δs⟧ₛ) ⟦List.take m Δs⟧ₛ) :
    (interp_ctx_split (Ψ ++ Γ) (i := List.length Ψ + p)).hom
      ≫ fst ((earlier.iter (List.length Ψ + p)).obj ⟦List.drop (List.length Ψ + p) (Ψ ++ Γ)⟧ₛ)
          ⟦List.take (List.length Ψ + p) (Ψ ++ Γ)⟧ₛ
      ≫ (nm_force_cut pr1).app ⟦List.drop (List.length Ψ + p) (Ψ ++ Γ)⟧ₛ
      ≫ earlier.map ((earlier.iter m).map (eqToHom pr2))
      ≫ earlier.map ((earlier.iter m).map C)
    = (interp_ctx_split (Ψ ++ Γ) (i := List.length Ψ)).hom
      ≫ fst ((earlier.iter (List.length Ψ)).obj ⟦List.drop (List.length Ψ) (Ψ ++ Γ)⟧ₛ)
          ⟦List.take (List.length Ψ) (Ψ ++ Γ)⟧ₛ
      ≫ (n_force_cut Hn).app ⟦List.drop (List.length Ψ) (Ψ ++ Γ)⟧ₛ
      ≫ earlier.map (eqToHom pr4)
      ≫ earlier.map S
      ≫ earlier.map (interp_ctx_split Δs (i := m)).hom
      ≫ earlier.map (fst ((earlier.iter m).obj ⟦List.drop m Δs⟧ₛ) ⟦List.take m Δs⟧ₛ) := by
    simp only [← Functor.map_comp]
    rw [← hIH]
    rw [← (n_force_cut Hn).naturality]
    have heqn := (nm_force_cut pr1).naturality (eqToHom pr2)
    dsimp at heqn
    rw [(earlier.iter m).map_comp, earlier.map_comp]
    rw [← Category.assoc ((nm_force_cut pr1).app _)
      (earlier.map ((earlier.iter m).map (eqToHom pr2)))
      (earlier.map ((earlier.iter m).map C))]
    erw [← heqn]; clear heqn
    rw [← Category.assoc]
    have heqAdd : (earlier.iter (List.length Ψ)).obj ((earlier.iter p).obj ⟦List.drop p (List.drop (List.length Ψ) (Ψ ++ Γ))⟧ₛ)
        = (earlier.iter (List.length Ψ + p)).obj ⟦List.drop (List.length Ψ + p) (Ψ ++ Γ)⟧ₛ := by
      rw [iter_add_comm, iter_add]; simp
    rw [interp_ctx_split_add _ _ _ heqAdd]
    rw [Category.assoc]
    congr 1
    rw [Category.assoc]
    congr 1
    symm
    rw [(earlier.iter (List.length Ψ)).map_comp]
    rw [(earlier.iter (List.length Ψ)).map_comp]
    rw [(earlier.iter (List.length Ψ)).map_comp]
    rw [(earlier.iter (List.length Ψ)).map_comp]
    rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc]
    rw [(n_force_cut Hn).naturality]
    have r : (earlier.iter (List.length Ψ)).obj ((earlier.iter p).obj ⟦List.drop p Γ⟧ₛ)
      = (earlier.iter (List.length Ψ + p)).obj ⟦List.drop p Γ⟧ₛ := by
      rw [iter_add_comm, iter_add]; simp
    have hco := nm_force_cut_hsplit Hn hm pr1 ⟦List.drop p Γ⟧ₛ r
    rw [← Category.assoc ((earlier.iter (List.length Ψ)).map ((nm_force_cut hm).app _))]
    rw [hco]; clear hco
    rw [← Category.assoc, ← Category.assoc, ← Category.assoc, ← Category.assoc]
    simp only [← Category.assoc]
    apply congrArg (· ≫ earlier.map ((earlier.iter m).map C))
    apply congrArg (· ≫ (nm_force_cut pr1).app ⟦List.drop p Γ⟧ₛ)
    rw [comp_eqToHom_iff, Category.assoc, Category.assoc]
    symm
    rw [eqToHom_map, eqToHom_trans]
    rw [Category.assoc, eqToHom_trans, eqToHom_map]
    symm
    rw [eqToHom_comp_iff]
    generalize_proofs P1 P2
    clear r heqAdd hIH C S hm pr1 Hn
    simp
    rw [← Category.assoc]
    have P1' : (⟦Γ⟧ₛ : ℐ.{i}) = ⟦List.drop (List.length Ψ) (Ψ ++ Γ)⟧ₛ := by
      grind only [= List.drop_zero, = List.drop_append, = List.drop_length]
    symm
    rw [← eqToHom_map _ P1']; clear P1
    rw [← (earlier.iter (List.length Ψ)).map_comp]
    have P2' : (earlier.iter p).obj ⟦List.drop p Γ⟧ₛ
        = (earlier.iter p).obj ⟦List.drop p (List.drop (List.length Ψ) (Ψ ++ Γ))⟧ₛ := by
      grind only [= List.drop_zero, = List.drop_append, = List.drop_length]
    rw [← eqToHom_map _ (Eq.symm P2')]; clear P2
    rw [← (earlier.iter (List.length Ψ)).map_comp]
    rw [← (earlier.iter (List.length Ψ)).map_comp]
    rw [← (earlier.iter (List.length Ψ)).map_comp]
    congr 1
    revert P1' P2'
    induction Ψ with
    | nil =>
      intro P1' P2'
      rfl
    | cons x xs IH =>
      intro P1' P2'
      exact IH (by simp) (by simp) P1' P2'

  lemma cut_ssubst_split_fst {σ : SSUBST} {Δ Γ : CTX.{i}} (H : TSSUBST σ Δ Γ) :
      ∀ (m : Nat) (G2 : m < Γ.length) (p3 : m ≤ offset_ssubst σ m),
      (((interp_ctx_split Δ (i := offset_ssubst σ m)).hom
            ≫ fst ((earlier.iter (offset_ssubst σ m)).obj ⟦List.drop (offset_ssubst σ m) Δ⟧ₛ)
              ⟦List.take (offset_ssubst σ m) Δ⟧ₛ)
          ≫ (nm_force_cut p3).app ⟦List.drop (offset_ssubst σ m) Δ⟧ₛ)
        ≫ (earlier.iter m).map ⟦cut_ssubst_typing σ H m G2⟧ₛₛ
      = (⟦H⟧ₛₛ ≫ (interp_ctx_split Γ (i := m)).hom)
        ≫ fst ((earlier.iter m).obj ⟦List.drop m Γ⟧ₛ) ⟦List.take m Γ⟧ₛ := by
    induction H with
    | single σ Hσ =>
      intro m
      cases m; swap
      . intro p; exfalso; simp at p
      . simp [cut_ssubst_typing, interp_ctx, nm_force_cut_id]
        rw [rightUnitor_inv_fst_single, Category.comp_id]
    | @wk σs Γ Δs σ Ψ Δ n Hn Hneq Hσs Hσ IH =>
      intro m
      cases m with
      | zero =>
        simp [interp_ctx, cut_ssubst_typing, nm_force_cut_id]
      | succ m =>
        simp
        intro p1 p2
        simp [cut_ssubst_typing]
        simp [interp_tssubst, interp_ssubst_wk, interp_ctx]
        subst Hneq
        generalize_proofs pr1 pr2 pr3 pr4
        refine Eq.trans ?_ (whisker_eq _ (split_cons_fst Δ Δs m)).symm
        refine Eq.trans ?_ (lift_snd_assoc _ _ _).symm
        exact bindadv_wk_core Ψ Γ Δs m (offset_ssubst σs m) Hn
          (offset_ssubst_len' σs Hσs m p1) pr1 pr2 pr4
          ⟦cut_ssubst_typing σs Hσs m pr3⟧ₛₛ ⟦Hσs⟧ₛₛ
          (IH m p1 (offset_ssubst_len' σs Hσs m p1))

  lemma eq_bind_adv (H : TSSUBST σ Δ Γ)
    (G2 : n + 1 < List.length Γ)
    (IH : ⟦List.drop (offset_ssubst σ (n + 1)) Δ,binds (cut_ssubst σ (n + 1)) a,TYPE.later τ⟧ₑ
      = Part.map (fun x ↦ ⟦cut_ssubst_typing σ H (n + 1) G2⟧ₛₛ ≫ x) ⟦Γ.drop (n + 1),a,TYPE.later τ⟧ₑ)
    : ⟦Δ,binds σ (EXPR.adv (n + 1) a),τ⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦Γ,EXPR.adv (n + 1) a,τ⟧ₑ := by
    simp only [binds]
    simp only [expr_interp]
    rw [Part.assert_pos]; swap
    . apply offset_ssubst_pos
      . assumption
      . simp
    . simp
      rw [Part.assert_pos]; swap
      . simp
      . simp
        rw [IH]
        . simp
          clear IH
          congr
          clear a
          ext y a; simp
          generalize_proofs p1 p2
          suffices this : interp_adv (offset_ssubst σ (n + 1)) p1 (⟦cut_ssubst_typing σ H (n + 1) G2⟧ₛₛ ≫ y)
            = ⟦H⟧ₛₛ ≫ interp_adv (n + 1) p2 y
          rw [this]
          clear a
          simp only [interp_adv]
          simp only [interp_ty] at y ⊢
          have heq : (earlier_later_adj.homEquiv ⟦List.drop (offset_ssubst σ (n + 1)) Δ⟧ₛ ⟦τ⟧ₜ).invFun
              (⟦cut_ssubst_typing σ H (n + 1) G2⟧ₛₛ ≫ y)
              = earlier.map ⟦cut_ssubst_typing σ H (n + 1) G2⟧ₛₛ ≫ (earlier_later_adj.homEquiv _ _).invFun y := by
              rfl
          rw [heq]; clear heq
          simp [-iter]; simp only [← Category.assoc]
          congr 1; simp [-iter]
          clear y
          have p3 := offset_ssubst_len' σ H (n + 1) G2
          rw [n_force_cut_nm p2 p1 p3]
          clear p1
          simp [-iter]
          rw [←(n_force_cut p2).naturality]
          simp only [← Category.assoc]
          congr 1
          exact cut_ssubst_split_fst H (n + 1) G2 p3

  lemma eq_bind_adv' (H : TSSUBST σ Δ Γ)
    (H' : TYPED Γ (EXPR.adv n a) τ)
    (G : n < List.length Γ)
    (IH : ⟦List.drop (offset_ssubst σ n) Δ,binds (cut_ssubst σ n) a,TYPE.later τ⟧ₑ
      = Part.map (fun x ↦ ⟦cut_ssubst_typing σ H n G⟧ₛₛ ≫ x) ⟦Γ.drop n,a,TYPE.later τ⟧ₑ)
    : ⟦Δ,binds σ (EXPR.adv n a),τ⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦Γ,EXPR.adv n a,τ⟧ₑ := by
    cases n with
    | zero =>
      obtain ⟨G1, G2⟩ := TYPED.adv_inversion H'
      exfalso; simp at G1
    | succ n => apply eq_bind_adv H G IH

  lemma eq_bind_fix (H : TSSUBST σ (Δ :: Δs) (Γ :: Γs))
    (IH : ⟦((τ.later :: Δ) :: Δs),binds σ.ext' a,τ⟧ₑ = Part.map (fun x ↦ ⟦TSSUBST.ext_typing H⟧ₛₛ ≫ x) ⟦((τ.later :: Γ) :: Γs),a,τ⟧ₑ)
    : ⟦(Δ :: Δs),binds σ (EXPR.fix' (TYPE.later τ) a),τ⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦(Γ :: Γs),EXPR.fix' (TYPE.later τ) a,τ⟧ₑ := by
    simp only [binds]
    simp only [expr_interp]
    rw [IH, sext_typing_interp]
    ext γ
    simp
    constructor
    . intro ⟨a, ⟨G, HEQ⟩⟩
      rw [HEQ]; clear HEQ
      exists a
      refine ⟨G, ?_⟩
      simp only [interp_fix, fixpoint, interp_ctx, interp_octx, interp_ty, Iso.inv_hom_id_assoc,
        MonoidalClosed.curry_natural_left, Category.assoc]
    . intro ⟨a, ⟨G, HEQ⟩⟩
      rw [HEQ]; clear HEQ
      exists a
      refine ⟨G, ?_⟩
      simp only [interp_fix, fixpoint, interp_ctx, interp_octx, interp_ty, Iso.inv_hom_id_assoc,
        MonoidalClosed.curry_natural_left, Category.assoc]

  lemma eq_bind_pair (H : TSSUBST σ Δ Γ)
    (IH1 : ⟦Δ,binds σ a,A⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦Γ,a,A⟧ₑ)
    (IH2 : ⟦Δ,binds σ b,B⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦Γ,b,B⟧ₑ)
    : ⟦Δ,binds σ (EXPR.pair a b),TYPE.prod A B⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦Γ,(EXPR.pair a b),TYPE.prod A B⟧ₑ := by
    simp only [binds]
    simp [expr_interp]
    rw [IH1, IH2]
    rfl

  lemma eq_bind_proj1 (H : TSSUBST σ Δ Γ)
    (IH : ⟦Δ,binds σ a,TYPE.prod τ A⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦Γ,a,TYPE.prod τ A⟧ₑ)
    : ⟦Δ,binds σ (EXPR.proj A a .L),τ⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦Γ,EXPR.proj A a .L,τ⟧ₑ := by
    simp only [binds]
    simp [expr_interp]
    rw [IH]
    rfl

  lemma eq_bind_proj2 (H : TSSUBST σ Δ Γ)
    (IH : ⟦Δ,binds σ a,TYPE.prod A τ⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦Γ,a,TYPE.prod A τ⟧ₑ)
    : ⟦Δ,binds σ (EXPR.proj A a .R),τ⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦Γ,EXPR.proj A a .R,τ⟧ₑ := by
    simp only [binds]
    simp [expr_interp]
    rw [IH]
    rfl

  lemma eq_bind_inl {A B : TYPE.{i}} (H : TSSUBST σ Δ Γ)
    (IH : ⟦Δ,binds σ a,A⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦Γ,a,A⟧ₑ)
    : ⟦Δ,binds σ (EXPR.inl B a),TYPE.sum A B⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦Γ,(EXPR.inl B a),TYPE.sum A B⟧ₑ := by
    simp only [binds]
    simp [expr_interp, interp_inl]
    rw [IH]
    rfl

  lemma eq_bind_inr {A B : TYPE.{i}} (H : TSSUBST σ Δ Γ)
    (IH : ⟦Δ,binds σ a,B⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦Γ,a,B⟧ₑ)
    : ⟦Δ,binds σ (EXPR.inr A a),TYPE.sum A B⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦Γ,(EXPR.inr A a),TYPE.sum A B⟧ₑ := by
    simp only [binds]
    simp [expr_interp, interp_inr]
    rw [IH]
    rfl

  lemma eq_bind_case {A B C : TYPE.{i}} (H : TSSUBST σ Δ Γ)
    (IHe : ⟦Δ,binds σ e,TYPE.sum A B⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦Γ,e,TYPE.sum A B⟧ₑ)
    (IHf : ⟦Δ,binds σ f,TYPE.arr A C⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦Γ,f,TYPE.arr A C⟧ₑ)
    (IHg : ⟦Δ,binds σ g,TYPE.arr B C⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦Γ,g,TYPE.arr B C⟧ₑ)
    : ⟦Δ,binds σ (EXPR.case A B e f g),C⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦Γ,(EXPR.case A B e f g),C⟧ₑ := by
    simp only [binds]
    simp [expr_interp, interp_case]
    rw [IHe, IHf, IHg]
    simp only [Part.bind_map, ← comp_lift, Category.assoc]

  lemma eq_bind_or (H : TSSUBST σ Δ Γ)
    (IH1 : ⟦Δ,binds σ a,TYPE.prop⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦Γ,a,TYPE.prop⟧ₑ)
    (IH2 : ⟦Δ,binds σ b,TYPE.prop⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦Γ,b,TYPE.prop⟧ₑ)
    : ⟦Δ,binds σ (EXPR.or a b),TYPE.prop⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦Γ,EXPR.or a b,TYPE.prop⟧ₑ := by
    simp only [binds]
    simp [expr_interp]
    rw [IH1, IH2]
    rfl

  lemma eq_bind_and (H : TSSUBST σ Δ Γ)
    (IH1 : ⟦Δ,binds σ a,TYPE.prop⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦Γ,a,TYPE.prop⟧ₑ)
    (IH2 : ⟦Δ,binds σ b,TYPE.prop⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦Γ,b,TYPE.prop⟧ₑ)
    : ⟦Δ,binds σ (EXPR.and a b),TYPE.prop⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦Γ,EXPR.and a b,TYPE.prop⟧ₑ := by
    simp only [binds]
    simp [expr_interp]
    rw [IH1, IH2]
    rfl

  lemma eq_bind_impl (H : TSSUBST σ Δ Γ)
    (IH1 : ⟦Δ,binds σ a,TYPE.prop⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦Γ,a,TYPE.prop⟧ₑ)
    (IH2 : ⟦Δ,binds σ b,TYPE.prop⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦Γ,b,TYPE.prop⟧ₑ)
    : ⟦Δ,binds σ (EXPR.impl a b),TYPE.prop⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦Γ,EXPR.impl a b,TYPE.prop⟧ₑ := by
    simp only [binds]
    simp [expr_interp]
    rw [IH1, IH2]
    rfl

  lemma eq_bind_forall (H : TSSUBST σ (Δ :: Δs) (Γ :: Γs))
    (IH : ⟦((A :: Δ) :: Δs),binds σ.ext' a,TYPE.prop⟧ₑ = Part.map (fun x ↦ ⟦TSSUBST.ext_typing H⟧ₛₛ ≫ x) ⟦((A :: Γ) :: Γs),a,TYPE.prop⟧ₑ)
    : ⟦(Δ :: Δs),binds σ (EXPR.forall' A a),TYPE.prop⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦(Γ :: Γs),EXPR.forall' A a,TYPE.prop⟧ₑ := by
    simp only [binds]
    simp only [expr_interp]
    rw [IH, sext_typing_interp]
    ext γ
    simp
    constructor
    . intro ⟨a, ⟨G, HEQ⟩⟩
      rw [HEQ]
      exact ⟨a, G, interp_forall_natural _ a⟩
    . intro ⟨a, ⟨G, HEQ⟩⟩
      rw [HEQ]
      exact ⟨a, G, (interp_forall_natural _ a).symm⟩

  lemma eq_bind_exist (H : TSSUBST σ (Δ :: Δs) (Γ :: Γs))
    (IH : ⟦((A :: Δ) :: Δs),binds σ.ext' a,TYPE.prop⟧ₑ = Part.map (fun x ↦ ⟦TSSUBST.ext_typing H⟧ₛₛ ≫ x) ⟦((A :: Γ) :: Γs),a,TYPE.prop⟧ₑ)
    : ⟦(Δ :: Δs),binds σ (EXPR.exists' A a),TYPE.prop⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦(Γ :: Γs),EXPR.exists' A a,TYPE.prop⟧ₑ := by
    simp only [binds]
    simp only [expr_interp]
    rw [IH, sext_typing_interp]
    ext γ
    simp
    constructor
    . intro ⟨a, ⟨G, HEQ⟩⟩
      rw [HEQ]
      exact ⟨a, G, interp_exists_natural _ a⟩
    . intro ⟨a, ⟨G, HEQ⟩⟩
      rw [HEQ]
      exact ⟨a, G, (interp_exists_natural _ a).symm⟩

  lemma eq_bind_lift (H : TSSUBST σ Δ Γ)
    (IH : ⟦Δ,binds σ a,TYPE.later TYPE.prop⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦Γ,a,TYPE.later TYPE.prop⟧ₑ)
    : ⟦Δ,binds σ (EXPR.lift a),TYPE.prop⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦Γ,(EXPR.lift a),TYPE.prop⟧ₑ := by
    simp only [binds]
    simp [expr_interp]
    rw [IH]
    rfl

  lemma eq_bind_true (H : TSSUBST σ Δ Γ)
    : ⟦Δ,binds σ EXPR.true,τ⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦Γ,EXPR.true,τ⟧ₑ := by
    simp only [binds]
    cases τ with
    | prop =>
      simp [expr_interp]
      rfl
    | _ => simp

  lemma eq_bind_false (H : TSSUBST σ Δ Γ)
    : ⟦Δ,binds σ EXPR.false,τ⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦Γ,EXPR.false,τ⟧ₑ := by
    simp only [binds]
    cases τ with
    | prop =>
      simp [expr_interp]
      rfl
    | _ => simp

  lemma eq_bind_eq (H : TSSUBST σ Δ Γ)
    (IH1 : ⟦Δ,binds σ a,A⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦Γ,a,A⟧ₑ)
    (IH2 : ⟦Δ,binds σ b,A⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦Γ,b,A⟧ₑ)
    : ⟦Δ,binds σ (EXPR.eq A a b),τ⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦Γ,EXPR.eq A a b,τ⟧ₑ := by
    simp only [binds]
    cases τ with
    | prop =>
      simp [expr_interp]
      rw [IH1, IH2]
      rfl
    | _ => simp

  lemma eq_bind_ax (H : TSSUBST σ Δ Γ)
    : ⟦Δ,binds σ (EXPR.ax A a),τ⟧ₑ = Part.map (fun x ↦ ⟦H⟧ₛₛ ≫ x) ⟦Γ,EXPR.ax A a,τ⟧ₑ := by
    simp only [binds]
    simp only [expr_interp]
    rfl

  lemma uncons_of_typed {Γ : CTX.{i}} {e : EXPR.{i}} {τ : TYPE.{i}} (H : TYPED Γ e τ) :
      ∃ (Γ₀ : OCTX.{i}) (Γs : CTX.{i}), Γ = Γ₀ :: Γs := by
    cases Γ with
    | nil => simpa using typing_stack_len H
    | cons Γ₀ Γs => exact ⟨Γ₀, Γs, rfl⟩

  lemma uncons_of_ssubst {σ : SSUBST} {Δ Γ : CTX.{i}} (H : TSSUBST σ Δ Γ) :
      ∃ (Δ₀ : OCTX.{i}) (Δs : CTX.{i}), Δ = Δ₀ :: Δs := by
    cases Δ with
    | nil => simpa using ssubst_len _ H
    | cons Δ₀ Δs => exact ⟨Δ₀, Δs, rfl⟩

  theorem eq_bind (Γ : CTX.{i}) (e : EXPR.{i}) (τ : TYPE.{i})
    (H : TSSUBST σ Δ Γ)
    (H' : TYPED Γ e τ)
    : expr_interp Δ (binds σ e) τ = (expr_interp Γ e τ).map (fun x => interp_tssubst H ≫ x) := by
    revert Δ σ Γ τ H H'
    induction e with
    | embed A a =>
      intro σ Δ Γ τ H H'
      apply eq_bind_embed
    | embed_apply A B a b IH1 IH2 =>
      intro σ Δ Γ τ H H'
      obtain ⟨G1, G2, G3⟩ := TYPED.embed_apply_inversion H'
      rw [G1]
      apply eq_bind_embed_apply
      . apply IH1; assumption
      . apply IH2; assumption
    | pure a IH =>
      intro σ Δ Γ τ H H'
      obtain ⟨G1, G2⟩ := TYPED.pure_inversion H'
      rw [G1]
      apply eq_bind_pure
      apply IH; assumption
    | var' n m =>
      intro σ Δ Γ τ H H'
      apply eq_bind_var
      assumption
    | app A a b IH1 IH2 =>
      intro σ Δ Γ τ H H'
      obtain ⟨G1, G2⟩ := TYPED.app_inversion H'
      apply eq_bind_app
      . apply IH1; assumption
      . apply IH2; assumption
    | lam' A a IH =>
      intro σ Δ Γ τ H H'
      obtain ⟨Γ, Γs, rfl⟩ := uncons_of_typed H'
      obtain ⟨Δ, Δs, rfl⟩ := uncons_of_ssubst H
      obtain ⟨τ', G1, G2⟩ := TYPED.lam'_inversion H'
      rw [G1]
      apply eq_bind_lam
      apply IH; assumption
    | delay a IH =>
      intro σ Δ Γ τ H H'
      obtain ⟨τ', G1, G2⟩ := TYPED.delay_inversion H'
      rw [G1]
      apply eq_bind_delay
      . apply IH; assumption
      . simp
    | adv n a IH =>
      intro σ Δ Γ τ H H'
      obtain ⟨G1, G2⟩ := TYPED.adv_inversion H'
      apply eq_bind_adv'
      . assumption
      . apply IH
        assumption
      . have J := typing_stack_len G2
        grind only [= List.length_drop, cases Or]
    | fix' A a IH =>
      intro σ Δ Γ τ H H'
      obtain ⟨Γ, Γs, rfl⟩ := uncons_of_typed H'
      obtain ⟨Δ, Δs, rfl⟩ := uncons_of_ssubst H
      obtain ⟨G1, G2⟩ := TYPED.fix'_inversion H'
      rw [G1]
      apply eq_bind_fix
      apply IH; assumption
    | pair a b IH1 IH2 =>
      intro σ Δ Γ τ H H'
      obtain ⟨τ1, τ2, G1, G2, G3⟩ := TYPED.pair_inversion H'
      rw [G1]
      apply eq_bind_pair
      . apply IH1; assumption
      . apply IH2; assumption
    | proj A a d IH =>
      intro σ Δ Γ τ H H'
      cases d with
      | L =>
        apply eq_bind_proj1
        apply IH; exact TYPED.projL_inversion H'
      | R =>
        apply eq_bind_proj2
        apply IH; exact TYPED.projR_inversion H'
    | inl B a IH =>
      intro σ Δ Γ τ H H'
      obtain ⟨A', G1, G2⟩ := TYPED.inl_inversion H'
      rw [G1]
      apply eq_bind_inl
      apply IH; assumption
    | inr A a IH =>
      intro σ Δ Γ τ H H'
      obtain ⟨B', G1, G2⟩ := TYPED.inr_inversion H'
      rw [G1]
      apply eq_bind_inr
      apply IH; assumption
    | case A B e f g IHe IHf IHg =>
      intro σ Δ Γ τ H H'
      obtain ⟨Ge, Gf, Gg⟩ := TYPED.case_inversion H'
      apply eq_bind_case
      · apply IHe; assumption
      · apply IHf; assumption
      · apply IHg; assumption
    | or a b IH1 IH2 =>
      intro σ Δ Γ τ H H'
      obtain ⟨G1, G2, G3⟩ := TYPED.or_inversion H'
      rw [G1]
      apply eq_bind_or
      . apply IH1; assumption
      . apply IH2; assumption
    | and a b IH1 IH2 =>
      intro σ Δ Γ τ H H'
      obtain ⟨G1, G2, G3⟩ := TYPED.and_inversion H'
      rw [G1]
      apply eq_bind_and
      . apply IH1; assumption
      . apply IH2; assumption
    | impl a b IH1 IH2 =>
      intro σ Δ Γ τ H H'
      obtain ⟨G1, G2, G3⟩ := TYPED.impl_inversion H'
      rw [G1]
      apply eq_bind_impl
      . apply IH1; assumption
      . apply IH2; assumption
    | forall' A a IH =>
      intro σ Δ Γ τ H H'
      obtain ⟨Γ, Γs, rfl⟩ := uncons_of_typed H'
      obtain ⟨Δ, Δs, rfl⟩ := uncons_of_ssubst H
      obtain ⟨G1, G2⟩ := TYPED.forall'_inversion H'
      rw [G1]
      apply eq_bind_forall
      apply IH; assumption
    | exists' A a IH =>
      intro σ Δ Γ τ H H'
      obtain ⟨Γ, Γs, rfl⟩ := uncons_of_typed H'
      obtain ⟨Δ, Δs, rfl⟩ := uncons_of_ssubst H
      obtain ⟨G1, G2⟩ := TYPED.exists'_inversion H'
      rw [G1]
      apply eq_bind_exist
      apply IH; assumption
    | lift a IH =>
      intro σ Δ Γ τ H H'
      obtain ⟨G1, G2⟩ := TYPED.lift_inversion H'
      rw [G1]
      apply eq_bind_lift
      apply IH; assumption
    | true =>
      intro σ Δ Γ τ H H'
      apply eq_bind_true
    | false =>
      intro σ Δ Γ τ H H'
      apply eq_bind_false
    | eq A a b IH1 IH2 =>
      intro σ Δ Γ τ H H'
      obtain ⟨G1, G2, G3⟩ := TYPED.eq_inversion H'
      apply eq_bind_eq
      . apply IH1; assumption
      . apply IH2; assumption
    | ax A a =>
      intro σ Δ Γ τ H H'
      apply eq_bind_ax

  lemma associator_inv_whiskerLeft {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] (X Y Y' Z Z' : C)
    (f : Y' ⟶ Y) (g : Z' ⟶ Z) :
      (X ◁ (f ⊗ₘ g)) ≫ (α_ X Y Z).inv = (α_ X Y' Z').inv ≫ ((X ◁ f) ⊗ₘ g) := by
    apply CartesianMonoidalCategory.hom_ext
    . simp; apply CartesianMonoidalCategory.hom_ext <;> simp
    . simp

  lemma associator_hom_whiskerRight {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] (X X' Y Z Z' : C)
    (f : X' ⟶ X) (g : Z' ⟶ Z) :
      ((f ▷ Y) ⊗ₘ g) ≫ (α_ X Y Z).hom = (α_ X' Y Z').hom ≫ (f ⊗ₘ (Y ◁ g)) := by
    apply CartesianMonoidalCategory.hom_ext
    . simp
    . simp; apply CartesianMonoidalCategory.hom_ext <;> simp

  lemma braiding_hom_whiskerLeft {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    [BraidedCategory C]
    (X Y Y' Z Z' : C)
    (f : Y' ⟶ Y) (g : Z' ⟶ Z) :
      ((X ◁ f) ⊗ₘ g) ≫ ((β_ X Y).hom ▷ Z) = ((β_ X Y').hom ▷ Z') ≫ ((f ▷ _) ⊗ₘ g) := by
    apply CartesianMonoidalCategory.hom_ext
    . simp
    . simp

  lemma wk_delay_hRHS (Γ Γ' : OCTX.{i}) (hΓ : Γ' = Γ) (L L' : CTX.{i}) (p6 : L = L') (n : ℕ)
    {Z : ℐ.{i}}
    (p3 : (⟦Γ⟧ₒ ⊗ earlier.obj ⟦L'⟧ₛ : ℐ.{i}) = ⟦Γ'⟧ₒ ⊗ earlier.obj ⟦L⟧ₛ)
    (q1 : (⟦List.drop n L⟧ₛ : ℐ.{i}) = ⟦List.drop n L'⟧ₛ)
    (T : earlier.obj ⟦List.drop n L'⟧ₛ ⟶ Z) :
    eqToHom (Eq.symm p3) ≫ snd ⟦Γ⟧ₒ (earlier.obj ⟦L'⟧ₛ)
      ≫ earlier.map (interp_ctx_split L' (i := n)).hom
      ≫ earlier.map (fst ((earlier.iter n).obj ⟦List.drop n L'⟧ₛ) ⟦List.take n L'⟧ₛ)
      ≫ earlier.map ((n_force (i := n)).app ⟦List.drop n L'⟧ₛ)
      ≫ T
    = snd ⟦Γ'⟧ₒ (earlier.obj ⟦L⟧ₛ)
      ≫ earlier.map (interp_ctx_split L (i := n)).hom
      ≫ earlier.map (fst ((earlier.iter n).obj ⟦List.drop n L⟧ₛ) ⟦List.take n L⟧ₛ)
      ≫ earlier.map ((n_force (i := n)).app ⟦List.drop n L⟧ₛ)
      ≫ earlier.map (eqToHom q1)
      ≫ T := by
    subst hΓ
    subst p6
    simp

  lemma wk_delay_lwl (Γ : OCTX.{i}) (L1 L2 : CTX.{i}) (n : ℕ)
    (p4 : n = L1.length) (p5 : 0 < L2.length)
    (q1 : (⟦List.drop n (L1 ++ L2)⟧ₛ : ℐ.{i}) = ⟦L2⟧ₛ) :
    ⟦local_weaken_list_typed Γ (TYPED_REN.global_shift n p4 (TYPED_REN.id p5)).global_lift⟧ᵣ
    = snd ⟦Γ ++ []⟧ₒ (earlier.obj ⟦L1 ++ L2⟧ₛ)
      ≫ earlier.map (interp_ctx_split (L1 ++ L2) (i := n)).hom
      ≫ earlier.map (fst ((earlier.iter n).obj ⟦List.drop n (L1 ++ L2)⟧ₛ) ⟦List.take n (L1 ++ L2)⟧ₛ)
      ≫ earlier.map ((n_force (i := n)).app ⟦List.drop n (L1 ++ L2)⟧ₛ)
      ≫ earlier.map (eqToHom q1)
      ≫ earlier.map (λ_ ⟦L2⟧ₛ).inv
      ≫ OplaxMonoidal.δ earlier (𝟙_ ℐ) ⟦L2⟧ₛ
      ≫ OplaxMonoidal.η earlier ▷ earlier.obj ⟦L2⟧ₛ := by
    subst p4
    induction Γ with
    | nil =>
      simp only [List.nil_append, local_weaken_list_typed, interp_typed_ren,
        interp_ren_global_lift, interp_ren_global_shift, interp_ren_id,
        interp_ctx, interp_octx]
      simp
      rw [leftUnitor_hom]
      generalize_proofs q2
      rw [show eqToHom q2 = (earlier.iter L1.length).map (eqToHom q1) from by
        rw [← eqToHom_map]]
      have hnat := (n_force (i := L1.length)).naturality (eqToHom q1)
      dsimp only [Functor.id_obj, Functor.id_map] at hnat
      have hnat' := congrArg earlier.map hnat
      simp only [Functor.map_comp] at hnat'
      erw [reassoc_of% hnat']
    | cons x xs IH =>
      simp only [List.cons_append, local_weaken_list_typed, interp_typed_ren,
        interp_ren_local_weaken, interp_ctx, interp_octx]
      rw [IH]
      simp

  lemma wk_delay_interp (n : ℕ)
    (Hlt : 0 < n + 1) (Hlt' : n + 1 < Γ.length) (Hlt'' : 0 < List.length Γ) :
    ⟦TYPED_REN.wk_delay Γ n Hlt' Hlt''⟧ᵣ =
    (interp_ctx_split Γ).hom ≫
      fst ((earlier.iter (n + 1)).obj ⟦List.drop (n + 1) Γ⟧ₛ) ⟦List.take (n + 1) Γ⟧ₛ
        ≫ (n_force_cut Hlt).app ⟦List.drop (n + 1) Γ⟧ₛ
        ≫ (λ_ (earlier.obj ⟦List.drop (n + 1) Γ⟧ₛ)).inv := by
    cases Γ with
    | nil => exfalso; simp at Hlt''
    | cons Γ Γs =>
      simp [interp_ctx_split, interp_ctx, interp_octx]
      simp [TYPED_REN.wk_delay]
      generalize_proofs p1 p2 p3
      clear Hlt'' Hlt'
      simp [n_force_cut]
      revert p1 p2 p3
      simp [interp_ctx, interp_octx]
      intro p1 p2
      generalize_proofs p3 p4 p5
      show eqToHom p3 ≫ ⟦local_weaken_list_typed Γ (TYPED_REN.global_shift n p4 (TYPED_REN.id p5)).global_lift⟧ᵣ
        = ⟦Γ⟧ₒ ◁ earlier.map (interp_ctx_split Γs (i := n)).hom
          ≫ ⟦Γ⟧ₒ ◁ earlier_prod.hom.app ((earlier.iter n).obj ⟦List.drop n Γs⟧ₛ, ⟦List.take n Γs⟧ₛ)
          ≫ (α_ ⟦Γ⟧ₒ (earlier.obj ((earlier.iter n).obj ⟦List.drop n Γs⟧ₛ)) (earlier.obj ⟦List.take n Γs⟧ₛ)).inv
          ≫ (β_ ⟦Γ⟧ₒ (earlier.obj ((earlier.iter n).obj ⟦List.drop n Γs⟧ₛ))).hom ▷ earlier.obj ⟦List.take n Γs⟧ₛ
          ≫ (α_ (earlier.obj ((earlier.iter n).obj ⟦List.drop n Γs⟧ₛ)) ⟦Γ⟧ₒ (earlier.obj ⟦List.take n Γs⟧ₛ)).hom
          ≫ fst (earlier.obj ((earlier.iter n).obj ⟦List.drop n Γs⟧ₛ)) (⟦Γ⟧ₒ ⊗ earlier.obj ⟦List.take n Γs⟧ₛ)
          ≫ earlier.map ((n_force (i := n)).app ⟦List.drop n Γs⟧ₛ)
          ≫ earlier.map (λ_ ⟦List.drop n Γs⟧ₛ).inv
          ≫ OplaxMonoidal.δ earlier (𝟙_ ℐ) ⟦List.drop n Γs⟧ₛ
          ≫ OplaxMonoidal.η earlier ▷ earlier.obj ⟦List.drop n Γs⟧ₛ
      have eqR := congrArg
        ((⟦Γ⟧ₒ ◁ earlier.map (interp_ctx_split Γs (i := n)).hom
          ≫ ⟦Γ⟧ₒ ◁ earlier_prod.hom.app ((earlier.iter n).obj ⟦List.drop n Γs⟧ₛ, ⟦List.take n Γs⟧ₛ)) ≫ ·)
        (cart_tail_chase_assoc ⟦Γ⟧ₒ (earlier.obj ((earlier.iter n).obj ⟦List.drop n Γs⟧ₛ))
          (earlier.obj ⟦List.take n Γs⟧ₛ)
          (earlier.map ((n_force (i := n)).app ⟦List.drop n Γs⟧ₛ)
            ≫ earlier.map (λ_ ⟦List.drop n Γs⟧ₛ).inv
            ≫ OplaxMonoidal.δ earlier (𝟙_ ℐ) ⟦List.drop n Γs⟧ₛ
            ≫ OplaxMonoidal.η earlier ▷ earlier.obj ⟦List.drop n Γs⟧ₛ))
      simp only [Category.assoc] at eqR
      refine Eq.trans ?_ eqR.symm
      clear eqR
      have midR := snd_push_gen (interp_ctx_split Γs (i := n)).hom ⟦Γ⟧ₒ
        (fst (earlier.obj ((earlier.iter n).obj ⟦List.drop n Γs⟧ₛ)) (earlier.obj ⟦List.take n Γs⟧ₛ)
          ≫ earlier.map ((n_force (i := n)).app ⟦List.drop n Γs⟧ₛ)
          ≫ earlier.map (λ_ ⟦List.drop n Γs⟧ₛ).inv
          ≫ OplaxMonoidal.δ earlier (𝟙_ ℐ) ⟦List.drop n Γs⟧ₛ
          ≫ OplaxMonoidal.η earlier ▷ earlier.obj ⟦List.drop n Γs⟧ₛ)
      refine Eq.trans ?_ midR.symm
      clear midR
      have midP := congrArg
        ((snd ⟦Γ⟧ₒ (earlier.obj ⟦Γs⟧ₛ) ≫ earlier.map (interp_ctx_split Γs (i := n)).hom) ≫ ·)
        (prod_fst_earlier_assoc ((earlier.iter n).obj ⟦List.drop n Γs⟧ₛ) ⟦List.take n Γs⟧ₛ
          (earlier.map ((n_force (i := n)).app ⟦List.drop n Γs⟧ₛ)
            ≫ earlier.map (λ_ ⟦List.drop n Γs⟧ₛ).inv
            ≫ OplaxMonoidal.δ earlier (𝟙_ ℐ) ⟦List.drop n Γs⟧ₛ
            ≫ OplaxMonoidal.η earlier ▷ earlier.obj ⟦List.drop n Γs⟧ₛ))
      simp only [Category.assoc] at midP
      refine Eq.trans ?_ midP.symm
      clear midP
      refine (eqToHom_comp_iff p3 _ _).mpr ?_
      have p6 : List.take n Γs ++ List.drop n Γs = Γs := by simp
      have hΓe : Γ ++ [] = Γ := by simp
      have q1 : (⟦List.drop n (List.take n Γs ++ List.drop n Γs)⟧ₛ : ℐ) = ⟦List.drop n Γs⟧ₛ := by
        rw [p6]
      refine Eq.trans ?_ (wk_delay_hRHS Γ (Γ ++ []) hΓe (List.take n Γs ++ List.drop n Γs) Γs p6 n p3 q1
        (earlier.map (λ_ ⟦List.drop n Γs⟧ₛ).inv
          ≫ OplaxMonoidal.δ earlier (𝟙_ ℐ) ⟦List.drop n Γs⟧ₛ
          ≫ OplaxMonoidal.η earlier ▷ earlier.obj ⟦List.drop n Γs⟧ₛ)).symm
      exact wk_delay_lwl Γ (List.take n Γs) (List.drop n Γs) n p4 p5 q1

  theorem eq_interp (Γ : CTX.{i}) (e1 e2 : EXPR.{i}) (τ : TYPE.{i}) (H : EQ Γ τ e1 e2)
    : expr_interp Γ e1 τ = expr_interp Γ e2 τ := by
    induction H with
    | rfl => rfl
    | sym _ H IH => exact IH.symm
    | tran H1 H2 IH1 IH2 => exact IH1.trans IH2
    | @beta_lam' Γ Γs e' τ' e'' τ'' G1 G2 =>
      simp [expr_interp, -single_subst]
      rw [Part.Dom.bind (expr_interp_correct G2)]
      simp [-single_subst]
      rw [Part.Dom.bind (expr_interp_correct G1)]
      rw [eq_bind (σ := (single_subst (List.length Γ :: List.map List.length Γs) e'))
        (Γ := ((τ' :: Γ) :: Γs))
        (H := (TSSUBST.single_subst G1)) _ _ G2]
      rw [←Part.bind_some_eq_map, Part.Dom.bind (expr_interp_correct G2), beta_lam]
      exact congrArg Part.some (congrArg (· ≫ _) (ssubst_single_interp G1)).symm
    | @beta_delay Γ e τ n Hlt Hlt' G =>
      cases n with
      | zero => exfalso; simp at Hlt
      | succ n =>
        simp [expr_interp]
        rw [Part.assert_pos Hlt, Part.Dom.bind (expr_interp_correct G)]
        simp
        rw [beta_delay]
        symm
        rw [eq_weak (σ := (local_weaken_list (List.length (Γ[0]'(Nat.lt_trans Hlt Hlt'))) (REN.global_shift n REN.id).global_lift))
          (H := TYPED_REN.wk_delay Γ n Hlt' (by grind only)) _ e τ G]
        rw [←Part.bind_some_eq_map, Part.Dom.bind (expr_interp_correct G)]
        congr
        exact wk_delay_interp n Hlt Hlt' (by grind only)
    | @unfold' τ Δ Γ e H =>
      simp [expr_interp, -single_subst]
      rw [Part.Dom.bind (expr_interp_correct H), fixpoint_unfold']
      let qqq : TYPED_REN (REN.global_shift 1 REN.id).cons ([τ.later] :: Δ :: Γ) ((τ.later :: Δ) :: Γ) :=
        TYPED_REN.cons _ (TYPED_REN.global_shift (Ψ := [[]]) 1 (by rfl) (TYPED_REN.id (by simp)))
      have eee : TYPED (Δ :: Γ) (EXPR.fix' τ.later (weaken e (REN.global_shift 1 REN.id).cons)).delay τ.later := by
        constructor; simp
        constructor
        apply weaken_typing H qqq
      rw [eq_bind (σ := (single_subst (Δ.length :: List.map List.length Γ) (EXPR.fix' τ.later (weaken e (REN.global_shift 1 REN.id).cons)).delay))
          (Γ := ((TYPE.later τ :: Δ) :: Γ))
          (H := (TSSUBST.single_subst eee)) _ _ H]
      rw [←Part.bind_some_eq_map]
      rw [Part.Dom.bind (expr_interp_correct H)]
      congr
      have eq := ssubst_single_interp eee
      simp only [List.map] at eq
      rw [eq]; clear eq
      simp only [interp_ty]
      congr 1; congr 1
      simp [expr_interp]
      generalize_proofs p1 p2
      revert p1 p2
      rw [Part.Dom.bind (expr_interp_correct (weaken_typing H qqq))]
      simp
      have heq := eq_weak (σ := (REN.global_shift 1 REN.id).cons)
        (Δ := ([τ.later] :: Δ :: Γ)) (H := qqq) _ e τ H
      have heq' : (⟦[τ.later] :: Δ :: Γ,weaken e (REN.global_shift 1 REN.id).cons,τ⟧ₑ.get (expr_interp_correct (weaken_typing H qqq)))
        = ⟦qqq⟧ᵣ ≫ (⟦(τ.later :: Δ) :: Γ,e,τ⟧ₑ).get (expr_interp_correct H) := by
        rw [Part.get_eq_get_of_eq _ _ heq]
        rfl
      rw [heq']; clear heq' heq eee
      intro p1
      subst qqq
      have heq : p1 = expr_interp_correct H := by rfl
      rw [heq]; clear heq
      set f := ⟦(τ.later :: Δ) :: Γ,e,τ⟧ₑ.get (expr_interp_correct H)
      clear_value f
      clear p1 H e e1 e2
      revert f; simp [interp_ctx, interp_octx, interp_ty]
      intro f
      have heq : (⟦TYPED_REN.cons _ (TYPED_REN.global_shift (Ψ := [[]]) 1 (by rfl) (TYPED_REN.id (by simp)))⟧ᵣ : ⟦[τ.later] :: Δ :: Γ⟧ₛ ⟶ ⟦(τ.later :: Δ) :: Γ⟧ₛ)
        = (fst _ _ ⊗ₘ force.app _) ≫ (α_ _ _ _).inv := by
        rfl
      rw [heq]; clear heq
      simp [interp_octx, interp_ty]
      simp [interp_fix, interp_octx, interp_ctx]
      simp only [← Category.assoc]
      have heq : (((α_ (later.obj ⟦τ⟧ₜ) (𝟙_ ℐ) (earlier.obj (⟦Δ⟧ₒ ⊗ earlier.obj ⟦Γ⟧ₛ))).inv
        ≫ (fst (later.obj ⟦τ⟧ₜ) (𝟙_ ℐ) ⊗ₘ force.app (⟦Δ⟧ₒ ⊗ earlier.obj ⟦Γ⟧ₛ)))
        ≫ (α_ (later.obj ⟦τ⟧ₜ) ⟦Δ⟧ₒ (earlier.obj ⟦Γ⟧ₛ)).inv)
        = ((𝟙 _) ⊗ₘ (snd _ _ ≫ force.app _)) ≫ (α_ _ _ _).inv := by
        rfl
      simp only [Functor.id] at heq
      rw [heq]; clear heq
      simp
      simp only [interp_delay]
      set g := (α_ (later.obj ⟦τ⟧ₜ) ⟦Δ⟧ₒ (earlier.obj ⟦Γ⟧ₛ)).inv ≫ f
      clear_value g; clear f
      rw [←Category.assoc, ←MonoidalCategory.whiskerLeft_comp]
      revert g
      simp only [interp_ctx]
      set P :=  ⟦Δ⟧ₒ ⊗ earlier.obj ⟦Γ⟧ₛ
      clear_value P; clear Γ Δ; clear Γ
      set Q := ⟦τ⟧ₜ
      clear_value Q; clear τ; clear τ
      intro g
      exact fixpoint_naturality _
    | @eta_lam' Γ e τ σ Ht =>
      cases Γ with
      | nil => simpa using typing_stack_len Ht
      | cons Γ Γs =>
        simp [expr_interp]
        rw [Part.assert_pos (h := by simp)]
        rw [Part.assert_pos (h := by simp)]
        let Hσ : TYPED_REN (REN.local_weaken REN.id) ((τ :: Γ) :: Γs) (Γ :: Γs) :=
          TYPED_REN.local_weaken τ (TYPED_REN.id (by simp))
        have Ht' : TYPED ((τ :: Γ) :: Γs) (weaken e (REN.local_weaken REN.id)) (τ.arr σ) := by
            apply weaken_typing
            . assumption
            . apply Hσ
        rw [Part.Dom.bind (expr_interp_correct Ht')]
        rw [Part.bind_assoc]
        simp
        trans Part.some ((expr_interp (Γ :: Γs) e (TYPE.arr τ σ)).get (expr_interp_correct Ht)); simp
        rw [eta_lam' ((expr_interp (Γ :: Γs) e (TYPE.arr τ σ)).get (expr_interp_correct Ht))]
        congr
        symm
        trans (Part.map (fun x ↦ ⟦Hσ⟧ᵣ ≫ x) ⟦Γ :: Γs,e,τ.arr σ⟧ₑ).get (expr_interp_correct Ht)
        . congr
          rw [eq_weak (σ := REN.local_weaken REN.id) (H := Hσ) _ e _ Ht]
        . simp
          rw [←Category.assoc]
          congr
    | @eta_delay Γ e τ Ht =>
      simp [expr_interp]
      rw [Part.assert_pos (h := by simp)]
      change (⟦Γ,e,τ.later⟧ₑ = (⟦Γ,e,τ.later⟧ₑ.bind _).bind _)
      rw [Part.Dom.bind (expr_interp_correct Ht)]
      simp
      rw [←eta_delay]
      simp
    | @beta_embed_apply Γ A B f x G1 =>
      simp [expr_interp]
      rw [Part.assert_pos (h := by simp)]
      rw [Part.assert_pos (h := by simp)]
      rw [Part.assert_pos (h := by simp)]
      simp
      rw [Part.assert_pos (h := by simp)]
      congr
    | beta_prod_l H1 H2 =>
      simp [expr_interp]
      rw [Part.Dom.bind (expr_interp_correct H1), Part.Dom.bind (expr_interp_correct H2)]
      simp
      rw [beta_prod_l]
      simp
    | beta_prod_r H1 H2 =>
      simp [expr_interp]
      rw [Part.Dom.bind (expr_interp_correct H1), Part.Dom.bind (expr_interp_correct H2)]
      simp
      rw [beta_prod_r]
      simp
    | eta_prod H =>
      simp [expr_interp]
      rw [Part.Dom.bind (expr_interp_correct H)]
      simp
      rw [Part.Dom.bind (expr_interp_correct H)]
      simp
      rw [←eta_prod]
      simp
    | beta_case_inl Ha Hf Hg =>
      simp [expr_interp]
      rw [Part.assert_pos (h := rfl), Part.Dom.bind (expr_interp_correct Ha), Part.bind_some,
        Part.Dom.bind (expr_interp_correct Hf), Part.Dom.bind (expr_interp_correct Hg),
        Part.Dom.bind (expr_interp_correct Hf), Part.Dom.bind (expr_interp_correct Ha),
        interp_case_inl]
    | beta_case_inr Hb Hf Hg =>
      simp [expr_interp]
      rw [Part.assert_pos (h := rfl), Part.Dom.bind (expr_interp_correct Hb), Part.bind_some,
        Part.Dom.bind (expr_interp_correct Hf), Part.Dom.bind (expr_interp_correct Hg),
        Part.Dom.bind (expr_interp_correct Hg), Part.Dom.bind (expr_interp_correct Hb),
        interp_case_inr]
    | cong_inl _ IH =>
      simp [expr_interp]
      rw [IH]
    | cong_inr _ IH =>
      simp [expr_interp]
      rw [IH]
    | cong_case _ _ _ IHe IHf IHg =>
      simp [expr_interp]
      rw [IHe, IHf, IHg]
    | cong_app _ _ IH1 IH2 =>
      simp [expr_interp]
      rw [IH1, IH2]
    | cong_embed_apply _ _ IH1 IH2 =>
      simp [expr_interp]
      rw [IH1, IH2]
    | cong_pure _ IH =>
      simp [expr_interp]
      rw [IH]
    | cong_lam' H IH =>
      simp [expr_interp]
      rw [IH]
    | cong_delay _ H IH =>
      simp [expr_interp]
      rw [IH]
    | cong_adv n H _ IH =>
      simp [expr_interp]
      rw [IH]
    | cong_fix' H IH =>
      simp [expr_interp]
      rw [IH]
    | cong_pair _ _ IH1 IH2 =>
      simp [expr_interp]
      rw [IH1, IH2]
    | cong_or _ _ IH1 IH2 =>
      simp [expr_interp]
      rw [IH1, IH2]
    | cong_and _ _ IH1 IH2 =>
      simp [expr_interp]
      rw [IH1, IH2]
    | cong_impl _ _ IH1 IH2 =>
      simp [expr_interp]
      rw [IH1, IH2]
    | cong_forall' _ IH =>
      simp [expr_interp]
      rw [IH]
    | cong_exists' _ IH =>
      simp [expr_interp]
      rw [IH]
    | cong_proj1 _ IH =>
      simp [expr_interp]
      rw [IH]
    | cong_proj2 _ IH =>
      simp [expr_interp]
      rw [IH]
    | cong_lift _ IH =>
      simp [expr_interp]
      rw [IH]
    | cong_eq _ _ IH1 IH2 =>
      simp [expr_interp]
      rw [IH1, IH2]
    | ax H1 H2 eq =>
      assumption
end interp
