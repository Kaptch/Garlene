module

public import Lean

public import SynthDom.Syntax.Prf.Core
public import SynthDom.Syntax.Prf.Weaken
public import SynthDom.Syntax.Expr.Typecheck
public import SynthDom.Syntax.Utils

@[expose] public section

section prf

open Lean

unseal EXPR.forall in
theorem PROVES.forall_intro : PROVES ((τ :: Γ) :: Γs) (intro_wrap Ψ) Φ → PROVES (Γ :: Γs) Ψ (.forall nm τ Φ) := PROVES.forall_intro'
unseal EXPR.forall in
theorem PROVES.forall_elim τ Φ e : TYPED ((τ :: Γ) :: Γs) Φ TYPE.prop → PROVES (Γ :: Γs) Ψ (.forall nm τ Φ) → TYPED (Γ :: Γs) e τ → PROVES (Γ :: Γs) Ψ (binds (single_subst (List.map List.length (Γ :: Γs)) e) Φ) := PROVES.forall_elim' τ Φ e
unseal EXPR.exists in
theorem PROVES.exists_intro τ Φ e : TYPED ((τ :: Γ) :: Γs) Φ TYPE.prop → TYPED (Γ :: Γs) e τ → PROVES (Γ :: Γs) Ψ (binds (single_subst (List.map List.length (Γ :: Γs)) e) Φ) → PROVES (Γ :: Γs) Ψ (.exists nm τ Φ) := PROVES.exists_intro' τ Φ e
unseal EXPR.exists in
theorem PROVES.exists_elim {τ : TYPE.{i}} {Φ Q : EXPR.{i}} : TYPED (Γ :: Γs) Q TYPE.prop → PROVES (Γ :: Γs) (Ψ :: Ψs) (.exists nm τ Φ) → PROVES ((τ :: Γ) :: Γs) ((Φ :: intro_wrap' Ψ) :: Ψs) (_root_.weaken Q octx_wk) → PROVES (Γ :: Γs) (Ψ :: Ψs) Q := PROVES.exists_elim'
theorem simplify_eq {Γ0 : OCTX.{i}} {Γs : CTX.{i}} {P1 P2 : EXPR.{i}}
    (HP1 : TYPED (Γ0 :: Γs) P1 TYPE.prop) (HP2 : TYPED (Γ0 :: Γs) P2 TYPE.prop) :
    PROVES (Γ0 :: Γs) Ψ (.eq TYPE.prop P1 P2) → PROVES (Γ0 :: Γs) Ψ P1 →
    PROVES (Γ0 :: Γs) Ψ P2 := by
  intros
  have EQ : ∀ P, P = (binds (single_subst (List.map List.length (Γ0 :: Γs)) P) (.var' 0 0)) := by
    intro P
    simp [single_subst]
    cases Γ0 with
    | nil =>
      cases Γs with
      | nil => simp [binds, ssubst_var, subst_var]
      | cons z zs => simp [binds, ssubst_var, subst_var]
    | cons y ys =>
      cases Γs with
      | nil => simp [binds, ssubst_var, subst_var]
      | cons z zs => simp [binds, ssubst_var, subst_var]
  have Hvar : TYPED ((TYPE.prop :: Γ0) :: Γs) (.var' 0 0) TYPE.prop :=
    TYPED.var' 0 0 rfl rfl
  rw [EQ P2]
  apply PROVES.eq_elim Hvar HP1 HP2
  . assumption
  . rw [<-(EQ P1)]
    assumption

theorem simplify_prop {Γ : CTX.{i}} {P1 P2 : EXPR.{i}} :
    EQ Γ TYPE.prop P1 P2 → PROVES Γ Ψ P1 → PROVES Γ Ψ P2 := by
  intro Heq Hp

  obtain ⟨Γ0, Γs, rfl⟩ : ∃ Γ0 Γs, Γ = Γ0 :: Γs := by
    cases Γ with
    | nil => exact absurd (typing_stack_len Heq.typed) (by simp)
    | cons a b => exact ⟨a, b, rfl⟩
  exact simplify_eq Heq.typed Heq.typed' (PROVES.eq_def Heq (Hlen := PROVES.len Hp)) Hp

abbrev PP_CTX := ElabCtx
abbrev PP_PCTX := ElabCtx

structure GOAL.{i} (_pp_ctx : PP_CTX) (_pp_pctx : PP_PCTX)
  (ctx : CTX.{i}) (pctx : PCTX.{i}) (prop : EXPR.{i}) where
  goal : PROVES ctx pctx prop

macro "⊢ᵍ " P:term : term => `(GOAL [[]] [[]] [[]] [[]] $P)

theorem GOAL_consistency (H : ⊢ᵍ (⟪⊥⟫ : EXPR.{i})) :
    PROVES ([[]] : CTX.{i}) [[]] EXPR.false := H.goal

theorem swap_PP_CTX PΓ : GOAL PΓ PΨ Γ Ψ Φ → GOAL PΓ' PΨ Γ Ψ Φ := by
  intros H
  let ⟨H⟩ := H
  constructor
  assumption

theorem swap_PP_PCTX PΨ : GOAL PΓ PΨ Γ Ψ Φ → GOAL PΓ PΨ' Γ Ψ Φ := by
  intros H
  let ⟨H⟩ := H
  constructor
  assumption

theorem GOAL_drop {Ψ Ψ' : PCTX.{i}} {P : EXPR.{i}} (k m : Nat)
    (hΨ : Ψ = pctx_ins Ψ' k m P) (H : GOAL PΓ' PΨ' Γ Ψ' Φ) : GOAL PΓ PΨ Γ Ψ Φ := by
  subst hΨ
  let ⟨H⟩ := H
  exact ⟨H.assum_insert_at k m P⟩

theorem GOAL_forall_intro (n : Name) :
  GOAL ((n :: PΓ) :: PΓs) PΨ ((τ :: Γ) :: Γs) (intro_wrap Ψ) P
  → GOAL (PΓ :: PΓs) PΨ (Γ :: Γs) Ψ (.forall x τ P) :=
  by
    intros H
    let ⟨H⟩ := H
    constructor
    apply PROVES.forall_intro H

theorem GOAL_forall_intro_points' {A : Type (imax i 0)} {Φ : EXPR.{i}}
    (HΦ : TYPED ((TYPE.embed A :: Γ) :: Γs) Φ TYPE.prop)
    (Hlen : (Γ :: Γs).length = Ψ.length)
    (h : ∀ a : A, GOAL PΓ PΨ (Γ :: Γs) Ψ
      (binds (single_subst (List.map List.length (Γ :: Γs)) (EXPR.embed A a)) Φ)) :
    GOAL PΓ PΨ (Γ :: Γs) Ψ (.forall' (TYPE.embed A) Φ) :=
  ⟨PROVES.forall_intro_points A Φ HΦ Hlen (fun a => (h a).goal)⟩

unseal EXPR.forall in
theorem GOAL_forall_intro_points {A : Type (imax i 0)} {Φ : EXPR.{i}} (nm : Name)
    (HΦ : TYPED ((TYPE.embed A :: Γ) :: Γs) Φ TYPE.prop)
    (Hlen : (Γ :: Γs).length = Ψ.length)
    (h : ∀ a : A, GOAL PΓ PΨ (Γ :: Γs) Ψ
      (binds (single_subst (List.map List.length (Γ :: Γs)) (EXPR.embed A a)) Φ)) :
    GOAL PΓ PΨ (Γ :: Γs) Ψ (.forall nm (TYPE.embed A) Φ) :=
  ⟨PROVES.forall_intro_points A Φ HΦ Hlen (fun a => (h a).goal)⟩

theorem GOAL_impl_intro (n : Name) (HQ : TYPED Γ Q TYPE.prop) :
  GOAL PΓ ((n :: PΨ) :: PΨs) Γ ((Q :: Ψ) :: Ψs) P
  → GOAL PΓ (PΨ :: PΨs) Γ (Ψ :: Ψs) (.impl Q P) :=
  by
    intros H
    let ⟨H⟩ := H
    exact ⟨PROVES.impl_intro (Htyped := HQ) H⟩

theorem GOAL_and_intro : GOAL PΓ PΨ Γ Ψ P → GOAL PΓ PΨ Γ Ψ Q → GOAL PΓ PΨ Γ Ψ (.and P Q) :=
  by
    intros H
    let ⟨H⟩ := H
    intros H'
    let ⟨H'⟩ := H'
    constructor
    apply PROVES.and_intro H H'

theorem GOAL_and_elim_l : GOAL PΓ PΨ Γ Ψ (.and P Q) → GOAL PΓ PΨ Γ Ψ P :=
  by
    intros H
    let ⟨H⟩ := H
    constructor
    apply PROVES.and_elim_l H

theorem GOAL_and_elim_r : GOAL PΓ PΨ Γ Ψ (.and P Q) → GOAL PΓ PΨ Γ Ψ Q :=
  by
    intros H
    let ⟨H⟩ := H
    constructor
    apply PROVES.and_elim_r H

theorem GOAL_or_intro_l (HQ : TYPED Γ Q TYPE.prop) : GOAL PΓ PΨ Γ Ψ P → GOAL PΓ PΨ Γ Ψ (.or P Q) :=
  by
    intros H
    let ⟨H⟩ := H
    exact ⟨PROVES.or_intro_l (Htyped := HQ) H⟩

theorem GOAL_or_intro_r (HP : TYPED Γ P TYPE.prop) : GOAL PΓ PΨ Γ Ψ Q → GOAL PΓ PΨ Γ Ψ (.or P Q) :=
  by
    intros H
    let ⟨H⟩ := H
    exact ⟨PROVES.or_intro_r (Htyped := HP) H⟩

theorem GOAL_or_elim (n : Name) (m : Name) :
  GOAL PΓ ((n :: PΨ) :: PΨs) Γ ((P :: Ψ) :: Ψs) Φ
  → GOAL PΓ ((m :: PΨ) :: PΨs) Γ ((Q :: Ψ) :: Ψs) Φ
  → GOAL PΓ (PΨ :: PΨs) Γ (Ψ :: Ψs) (.or P Q)
  → GOAL PΓ (PΨ :: PΨs) Γ (Ψ :: Ψs) Φ :=
  by
    intros H
    let ⟨H⟩ := H
    intros H'
    let ⟨H'⟩ := H'
    intros H''
    let ⟨H''⟩ := H''
    constructor
    apply PROVES.or_elim H H' H''

theorem GOAL_sum_elim {A B : TYPE.{i}} {Φ : EXPR.{i}} (na ne nb ne2 : Name) (e : EXPR.{i})
    (HΦ : TYPED (Γ :: Γs) Φ TYPE.prop) (He : TYPED (Γ :: Γs) e (TYPE.sum A B)) :
    GOAL ((na :: PΓ) :: PΓs) ((ne :: PΨ) :: PΨs) ((A :: Γ) :: Γs)
        ((.eq (TYPE.sum A B) (weaken e octx_wk) (.inl B (.var' 0 0)) :: intro_wrap' Ψ) :: Ψs)
        (weaken Φ octx_wk)
    → GOAL ((nb :: PΓ) :: PΓs) ((ne2 :: PΨ) :: PΨs) ((B :: Γ) :: Γs)
        ((.eq (TYPE.sum A B) (weaken e octx_wk) (.inr A (.var' 0 0)) :: intro_wrap' Ψ) :: Ψs)
        (weaken Φ octx_wk)
    → GOAL (PΓ :: PΓs) (PΨ :: PΨs) (Γ :: Γs) (Ψ :: Ψs) Φ :=
  by
    intros H1 H2
    let ⟨H1⟩ := H1
    let ⟨H2⟩ := H2
    exact ⟨PROVES.sum_elim e HΦ He H1 H2⟩

theorem GOAL_loeb (n : Name) : GOAL PΓ ((n :: PΨ) :: PΨs) Γ ((.lift (.delay (weaken Φ (REN.global_shift 1 REN.id))) :: Ψs) :: Φs) Φ → GOAL PΓ (PΨ :: PΨs) Γ (Ψs :: Φs) Φ :=
  by
    intros H
    let ⟨H⟩ := H
    constructor
    apply PROVES.loeb_ind H

theorem GOAL_lift_intro (HΓ : 0 < Γ.length) : GOAL ([] :: PΓ) ([] :: PΨ) ([] :: Γ) ([] :: Ψ) Φ → GOAL PΓ PΨ Γ Ψ (.lift (.delay Φ)) :=
  by
    intros H
    let ⟨H⟩ := H
    exact ⟨PROVES.lift_intro (Hpos := HΓ) H⟩

theorem GOAL_later_mono (HΓ : 0 < Γ.length) (nm : Name) :
    GOAL PΓ PΨ Γ Ψ (.lift (.delay P)) →
    GOAL ([] :: PΓ) ((nm :: []) :: PΨ) ([] :: Γ) ([P] :: Ψ) Q →
    GOAL PΓ PΨ Γ Ψ (.lift (.delay Q)) :=
  by
    intros H1 H2
    let ⟨H1⟩ := H1
    let ⟨H2⟩ := H2
    exact ⟨PROVES.later_mono (Hpos := HΓ) H1 H2⟩

theorem GOAL_later_and :
    GOAL PΓ PΨ Γ Ψ (.lift (.delay P)) →
    GOAL PΓ PΨ Γ Ψ (.lift (.delay Q)) →
    GOAL PΓ PΨ Γ Ψ (.lift (.delay (.and P Q))) :=
  by
    intros H1 H2
    let ⟨H1⟩ := H1
    let ⟨H2⟩ := H2
    exact ⟨PROVES.later_and H1 H2⟩

theorem GOAL_later_or :
    GOAL PΓ PΨ Γ Ψ (.lift (.delay (.or P Q))) →
    GOAL PΓ PΨ Γ Ψ (.or (.lift (.delay P)) (.lift (.delay Q))) :=
  by
    intros H
    let ⟨H⟩ := H
    exact ⟨PROVES.later_or H⟩

theorem GOAL_false_elim (HP : TYPED Γ P TYPE.prop) : GOAL PΓ PΨ Γ Ψ .false → GOAL PΓ PΨ Γ Ψ P :=
  by
    intros H
    let ⟨H⟩ := H
    exact ⟨PROVES.false_elim P (Htyped := HP) H⟩

theorem GOAL_true_intro (HΓ : 0 < Γ.length) (Hlen : Γ.length = Ψ.length) : GOAL PΓ PΨ Γ Ψ .true :=
  by
    exact ⟨PROVES.true_intro (Hpos := HΓ) (Hlen := Hlen)⟩

theorem GOAL_eq_refl {τ : TYPE.{i}} {e : EXPR.{i}} (H : TYPED Γ e τ) (Hlen : Γ.length = Ψ.length) :
    GOAL PΓ PΨ Γ Ψ (.eq τ e e) :=
  by
    exact ⟨PROVES.eq_def (EQ.rfl H) (Hlen := Hlen)⟩

theorem GOAL_impl_elim :
    GOAL PΓ PΨ Γ Ψ (.impl P Q) → GOAL PΓ PΨ Γ Ψ P → GOAL PΓ PΨ Γ Ψ Q := by
  intro H1 H2
  let ⟨H1⟩ := H1
  let ⟨H2⟩ := H2
  exact ⟨PROVES.impl_elim H1 H2⟩

theorem GOAL_inl_inj {A B : TYPE.{i}} {a a' : EXPR.{i}} :
    GOAL PΓ PΨ Γ Ψ (.eq (TYPE.sum A B) (.inl B a) (.inl B a')) →
    GOAL PΓ PΨ Γ Ψ (.eq A a a') := by
  intro H; let ⟨H⟩ := H; exact ⟨PROVES.inl_inj H⟩

theorem GOAL_inr_inj {A B : TYPE.{i}} {b b' : EXPR.{i}} :
    GOAL PΓ PΨ Γ Ψ (.eq (TYPE.sum A B) (.inr A b) (.inr A b')) →
    GOAL PΓ PΨ Γ Ψ (.eq B b b') := by
  intro H; let ⟨H⟩ := H; exact ⟨PROVES.inr_inj H⟩

theorem GOAL_inl_inr_disj {A B : TYPE.{i}} {a b : EXPR.{i}} :
    GOAL PΓ PΨ Γ Ψ (.eq (TYPE.sum A B) (.inl B a) (.inr A b)) →
    GOAL PΓ PΨ Γ Ψ EXPR.false := by
  intro H; let ⟨H⟩ := H; exact ⟨PROVES.inl_inr_disj H⟩

theorem GOAL_delay_eq {A : TYPE.{i}} {e1 e2 : EXPR.{i}} :
    GOAL PΓ PΨ Γ Ψ (.lift (.delay (.eq A e1 e2))) →
    GOAL PΓ PΨ Γ Ψ (.eq (TYPE.later A) (.delay e1) (.delay e2)) := by
  intro H
  let ⟨H⟩ := H
  exact ⟨PROVES.delay_eq H⟩

theorem GOAL_pure_intro (Htyped : TYPED Γ (.pure (.embed Prop P)) TYPE.prop)
    (Hlen : Γ.length = Ψ.length) : P → GOAL PΓ PΨ Γ Ψ (.pure (.embed Prop P)) :=
  by
    intros H
    exact ⟨PROVES.pure_intro H (Htyped := Htyped) (Hlen := Hlen)⟩

theorem projectHypLater (Hi : i < Ψ.length) (Hj : j < (Ψ.get (Fin.mk i Hi)).length)
    (Htyped : TYPED Γ (weaken ((Ψ[i]'Hi)[j]'Hj) (REN.global_shift i REN.id)) TYPE.prop)
    (Hlen : Γ.length = Ψ.length) :
  GOAL PΓ PΨ Γ Ψ (weaken ((Ψ[i]'Hi)[j]'Hj) (REN.global_shift i REN.id)) := by
  constructor
  apply PROVES.asm i j (Htyped := Htyped) (Hlen := Hlen)
  . rw [List.getElem?_eq_getElem]
    assumption
  . rw [List.getElem?_eq_getElem]

theorem GOAL_simplify_prop : EQ Γ TYPE.prop Φ Φ' → GOAL PΓ PΨ Γ Ψ Φ → GOAL PΓ PΨ Γ Ψ Φ' :=
  by
    intros HEQ H
    let ⟨H⟩ := H
    constructor
    apply simplify_prop HEQ H

theorem GOAL_subst (t : GOAL PΓ PΨ Γ Ψ Φ) (p : Φ' = Φ) :
  GOAL PΓ PΨ Γ Ψ Φ' :=
  by
    rw [p]
    apply t

theorem GOAL_assert (n : Name) : GOAL PΓ (PΨ :: PΨs) Γ (Ψ :: Ψs) P →
  GOAL PΓ ((n :: PΨ) :: PΨs) Γ ((P :: Ψ) :: Ψs) Q →
  GOAL PΓ (PΨ :: PΨs) Γ (Ψ :: Ψs) Q :=
  by
    intros H1 H2
    let ⟨H1⟩ := H1
    let ⟨H2⟩ := H2
    have H2 := PROVES.impl_intro (Htyped := PROVES.typed H1) H2
    constructor
    apply PROVES.impl_elim
    apply  H2
    apply H1

theorem GOAL_exists_intro {Γ0 : OCTX.{i}} {Γs : CTX.{i}} {τ : TYPE.{i}} {P t : EXPR.{i}} :
  TYPED ((τ :: Γ0) :: Γs) P TYPE.prop → TYPED (Γ0 :: Γs) t τ →
  GOAL PΓ PΨ (Γ0 :: Γs) Ψ (binds (single_subst (List.map List.length (Γ0 :: Γs)) t) P) →
  GOAL PΓ PΨ (Γ0 :: Γs) Ψ (.exists nm τ P) :=
  by
    intros HP Ht H
    let ⟨H⟩ := H
    exact ⟨PROVES.exists_intro τ P t HP Ht H⟩

theorem GOAL_exists_elim {Γ0 : OCTX.{i}} {Γs : CTX.{i}} {τ : TYPE.{i}} {Φ Q : EXPR.{i}}
    (vn hn : Name) :
  TYPED (Γ0 :: Γs) Q TYPE.prop →
  GOAL (PΓ :: PΓs) (PΨ :: PΨs) (Γ0 :: Γs) (Ψ :: Ψs) (.exists nm τ Φ) →
  GOAL ((vn :: PΓ) :: PΓs) ((hn :: PΨ) :: PΨs) ((τ :: Γ0) :: Γs)
    ((Φ :: intro_wrap' Ψ) :: Ψs) (weaken Q octx_wk) →
  GOAL (PΓ :: PΓs) (PΨ :: PΨs) (Γ0 :: Γs) (Ψ :: Ψs) Q :=
  by
    intros HQ H1 H2
    let ⟨H1⟩ := H1
    let ⟨H2⟩ := H2
    exact ⟨PROVES.exists_elim HQ H1 H2⟩

theorem GOAL_forall_elim {Γ0 : OCTX.{i}} {Γs : CTX.{i}} {τ : TYPE.{i}} {P t : EXPR.{i}} :
  TYPED ((τ :: Γ0) :: Γs) P TYPE.prop →
  GOAL PΓ PΨ (Γ0 :: Γs) Ψ (.forall nm τ P) → TYPED (Γ0 :: Γs) t τ →
  GOAL PΓ PΨ (Γ0 :: Γs) Ψ (binds (single_subst (List.map List.length (Γ0 :: Γs)) t) P) :=
  by
    intros HP H G
    let ⟨H⟩ := H
    constructor
    apply PROVES.forall_elim _ _ _ HP H G

theorem GOAL_eq_elim {Γ0 : OCTX.{i}} {Γs : CTX.{i}} {B : TYPE.{i}} {e1 e2 Φ : EXPR.{i}} :
  TYPED ((B :: Γ0) :: Γs) Φ TYPE.prop →
  TYPED (Γ0 :: Γs) e1 B → TYPED (Γ0 :: Γs) e2 B →
  GOAL PΓ PΨ (Γ0 :: Γs) Ψ (.eq B e1 e2) →
  GOAL PΓ PΨ (Γ0 :: Γs) Ψ (binds (single_subst (List.map List.length (Γ0 :: Γs)) e1) Φ) →
  GOAL PΓ PΨ (Γ0 :: Γs) Ψ (binds (single_subst (List.map List.length (Γ0 :: Γs)) e2) Φ) :=
  by
    intros HΦ He1 He2 Heq H1
    let ⟨Heq⟩ := Heq
    let ⟨H1⟩ := H1
    constructor
    exact PROVES.eq_elim HΦ He1 He2 Heq H1

theorem GOAL_eq_symm {Γ0 : OCTX.{i}} {Γs : CTX.{i}} {B : TYPE.{i}} {e1 e2 : EXPR.{i}} :
    GOAL PΓ PΨ (Γ0 :: Γs) Ψ (.eq B e1 e2) →
    GOAL PΓ PΨ (Γ0 :: Γs) Ψ (.eq B e2 e1) := by
  intro equation
  let ⟨raw⟩ := equation
  have typed := TYPED.eq_inversion (PROVES.typed raw)
  have He1 := typed.2.1
  have He2 := typed.2.2
  have Hlen := PROVES.len raw
  let motive : EXPR.{i} := .eq B (.var' 0 0) (weaken e1 octx_wk)
  have typedMotive : TYPED ((B :: Γ0) :: Γs) motive TYPE.prop := by
    dsimp [motive]
    apply TYPED.eq
    · exact TYPED.var' 0 0 rfl rfl
    · exact weaken_typing He1 (TYPED_REN.local_weaken B (TYPED_REN.id (by simp)))
  have substVar (e : EXPR.{i}) :
      binds (single_subst (List.map List.length (Γ0 :: Γs)) e) (.var' 0 0) = e := by
    simp only [single_subst, binds]
    cases Γ0 <;> cases Γs <;> simp
  have substWeaken (e : EXPR.{i}) (He : TYPED (Γ0 :: Γs) e B) :
      binds (single_subst (List.map List.length (Γ0 :: Γs)) e)
        (weaken e1 octx_wk) = e1 := by
    let renProof : TYPED_REN octx_wk ((B :: Γ0) :: Γs) (Γ0 :: Γs) :=
      TYPED_REN.local_weaken B (TYPED_REN.id (by simp))
    let substProof := TSSUBST.single_subst He
    rw [binds_weaken He1 renProof substProof]
    rw [show (single_subst (List.map List.length (Γ0 :: Γs)) e).scr octx_wk =
        SSUBST.id (List.map List.length (Γ0 :: Γs)) by
      simp only [single_subst, octx_wk, SSUBST.scr, drop0_cons]]
    exact binds_ctx_id He1
  have base : GOAL PΓ PΨ (Γ0 :: Γs) Ψ
      (binds (single_subst (List.map List.length (Γ0 :: Γs)) e1) motive) := by
    simpa only [motive, eq_subst, substVar e1, substWeaken e1 He1] using
      (GOAL_eq_refl (PΓ := PΓ) (PΨ := PΨ) (Ψ := Ψ) He1 Hlen)
  have result := GOAL_eq_elim typedMotive He1 He2 equation base
  simpa only [motive, eq_subst, substVar e2, substWeaken e2 He2] using result

theorem GOAL_import {Γ0 : OCTX.{i}} {Γs : CTX.{i}} {Ψ : PCTX.{i}} {Φ : EXPR.{i}}
    (t : GOAL PΓ' PΨ' ([[]] : CTX.{i}) [[]] Φ)
    (Hlen : (Γ0 :: Γs).length = Ψ.length) :
    GOAL PΓ PΨ (Γ0 :: Γs) Ψ (_root_.weaken Φ (local_weaken_list Γ0.length REN.id)) := by
  let ⟨H⟩ := t
  exact ⟨PROVES.import_ctx H Hlen⟩

end prf
