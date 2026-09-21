module

public import SynthDom.Syntax.Ty.Core
public import SynthDom.Interp.Base

@[expose] public section

section expr

open Lean
open CategoryTheory
open MonoidalCategory

inductive DIR : Type where
| L : DIR
| R : DIR

inductive EXPR.{i} : Type (i + 1) where
| embed : (A : Type (imax i 0)) → A → EXPR
| embed_apply (A B : Type (imax i 0)) : EXPR → EXPR → EXPR
| pure : EXPR → EXPR
| var' : Nat → Nat → EXPR
| app : TYPE.{i} → EXPR → EXPR → EXPR
| lam' : TYPE.{i} → EXPR → EXPR
| delay : EXPR → EXPR
| adv : Nat → EXPR → EXPR
| fix' : TYPE.{i} → EXPR → EXPR
| pair : EXPR → EXPR → EXPR
| proj : TYPE.{i} → EXPR → DIR → EXPR
| inl : TYPE.{i} → EXPR → EXPR
| inr : TYPE.{i} → EXPR → EXPR
| case : TYPE.{i} → TYPE.{i} → EXPR → EXPR → EXPR → EXPR
| or : EXPR → EXPR → EXPR
| and : EXPR → EXPR → EXPR
| impl : EXPR → EXPR → EXPR
| forall' : TYPE.{i} → EXPR → EXPR
| exists' : TYPE.{i} → EXPR → EXPR
| lift : EXPR → EXPR
| true : EXPR
| false : EXPR
| eq : TYPE.{i} → EXPR → EXPR → EXPR
| ax (t : TYPE.{i}) : (𝟙_ _ ⟶ ⟦t⟧ₜ) → EXPR

inductive REN where
| id : REN
| comp : REN → REN → REN
| local_weaken : REN → REN
| cons : REN → REN
| global_lift : REN → REN
| global_shift (n : Nat) : REN → REN

inductive TYPED : CTX.{i} → EXPR.{i} → TYPE.{i} → Prop where
| embed : ∀ {Γ A a},
  0 < Γ.length →
  TYPED Γ (EXPR.embed A a) (TYPE.embed A)
| embed_apply : ∀ {Γ A B f x},
  TYPED Γ f (TYPE.embed (A → B)) →
  TYPED Γ x (TYPE.embed A) →
  TYPED Γ (.embed_apply A B f x) (TYPE.embed B)
| pure : ∀ {Γ e},
  TYPED Γ e (TYPE.embed Prop) →
  TYPED Γ (EXPR.pure e) TYPE.prop
| var' : ∀ {Γ : CTX.{i}} {Δ : OCTX.{i}} {τ : TYPE.{i}} (p q : Nat),
  (Heq1 : Γ[p]? = some Δ) →
  (Heq2 : Δ[q]? = τ) →
  TYPED Γ (EXPR.var' p q) τ
| app : ∀ {Γ e1 e2 A B},
  TYPED Γ e1 (TYPE.arr A B) →
  TYPED Γ e2 A →
  TYPED Γ (EXPR.app A e1 e2) B
| lam' : ∀ {Γ Δ A B e},
  TYPED ((A :: Δ) :: Γ) e B →
  TYPED (Δ :: Γ) (EXPR.lam' A e) (TYPE.arr A B)
| delay : ∀ {Γ e A},
  0 < Γ.length →
  TYPED ([] :: Γ) e A →
  TYPED Γ (EXPR.delay e) (TYPE.later A)
| adv : ∀ {n Γ e A},
  0 < n →
  TYPED (Γ.drop n) e (TYPE.later A) →
  TYPED Γ (EXPR.adv n e) A
| fix' : ∀ {Γ Δ e A},
  TYPED ((TYPE.later A :: Δ) :: Γ) e A →
  TYPED (Δ :: Γ) (EXPR.fix' (TYPE.later A) e) A
| pair : ∀ {Γ e1 e2 A B},
  TYPED Γ e1 A →
  TYPED Γ e2 B →
  TYPED Γ (EXPR.pair e1 e2) (TYPE.prod A B)
| projL : ∀ {Γ e A B},
  TYPED Γ e (TYPE.prod A B) →
  TYPED Γ (EXPR.proj B e .L) A
| projR : ∀ {Γ e A B},
  TYPED Γ e (TYPE.prod A B) →
  TYPED Γ (EXPR.proj A e .R) B
| inl : ∀ {Γ e A B},
  TYPED Γ e A →
  TYPED Γ (EXPR.inl B e) (TYPE.sum A B)
| inr : ∀ {Γ e A B},
  TYPED Γ e B →
  TYPED Γ (EXPR.inr A e) (TYPE.sum A B)
| case : ∀ {Γ e f g A B C},
  TYPED Γ e (TYPE.sum A B) →
  TYPED Γ f (TYPE.arr A C) →
  TYPED Γ g (TYPE.arr B C) →
  TYPED Γ (EXPR.case A B e f g) C
| or : ∀ {Γ e1 e2},
  TYPED Γ e1 TYPE.prop →
  TYPED Γ e2 TYPE.prop →
  TYPED Γ (EXPR.or e1 e2) TYPE.prop
| and : ∀ {Γ e1 e2},
  TYPED Γ e1 TYPE.prop →
  TYPED Γ e2 TYPE.prop →
  TYPED Γ (EXPR.and e1 e2) TYPE.prop
| impl : ∀ {Γ e1 e2},
  TYPED Γ e1 TYPE.prop →
  TYPED Γ e2 TYPE.prop →
  TYPED Γ (EXPR.impl e1 e2) TYPE.prop
| forall' : ∀ {Γ Δ A e},
  TYPED ((A :: Δ) :: Γ) e TYPE.prop →
  TYPED (Δ :: Γ) (EXPR.forall' A e) TYPE.prop
| exists' : ∀ {Γ Δ A e},
  TYPED ((A :: Δ) :: Γ) e TYPE.prop →
  TYPED (Δ :: Γ) (EXPR.exists' A e) TYPE.prop
| lift : ∀ {Γ e},
  TYPED Γ e (TYPE.later TYPE.prop) →
  TYPED Γ (EXPR.lift e) TYPE.prop
| true : ∀ {Γ}, 0 < Γ.length → TYPED Γ EXPR.true TYPE.prop
| false : ∀ {Γ}, 0 < Γ.length → TYPED Γ EXPR.false TYPE.prop
| eq : ∀ {Γ e1 e2 τ}, TYPED Γ e1 τ → TYPED Γ e2 τ → TYPED Γ (EXPR.eq τ e1 e2) TYPE.prop
| ax (t : TYPE.{i}) (f : 𝟙_ _ ⟶ ⟦t⟧ₜ) : ∀ {Γ}, 0 < Γ.length → TYPED Γ (EXPR.ax t f) t

theorem TYPED.embed_inversion (H : TYPED Γ (.embed A e) τ) :
  τ = (TYPE.embed A) := by
  cases H with
  | _ => rfl

theorem TYPED.embed_apply_inversion (H : TYPED Γ (.embed_apply A B f a) τ) :
  τ = (TYPE.embed B) ∧ TYPED Γ f (TYPE.embed (A → B)) ∧ TYPED Γ a (TYPE.embed A) := by
  cases H with
  | @embed_apply _ A B =>
    constructor
    . rfl
    . constructor <;> assumption

theorem TYPED.pure_inversion (H : TYPED Γ (.pure e) τ) :
  τ = TYPE.prop ∧ TYPED Γ e (TYPE.embed Prop) := by
  cases H with
  | _ =>
    constructor
    . rfl
    . assumption

theorem TYPED.var'_inversion (H : TYPED Γ (.var' n m) τ) :
  ∃ Δ, Γ[n]? = some Δ ∧ Δ[m]? = τ := by
  cases H with
  | _ => exists ?_; constructor <;> assumption

theorem TYPED.app_inversion (H : TYPED Γ (.app σ f e) τ) :
  TYPED Γ f (TYPE.arr σ τ) ∧ TYPED Γ e σ := by
  cases H with
  | _ => exists ?_; assumption

theorem TYPED.lam'_inversion (H : TYPED (Γ :: Γs) (.lam' τ e) σ) :
  ∃ τ', σ = TYPE.arr τ τ' ∧ TYPED ((τ :: Γ) :: Γs) e τ' := by
  cases H with
  | _ =>
    exists ?_; constructor
    . rfl
    . assumption

theorem TYPED.delay_inversion (H : TYPED Γ (.delay e) τ) :
  ∃ τ', τ = TYPE.later τ' ∧ TYPED ([] :: Γ) e τ' := by
  cases H with
  | _ =>
    exists ?_; constructor
    . rfl
    . assumption

theorem TYPED.adv_inversion (H : TYPED Γ (.adv n e) τ) :
  0 < n ∧ TYPED (Γ.drop n) e (TYPE.later τ) := by
  cases H with
  | _ =>
    constructor
    . assumption
    . assumption

theorem TYPED.fix'_inversion (H : TYPED (Γ :: Γs) (.fix' τ e) σ) :
  τ = TYPE.later σ ∧ TYPED ((TYPE.later σ :: Γ) :: Γs) e σ := by
  cases H with
  | _ =>
    constructor
    . rfl
    . assumption

theorem TYPED.pair_inversion (H : TYPED Γ (.pair e1 e2) τ) :
  ∃ τ1 τ2, τ = TYPE.prod τ1 τ2 ∧ TYPED Γ e1 τ1 ∧ TYPED Γ e2 τ2 := by
  cases H with
  | @pair _ _ _ A B =>
    exists A, B

theorem TYPED.projL_inversion (H : TYPED Γ (.proj σ e .L) τ) :
  TYPED Γ e (TYPE.prod τ σ) := by
  cases H with
  | @projL _ _ _ σ => assumption

theorem TYPED.projR_inversion (H : TYPED Γ (.proj σ e .R) τ) :
  TYPED Γ e (TYPE.prod σ τ) := by
  cases H with
  | @projR _ _ σ _ => assumption

theorem TYPED.inl_inversion (H : TYPED Γ (.inl B e) τ) :
  ∃ A, τ = TYPE.sum A B ∧ TYPED Γ e A := by
  cases H with
  | @inl _ _ A _ => exists A

theorem TYPED.inr_inversion (H : TYPED Γ (.inr A e) τ) :
  ∃ B, τ = TYPE.sum A B ∧ TYPED Γ e B := by
  cases H with
  | @inr _ _ _ B => exists B

theorem TYPED.case_inversion (H : TYPED Γ (.case A B e f g) τ) :
  TYPED Γ e (TYPE.sum A B) ∧ TYPED Γ f (TYPE.arr A τ) ∧ TYPED Γ g (TYPE.arr B τ) := by
  cases H with
  | case => exact ⟨by assumption, by assumption, by assumption⟩

theorem TYPED.or_inversion (H : TYPED Γ (.or e1 e2) τ) :
  τ = TYPE.prop ∧ TYPED Γ e1 TYPE.prop ∧ TYPED Γ e2 TYPE.prop := by
  cases H with
  | _ =>
    constructor
    . rfl
    . constructor <;> assumption

theorem TYPED.and_inversion (H : TYPED Γ (.and e1 e2) τ) :
  τ = TYPE.prop ∧ TYPED Γ e1 TYPE.prop ∧ TYPED Γ e2 TYPE.prop := by
  cases H with
  | _ =>
    constructor
    . rfl
    . constructor <;> assumption

theorem TYPED.impl_inversion (H : TYPED Γ (.impl e1 e2) τ) :
  τ = TYPE.prop ∧ TYPED Γ e1 TYPE.prop ∧ TYPED Γ e2 TYPE.prop := by
  cases H with
  | _ =>
    constructor
    . rfl
    . constructor <;> assumption

theorem TYPED.forall'_inversion (H : TYPED (Γ :: Γs) (.forall' τ e) σ) :
  σ = TYPE.prop ∧ TYPED ((τ :: Γ) :: Γs) e TYPE.prop := by
  cases H with
  | _ =>
    constructor
    . rfl
    . assumption

theorem TYPED.exists'_inversion (H : TYPED (Γ :: Γs) (.exists' τ e) σ) :
  σ = TYPE.prop ∧ TYPED ((τ :: Γ) :: Γs) e TYPE.prop := by
  cases H with
  | _ =>
    constructor
    . rfl
    . assumption

theorem TYPED.lift_inversion (H : TYPED Γ (.lift e) τ) :
  τ = TYPE.prop ∧ TYPED Γ e (TYPE.later TYPE.prop) := by
  cases H with
  | _ =>
    constructor
    . rfl
    . assumption

theorem TYPED.true_inversion (H : TYPED Γ .true τ) :
  τ = TYPE.prop := by
  cases H with
  | _ => constructor

theorem TYPED.false_inversion (H : TYPED Γ .false τ) :
  τ = TYPE.prop := by
  cases H with
  | _ => constructor

theorem TYPED.eq_inversion (H : TYPED Γ (.eq σ e1 e2) τ) :
  τ = TYPE.prop ∧ TYPED Γ e1 σ ∧ TYPED Γ e2 σ := by
  cases H with
  | _ =>
    constructor
    . rfl
    . constructor <;> assumption

theorem TYPED.type_uniq : TYPED Γ e τ → TYPED Γ e τ' → τ = τ' := by
  induction e generalizing τ τ' Γ with
  | embed A a =>
    intros H1 H2
    rw [TYPED.embed_inversion H1]
    rw [TYPED.embed_inversion H2]
  | embed_apply B f x IH1 IH2 =>
    intros H1 H2
    have H1 := TYPED.embed_apply_inversion H1
    have H2 := TYPED.embed_apply_inversion H2
    rcases H1 with ⟨Heq1, Hf1, Hx1⟩
    rcases H2 with ⟨Heq2, Hf2, Hx2⟩
    rw [Heq1, Heq2]
  | pure e IH =>
    intros H1 H2
    rw [(TYPED.pure_inversion H1).1]
    rw [(TYPED.pure_inversion H2).1]
  | var' n m =>
    intros H1 H2
    have H1 := TYPED.var'_inversion H1
    have H2 := TYPED.var'_inversion H2
    rcases H1 with ⟨Δ1, Heq1_1, Heq1_2⟩
    rcases H2 with ⟨Δ2, Heq2_1, Heq2_2⟩
    rw [Heq1_1] at Heq2_1
    injection Heq2_1 with HeqΔ
    cases HeqΔ
    rw [Heq1_2] at Heq2_2
    injection Heq2_2 with Heqτ
  | app _ e1 e2 IH1 IH2 =>
    intros H1 H2
    have H1 := TYPED.app_inversion H1
    have H2 := TYPED.app_inversion H2
    rcases H1 with ⟨Hf1, He1⟩
    rcases H2 with ⟨Hf2, He2⟩
    specialize (IH1 Hf1 Hf2)
    specialize (IH2 He1 He2)
    cases IH2
    injection IH1
  | lam' σ e IH =>
    intros H1 H2
    cases Γ with
    | nil =>
      cases H1
    | cons Γ Γs =>
      have H1 := TYPED.lam'_inversion H1
      have H2 := TYPED.lam'_inversion H2
      rcases H1 with ⟨τ1, Heq1, He1⟩
      rcases H2 with ⟨τ2, Heq2, He2⟩
      rw [Heq1, Heq2]
      congr
      specialize (IH He1 He2)
      cases IH
      simp
  | delay e IH =>
    intros H1 H2
    have H1 := TYPED.delay_inversion H1
    have H2 := TYPED.delay_inversion H2
    rcases H1 with ⟨τ1, Heq1, He1⟩
    rcases H2 with ⟨τ2, Heq2, He2⟩
    rw [Heq1, Heq2]
    congr
    specialize (IH He1 He2)
    cases IH
    simp
  | adv n e IH =>
    intros H1 H2
    have ⟨_, H1⟩ := TYPED.adv_inversion H1
    have ⟨_, H2⟩ := TYPED.adv_inversion H2
    specialize (IH H1 H2)
    cases IH
    simp
  | fix' σ e IH =>
    intros H1 H2
    cases Γ with
    | nil =>
      cases H1
    | cons Γ Γs =>
      have H1 := TYPED.fix'_inversion H1
      have H2 := TYPED.fix'_inversion H2
      rcases H1 with ⟨Heq1, He1⟩
      rcases H2 with ⟨Heq2, He2⟩
      rw [Heq1] at Heq2
      injection Heq2 with Heqσ
  | pair e1 e2 IH1 IH2 =>
    intros H1 H2
    have H1 := TYPED.pair_inversion H1
    have H2 := TYPED.pair_inversion H2
    rcases H1 with ⟨τ1_1, τ1_2, Heq1, He1_1, He1_2⟩
    rcases H2 with ⟨τ2_1, τ2_2, Heq2, He2_1, He2_2⟩
    rw [Heq1, Heq2]
    specialize (IH1 He1_1 He2_1)
    specialize (IH2 He1_2 He2_2)
    cases IH1
    cases IH2
    simp
  | proj σ e d IH =>
    intros H1 H2
    cases d with
    | L =>
      have H1 := TYPED.projL_inversion H1
      have H2 := TYPED.projL_inversion H2
      specialize (IH H1 H2)
      cases IH
      simp
    | R =>
      have H1 := TYPED.projR_inversion H1
      have H2 := TYPED.projR_inversion H2
      specialize (IH H1 H2)
      cases IH
      simp
  | inl B e IH =>
    intros H1 H2
    rcases TYPED.inl_inversion H1 with ⟨A1, Heq1, He1⟩
    rcases TYPED.inl_inversion H2 with ⟨A2, Heq2, He2⟩
    rw [Heq1, Heq2]
    specialize (IH He1 He2); cases IH; simp
  | inr A e IH =>
    intros H1 H2
    rcases TYPED.inr_inversion H1 with ⟨B1, Heq1, He1⟩
    rcases TYPED.inr_inversion H2 with ⟨B2, Heq2, He2⟩
    rw [Heq1, Heq2]
    specialize (IH He1 He2); cases IH; simp
  | case A B e f g IHe IHf IHg =>
    intros H1 H2
    obtain ⟨He1, Hf1, Hg1⟩ := TYPED.case_inversion H1
    obtain ⟨He2, Hf2, Hg2⟩ := TYPED.case_inversion H2
    have h := IHf Hf1 Hf2; injection h
  | or e1 e2 IH1 IH2 =>
    intros H1 H2
    have H1 := TYPED.or_inversion H1
    have H2 := TYPED.or_inversion H2
    rcases H1 with ⟨Heq1, He1_1, He1_2⟩
    rcases H2 with ⟨Heq2, He2_1, He2_2⟩
    rw [Heq1, Heq2]
  | and e1 e2 IH1 IH2 =>
    intros H1 H2
    have H1 := TYPED.and_inversion H1
    have H2 := TYPED.and_inversion H2
    rcases H1 with ⟨Heq1, He1_1, He1_2⟩
    rcases H2 with ⟨Heq2, He2_1, He2_2⟩
    rw [Heq1, Heq2]
  | impl e1 e2 IH1 IH2 =>
    intros H1 H2
    have H1 := TYPED.impl_inversion H1
    have H2 := TYPED.impl_inversion H2
    rcases H1 with ⟨Heq1, He1_1, He1_2⟩
    rcases H2 with ⟨Heq2, He2_1, He2_2⟩
    rw [Heq1, Heq2]
  | forall' σ e IH =>
    intros H1 H2
    cases Γ with
    | nil =>
      cases H1
    | cons Γ Γs =>
      have H1 := TYPED.forall'_inversion H1
      have H2 := TYPED.forall'_inversion H2
      rcases H1 with ⟨Heq1, He1⟩
      rcases H2 with ⟨Heq2, He2⟩
      rw [Heq1, Heq2]
  | exists' σ e IH =>
    intros H1 H2
    cases Γ with
    | nil =>
      cases H1
    | cons Γ Γs =>
      have H1 := TYPED.exists'_inversion H1
      have H2 := TYPED.exists'_inversion H2
      rcases H1 with ⟨Heq1, He1⟩
      rcases H2 with ⟨Heq2, He2⟩
      rw [Heq1, Heq2]
  | lift e IH =>
    intros H1 H2
    have H1 := TYPED.lift_inversion H1
    have H2 := TYPED.lift_inversion H2
    rcases H1 with ⟨Heq1, He1⟩
    rcases H2 with ⟨Heq2, He2⟩
    rw [Heq1, Heq2]
  | true =>
    intros H1 H2
    rw [TYPED.true_inversion H1]
    rw [TYPED.true_inversion H2]
  | false =>
    intros H1 H2
    rw [TYPED.false_inversion H1]
    rw [TYPED.false_inversion H2]
  | eq e1 e2 IH1 IH2 =>
    intros H1 H2
    have H1 := TYPED.eq_inversion H1
    have H2 := TYPED.eq_inversion H2
    rcases H1 with ⟨Heq1, He1_1, He1_2⟩
    rcases H2 with ⟨Heq2, He2_1, He2_2⟩
    rw [Heq1, Heq2]
  | ax e f =>
    intros H1 H2
    cases H1 with
    | ax H1 =>
      cases H2 with
      | ax H2 =>
        rfl

theorem TYPED.typed_uniq' (H1 : TYPED Γ e τ) (H2 : TYPED Γ e τ') : HEq H1 H2 := by
  induction e generalizing τ τ' Γ with
  | embed A a =>
    cases H1 with
    | _ => cases H2; rfl
  | embed_apply A B f x IH1 IH2 =>
    cases H1 with
    | embed_apply a1 a2 =>
      cases H2 with
      | embed_apply b1 b2 =>
        have HEQ1 := TYPED.type_uniq a1 b1
        have HEQ2 := TYPED.type_uniq a2 b2
        cases HEQ2
        cases HEQ1
        simp
  | pure e IH =>
    cases H1 with
    | pure a =>
      cases H2 with
      | pure b =>
        have HEQ := TYPED.type_uniq a b
        cases HEQ
        simp
  | var' n m =>
    cases H1 with
    | var' n' m' G1 G2 =>
      cases H2 with
      | var' n'' m'' G3 G4 =>
        have J1 := G3
        rw [G1] at J1
        injection J1 with J1'
        cases J1'
        have J2 := G4
        rw [G2] at J2
        injection J2 with J2'
        cases J2'
        rfl
  | app σ e1 e2 IH1 IH2 =>
    cases H1 with
    | app f1 e1' =>
      cases H2 with
      | app f2 e2' =>
        have HEQ1 := TYPED.type_uniq f1 f2
        have HEQ2 := TYPED.type_uniq e1' e2'
        cases HEQ2
        cases HEQ1
        simp
  | lam' σ e IH =>
    cases Γ with
    | nil =>
      cases H1
    | cons Γ Γs =>
      cases H1 with
      | lam' e1' =>
        cases H2 with
        | lam' e2' =>
          have HEQ := TYPED.type_uniq e1' e2'
          cases HEQ
          simp
  | delay e IH =>
    cases H1 with
    | delay _ e1' =>
      cases H2 with
      | delay _ e2' =>
        have HEQ := TYPED.type_uniq e1' e2'
        cases HEQ
        simp
  | adv n e IH =>
    cases H1 with
    | adv n1 e1' =>
      cases H2 with
      | adv n2 e2' =>
        have HN : n1 = n2 := by rfl
        cases HN
        have HEQ := TYPED.type_uniq e1' e2'
        cases HEQ
        simp
  | fix' σ e IH =>
    cases H1 with
    | fix' e1' =>
      cases H2 with
      | fix' e2' =>
        specialize (IH e1' e2')
        simp
  | pair e1 e2 IH1 IH2 =>
    cases H1 with
    | pair e1_1 e1_2 =>
      cases H2 with
      | pair e2_1 e2_2 =>
        have EQ1 := TYPED.type_uniq e1_1 e2_1
        have EQ2 := TYPED.type_uniq e1_2 e2_2
        cases EQ1
        cases EQ2
        simp
  | proj σ e d IH =>
    cases d with
    | L =>
      cases H1 with
      | projL e1' =>
        cases H2 with
        | projL e2' =>
          have HEQ := TYPED.type_uniq e1' e2'
          cases HEQ
          simp
    | R =>
      cases H1 with
      | projR e1' =>
        cases H2 with
        | projR e2' =>
          have HEQ := TYPED.type_uniq e1' e2'
          cases HEQ
          simp
  | inl B e IH => cases TYPED.type_uniq H1 H2; simp
  | inr A e IH => cases TYPED.type_uniq H1 H2; simp
  | case A B e f g IHe IHf IHg => cases TYPED.type_uniq H1 H2; simp
  | or e1 e2 IH1 IH2 =>
    cases H1 with
    | or e1_1 e1_2 =>
      cases H2 with
      | or e2_1 e2_2 =>
        have EQ1 := TYPED.type_uniq e1_1 e2_1
        have EQ2 := TYPED.type_uniq e1_2 e2_2
        cases EQ1
        cases EQ2
        simp
  | and e1 e2 IH1 IH2 =>
    cases H1 with
    | and e1_1 e1_2 =>
      cases H2 with
      | and e2_1 e2_2 =>
        have EQ1 := TYPED.type_uniq e1_1 e2_1
        have EQ2 := TYPED.type_uniq e1_2 e2_2
        cases EQ1
        cases EQ2
        simp
  | impl e1 e2 IH1 IH2 =>
    cases H1 with
    | impl e1_1 e1_2 =>
      cases H2 with
      | impl e2_1 e2_2 =>
        have EQ1 := TYPED.type_uniq e1_1 e2_1
        have EQ2 := TYPED.type_uniq e1_2 e2_2
        cases EQ1
        cases EQ2
        simp
  | forall' σ e IH =>
    cases H1 with
    | forall' e1' =>
      cases H2 with
      | forall' e2' =>
        have HEQ := TYPED.type_uniq e1' e2'
        cases HEQ
        simp
  | exists' σ e IH =>
    cases H1 with
    | exists' e1' =>
      cases H2 with
      | exists' e2' =>
        have HEQ := TYPED.type_uniq e1' e2'
        cases HEQ
        simp
  | lift e IH =>
    cases H1 with
    | lift e1' =>
      cases H2 with
      | lift e2' =>
        have HEQ := TYPED.type_uniq e1' e2'
        cases HEQ
        simp
  | true =>
    cases H1 with
    | true _ =>
      cases H2 with
      | true _ => rfl
  | false =>
    cases H1 with
    | false _ =>
      cases H2 with
      | false _ => rfl
  | eq τ e1 e2 IH1 IH2 =>
    cases H1 with
    | eq e1_1 e1_2 =>
      cases H2 with
      | eq e2_1 e2_2 =>
        have EQ1 := TYPED.type_uniq e1_1 e2_1
        have EQ2 := TYPED.type_uniq e1_2 e2_2
        cases EQ1
        cases EQ2
        simp
  | ax t f =>
    cases H1 with
    | ax H1 =>
      cases H2 with
      | ax H2 =>
        rfl

theorem TYPED.typed_uniq (H1 H2 : TYPED Γ e τ) : H1 = H2 := by
  rfl

instance : Subsingleton (TYPED Γ e τ) := ⟨TYPED.typed_uniq⟩

inductive TYPED_REN : REN → CTX.{i} → CTX.{i} → Type (i + 1) where
| id : 0 < Γ.length → TYPED_REN .id Γ Γ
| comp : TYPED_REN σ' Δ Ψ → TYPED_REN σ Γ Δ → TYPED_REN (.comp σ' σ) Γ Ψ
| local_weaken τ : TYPED_REN σ (Ψ :: Γ) (Φ :: Δ) → TYPED_REN (.local_weaken σ) ((τ :: Ψ) :: Γ) (Φ :: Δ)
| cons τ : TYPED_REN σ (Ψ :: Γ) (Φ :: Δ) → TYPED_REN (.cons σ) ((τ :: Ψ) :: Γ) ((τ :: Φ) :: Δ)
| global_lift : TYPED_REN σ Γ Δ → TYPED_REN (.global_lift σ) ([] :: Γ) ([] :: Δ)
| global_shift n : n = Ψ.length → TYPED_REN σ Γ Δ → TYPED_REN (.global_shift n σ) (Ψ ++ Γ) Δ

theorem typing_stack_len {Γ e τ} (H : TYPED Γ e τ) : 0 < Γ.length := by
  induction H with
  | embed H =>
    exact H
  | embed_apply f x => assumption
  | pure e => assumption
  | @var' Γ Δ τ p q Heq1 Heq2 =>
    cases H : List.length Γ
    . rw [List.length_eq_zero_iff] at H
      rw [H] at Heq1
      simp at Heq1
    . simp
  | app e1 e2 => assumption
  | lam' e IH => assumption
  | delay e => assumption
  | adv e IH =>
    simp at *
    omega
  | fix' e => assumption
  | pair e1 e2 => assumption
  | projL e => assumption
  | projR e => assumption
  | inl e => assumption
  | inr e => assumption
  | case e f g => assumption
  | or e1 e2 => assumption
  | and e1 e2 => assumption
  | impl e1 e2 => assumption
  | forall' e IH => assumption
  | exists' e IH => assumption
  | lift e => assumption
  | true => assumption
  | false => assumption
  | eq e1 e2 IH1 IH2 => assumption
  | ax H => assumption

theorem TYPED.ctx_pad {Γ : CTX.{i}} {e : EXPR.{i}} {τ : TYPE.{i}} (H : TYPED Γ e τ) :
    ∀ Γ' : CTX.{i}, TYPED (Γ ++ Γ') e τ := by
  induction H with
  | embed h => intro Γ'; exact TYPED.embed (by simp; omega)
  | embed_apply _ _ IH1 IH2 => intro Γ'; exact TYPED.embed_apply (IH1 Γ') (IH2 Γ')
  | pure _ IH => intro Γ'; exact TYPED.pure (IH Γ')
  | @var' Γ Δ τ p q Heq1 Heq2 =>
    intro Γ'
    refine TYPED.var' p q ?_ Heq2
    have hp : p < Γ.length := by
      rcases Nat.lt_or_ge p Γ.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at Heq1; simp at Heq1
    rw [List.getElem?_append_left hp]
    exact Heq1
  | app _ _ IH1 IH2 => intro Γ'; exact TYPED.app (IH1 Γ') (IH2 Γ')
  | lam' _ IH => intro Γ'; exact TYPED.lam' (IH Γ')
  | delay h _ IH => intro Γ'; exact TYPED.delay (by simp; omega) (IH Γ')
  | @adv n Γ e A hn Hsub IH =>
    intro Γ'
    have hlt : n < Γ.length := by
      have h := typing_stack_len Hsub
      simp only [List.length_drop] at h
      omega
    refine TYPED.adv hn ?_
    rw [List.drop_append_of_le_length (Nat.le_of_lt hlt)]
    exact IH Γ'
  | fix' _ IH => intro Γ'; exact TYPED.fix' (IH Γ')
  | pair _ _ IH1 IH2 => intro Γ'; exact TYPED.pair (IH1 Γ') (IH2 Γ')
  | projL _ IH => intro Γ'; exact TYPED.projL (IH Γ')
  | projR _ IH => intro Γ'; exact TYPED.projR (IH Γ')
  | inl _ IH => intro Γ'; exact TYPED.inl (IH Γ')
  | inr _ IH => intro Γ'; exact TYPED.inr (IH Γ')
  | case _ _ _ IHe IHf IHg => intro Γ'; exact TYPED.case (IHe Γ') (IHf Γ') (IHg Γ')
  | or _ _ IH1 IH2 => intro Γ'; exact TYPED.or (IH1 Γ') (IH2 Γ')
  | and _ _ IH1 IH2 => intro Γ'; exact TYPED.and (IH1 Γ') (IH2 Γ')
  | impl _ _ IH1 IH2 => intro Γ'; exact TYPED.impl (IH1 Γ') (IH2 Γ')
  | forall' _ IH => intro Γ'; exact TYPED.forall' (IH Γ')
  | exists' _ IH => intro Γ'; exact TYPED.exists' (IH Γ')
  | lift _ IH => intro Γ'; exact TYPED.lift (IH Γ')
  | true h => intro Γ'; exact TYPED.true (by simp; omega)
  | false h => intro Γ'; exact TYPED.false (by simp; omega)
  | eq _ _ IH1 IH2 => intro Γ'; exact TYPED.eq (IH1 Γ') (IH2 Γ')
  | ax t f h => intro Γ'; exact TYPED.ax t f (by simp; omega)

theorem typing_ren_len {σ : REN} {Γ Δ}
  (H : TYPED_REN σ Γ Δ) : Δ.length ≤ Γ.length := by
  induction H with
  | id => simp
  | @comp σ' _ _ σ _ H1 H2 IH1 IH2 => omega
  | @local_weaken κ Ψ _ _ _ τ H IH => exact IH
  | @cons κ Ψ Γ' Φ Δ τ H IH => exact IH
  | @global_lift _ _ _ _ IH => simp; exact IH
  | @global_shift n _ _ _ H1 H2 IH => simp; omega

theorem ren_len (σ : REN) (Hσ : TYPED_REN σ Γ Δ)
  : 0 < Δ.length := by
  induction Hσ with
  | id Hl => assumption
  | comp _ _ IH _ => assumption
  | cons _ _ IH => assumption
  | local_weaken _ _ IH => assumption
  | global_lift => simp
  | global_shift _ _ _ IH => assumption

theorem ren_len' (σ : REN) (Hσ : TYPED_REN σ Γ Δ)
  : 0 < Γ.length := by
  induction Hσ with
  | id Hl => assumption
  | comp _ _ IH _ => assumption
  | cons _ _ IH => assumption
  | local_weaken _ _ IH => assumption
  | global_lift => simp
  | global_shift _ _ _ IH => simp; omega

@[irreducible] def EXPR.var.{i} (_nm : Lean.Name) (n m : Nat) : EXPR.{i} := EXPR.var' n m
@[irreducible] def EXPR.lam.{i} (_nm : Lean.Name) (τ : TYPE.{i}) (e : EXPR.{i}) : EXPR.{i} := EXPR.lam' τ e
@[irreducible] def EXPR.forall.{i} (_nm : Lean.Name) (τ : TYPE.{i}) (e : EXPR.{i}) : EXPR.{i} := EXPR.forall' τ e
@[irreducible] def EXPR.exists.{i} (_nm : Lean.Name) (τ : TYPE.{i}) (e : EXPR.{i}) : EXPR.{i} := EXPR.exists' τ e
@[irreducible] def EXPR.fix.{i} (_nm : Lean.Name) (τ : TYPE.{i}) (e : EXPR.{i}) : EXPR.{i} := EXPR.fix' τ e
@[irreducible] def EXPR.annot.{i} (e : EXPR.{i}) (_τ : TYPE.{i}) : EXPR.{i} := e

unseal EXPR.var
unseal EXPR.lam
unseal EXPR.forall
unseal EXPR.exists
unseal EXPR.fix
unseal EXPR.annot

theorem TYPED.var : ∀ {Γ : CTX.{i}} {Δ : OCTX.{i}} {τ : TYPE.{i}} (p q : Nat),
  (Heq1 : Γ[p]? = some Δ) →
  (Heq2 : Δ[q]? = τ) →
  TYPED Γ (EXPR.var nm p q) τ := TYPED.var'

theorem TYPED.lam {_nm} {Γ Δ A B e} (H : TYPED ((A :: Δ) :: Γ) e B)
  : TYPED (Δ :: Γ) (EXPR.lam _nm A e) (TYPE.arr A B) := by
  simp [EXPR.lam]
  constructor; assumption

theorem TYPED.forall {_nm} {Γ Δ A e} (H : TYPED ((A :: Δ) :: Γ) e TYPE.prop)
  : TYPED (Δ :: Γ) (EXPR.forall _nm A e) TYPE.prop := by
  simp [EXPR.forall]
  constructor; assumption

theorem TYPED.exists {_nm} {Γ Δ A e} (H : TYPED ((A :: Δ) :: Γ) e TYPE.prop)
  : TYPED (Δ :: Γ) (EXPR.exists _nm A e) TYPE.prop := by
  simp [EXPR.exists]
  constructor; assumption

theorem TYPED.fix {_nm} {Γ Δ A e} (H : TYPED ((TYPE.later A :: Δ) :: Γ) e A)
  : TYPED (Δ :: Γ) (EXPR.fix _nm (TYPE.later A) e) A := by
  simp [EXPR.fix]
  constructor; assumption

theorem TYPED.var_inversion (H : TYPED Γ (.var nm n m) τ) :
  ∃ Δ, Γ[n]? = some Δ ∧ Δ[m]? = τ := by
  apply H.var'_inversion

theorem TYPED.lam_inversion (H : TYPED (Γ :: Γs) (.lam nm τ e) σ) :
  ∃ τ', σ = TYPE.arr τ τ' ∧ TYPED ((τ :: Γ) :: Γs) e τ' := by
  apply H.lam'_inversion

theorem TYPED.forall_inversion (H : TYPED (Γ :: Γs) (.forall nm τ e) σ) :
  σ = TYPE.prop ∧ TYPED ((τ :: Γ) :: Γs) e TYPE.prop := by
  apply H.forall'_inversion

theorem TYPED.exists_inversion (H : TYPED (Γ :: Γs) (.exists nm τ e) σ) :
  σ = TYPE.prop ∧ TYPED ((τ :: Γ) :: Γs) e TYPE.prop := by
  apply H.exists'_inversion

theorem TYPED.fix_inversion (H : TYPED (Γ :: Γs) (.fix nm τ e) σ) :
  τ = TYPE.later σ ∧ TYPED ((TYPE.later σ :: Γ) :: Γs) e σ := by
  apply H.fix'_inversion

theorem TYPED.var_explicit {nm : Name} (p : Fin Γ.length) (q : Fin Γ[p].length)
  : TYPED Γ (EXPR.var nm p q) Γ[p][q] := by
  apply (@TYPED.var' Γ Γ[p])
  . simp
  . simp

theorem TYPED.var'_explicit (p : Fin Γ.length) (q : Fin Γ[p].length)
  : TYPED Γ (EXPR.var' p q) Γ[p][q] := by
  apply (@TYPED.var' Γ Γ[p])
  . simp
  . simp

structure SYNT (ty : TYPE.{i}) : Type (i + 1) where
  expr : EXPR.{i}
  proof : TYPED [[]] expr ty

@[simp, implicit_reducible]
def offset_ren (σ : REN) (n : Nat) : Nat :=
match n with
| .zero => 0
| .succ n' =>
  match σ with
  | .id => n
  | @REN.comp σ' σ => offset_ren σ (offset_ren σ' n)
  | @REN.local_weaken σ => offset_ren σ n
  | @REN.cons σ => offset_ren σ n
  | @REN.global_lift σ => offset_ren σ n' + 1
  | @REN.global_shift p σ => p + offset_ren σ n

@[simp]
theorem offset_ren_zero (σ : REN) : offset_ren σ 0 = 0 := by
  simp [offset_ren]

theorem offset_ren_ge (σ : REN) (n : Nat) : n ≤ offset_ren σ n := by
  induction σ generalizing n with
  | id => cases n <;> simp
  | comp σ σ' IH IH' =>
    cases n with
    | zero => simp
    | succ n =>
      simp only [offset_ren]
      exact (IH _).trans (IH' _)
  | local_weaken σ IH =>
    cases n with
    | zero => simp
    | succ n => exact IH _
  | cons σ IH =>
    cases n with
    | zero => simp
    | succ n => exact IH _
  | global_lift σ IH =>
    cases n with
    | zero => simp
    | succ n =>
      simp only [offset_ren]
      have := IH n
      omega
  | global_shift p σ IH =>
    cases n with
    | zero => simp
    | succ n =>
      simp only [offset_ren]
      have := IH (n + 1)
      omega

@[simp]
theorem offset_ren_pos (σ : REN) (n : Nat) (Hn : 0 < n) : 0 < offset_ren σ n := by
  exact Hn.trans_le (offset_ren_ge σ n)

@[simp]
theorem offset_ren_pos_iff (σ : REN) (n : Nat) : 0 < n ↔ 0 < offset_ren σ n := by
  constructor
  · exact offset_ren_pos σ n
  · intro h
    cases n with
    | zero => simp at h
    | succ n => exact Nat.zero_lt_succ n

theorem offset_ren_len (σ : REN) (Hσ : TYPED_REN σ Γ Δ) (n : Nat)
(Hn : n < Δ.length)
  : offset_ren σ n < Γ.length := by
  revert n
  induction Hσ with
    | id =>
      intros n Hn
      cases n with
      | zero => simp; omega
      | succ n' => simp; omega
    | @comp σ' _ _ σ _ H1 H2 IH1 IH2 =>
      intros n Hn
      cases n with
      | zero =>
        simp
        specialize (IH2 0)
        simp at IH2
        apply IH2
        specialize (IH1 0)
        simp at IH1
        apply IH1
        assumption
      | succ n' =>
        simp
        specialize (IH2 (offset_ren σ' (n' + 1)))
        apply IH2
        apply IH1
        assumption
    | @local_weaken κ Ψ _ _ _ τ H IH =>
      intros n Hn
      cases n with
      | zero => simp
      | succ n' =>
        simp at *
        apply IH
        omega
    | @cons κ Ψ Γ Φ Δ τ H IH =>
      intros n Hn
      cases n with
      | zero => simp
      | succ n' =>
        simp at *
        apply IH
        omega
    | @global_lift σ _ _ _ IH =>
      intros n Hn
      cases n with
      | zero => simp
      | succ n' =>
        simp at *
        specialize (IH n' Hn)
        omega
    | @global_shift p _ _ _ H1 H2 H3 IH =>
      intros n Hn
      cases n with
      | zero =>
        simp
        have T := ren_len' _ H3
        omega
      | succ n' =>
        simp at *
        specialize (IH (n' + 1) (by omega))
        omega

@[simp]
def weaken_var' (σ : REN) (n m : Nat) : Nat × Nat :=
match σ with
| .id => ⟨n, m⟩
| @REN.comp σ' σ =>
  let ⟨n', m'⟩ := weaken_var' σ' n m
  weaken_var' σ n' m'
| @REN.local_weaken σ =>
  let ⟨n', m'⟩ := weaken_var' σ n m
  ⟨n', match n' with | .zero => m' + 1 | _ => m'⟩
| @REN.cons σ' =>
  match n with
  | .zero =>
    match m with
    | .zero => ⟨0, 0⟩
    | .succ m =>
      let ⟨n', m'⟩ := weaken_var' σ' 0 m
      ⟨n', match n' with | .zero => m' + 1 | _ => m'⟩
  | .succ n =>
    let ⟨n', m'⟩ := weaken_var' σ' (n + 1) m
    ⟨n', match n' with | .zero => m' + 1 | _ => m'⟩
| @REN.global_lift σ' =>
  match n with
  | .zero => ⟨0, m⟩
  | .succ n' =>
    let ⟨n', m'⟩ := weaken_var' σ' n' m
    ⟨(n' + 1), m'⟩
| @REN.global_shift p σ' =>
  let ⟨n', m'⟩ := weaken_var' σ' n m
  ⟨(p + n'), m'⟩

def weaken_var'_correct {Γ Δ : CTX.{i}} (σ : REN)
  (n m : Nat) (Hσ : TYPED_REN σ Γ Δ) (Ψ : OCTX.{i}) τ
  (Hn : Δ[n]? = some Ψ) (Hm : Ψ[m]? = some τ)
  : Σ' Ψ' : OCTX.{i}, ((Γ[(weaken_var' σ n m).fst]? = some Ψ') ∧ (Ψ'[(weaken_var' σ n m).snd]? = some τ)) :=
  match Hσ with
  | TYPED_REN.id _ => by
    exists Ψ
  | @TYPED_REN.comp σ' _ _ σ _ H1 H2 => by
    let ⟨Ψ', G1, G2⟩ := (weaken_var'_correct _ n m H1 _ _ Hn Hm)
    let ⟨Ψ'', J1, J2⟩ := (weaken_var'_correct _ (weaken_var' σ' n m).fst (weaken_var' σ' n m).snd H2 Ψ' τ G1 G2)
    exists Ψ''
  | @TYPED_REN.local_weaken σ Ψ _ _ _ τ H => by
    let ⟨Ψ'', H1, H2⟩ := (weaken_var'_correct _ n m H _ _ Hn Hm)
    exists (match (weaken_var' σ n m).fst with | .zero => (τ :: Ψ'') | _ => Ψ'')
    constructor
    . cases HEQ : (weaken_var' σ n m).fst with
      | zero =>
        simp; rw [HEQ] at H1
        simp at H1
        rw [HEQ]
        simp
        assumption
      | succ q =>
        simp; rw [HEQ] at H1
        simp at H1
        rw [HEQ]
        simp
        rw [H1]
    . cases HEQ : (weaken_var' σ n m).fst with
      | zero =>
        simp; rw [HEQ] at H1
        simp at H1
        rw [HEQ]
        simp
        assumption
      | succ q =>
        simp; rw [HEQ] at H1
        simp at H1
        rw [HEQ]
        simp
        assumption
  | @TYPED_REN.cons σ Ψ Γ Φ Δ τ H => by
    cases n with
    | zero =>
      cases m with
      | zero =>
        exists (τ :: Ψ)
        constructor
        . simp
        . simp at *
          rw [<-Hn] at Hm; simp at Hm
          exact Hm
      | succ m' =>
        simp at Hn
        rw [<-Hn] at Hm
        simp at Hm
        let ⟨Ψ'', H1, H2⟩ := weaken_var'_correct _ 0 m' H Φ _ (Eq.refl _) Hm
        exists (match (weaken_var' σ 0 m').fst with | .zero => (τ :: Ψ'') | _ => Ψ'')
        cases HEQ : (weaken_var' σ 0 m').fst with
        | zero =>
          simp; rw [HEQ]
          simp; rw [HEQ] at H1; simp at H1
          rw [H2]
          constructor
          . assumption
          . simp
        | succ q =>
          simp; rw [HEQ]
          simp; rw [HEQ] at H1; simp at H1
          rw [H2]
          constructor
          . assumption
          . rfl
    | succ n' =>
      let ⟨Ψ'', Hn', Hm'⟩ := weaken_var'_correct _ (n' + 1) m H _ _ Hn Hm
      exists (match (weaken_var' σ (n' + 1) m).fst with | .zero => τ :: Ψ'' | _ => Ψ'')
      cases HEQ : (weaken_var' σ (n' + 1) m).fst with
      | zero =>
        simp; rw [HEQ]; simp at *
        rw [HEQ] at Hn'; simp at Hn'
        constructor
        . assumption
        . assumption
      | succ q =>
        simp; rw [HEQ]; simp at *
        rw [HEQ] at Hn'; simp at Hn'
        constructor
        . assumption
        . assumption
  | @TYPED_REN.global_lift σ _ _ H => by
    cases n with
    | zero => exfalso; simp at *; rw [Hn] at Hm; cases Hm
    | succ n' =>
      simp
      let ⟨Ψ'', Hn', Hm'⟩ := weaken_var'_correct _ n' m H Ψ τ Hn Hm
      exists Ψ''
  | @TYPED_REN.global_shift σ _ _ _ p H2 H3 => by
    let ⟨Ψ'', Hn', Hm'⟩ := weaken_var'_correct _ n m H3 Ψ τ Hn Hm
    exists Ψ''; simp
    rw [List.getElem?_append]; rw [ite_cond_eq_false]
    . constructor
      . rw [H2]; rw [<-Hn']
        congr 1
        omega
      . assumption
    . simp; omega

theorem weaken_var'_typing {Γ : CTX.{i}}
(H : TYPED Γ (.var' n m) τ)
(σ : REN) (Hσ : TYPED_REN σ Δ Γ) : TYPED Δ (.var' (weaken_var' σ n m).1 (weaken_var' σ n m).2) τ := by
  cases H with
  | var' _ _ Heq1 Heq2 =>
    let ⟨Ψ, H1, H2⟩ := weaken_var'_correct σ n m Hσ _ _ Heq1 Heq2
    constructor
    . exact H1
    . exact H2

@[simp]
def cut_ren (σ : REN) (n : Nat) : REN :=
match n with
| .zero => σ
| .succ n' =>
  match σ with
  | .id => .id
  | @REN.comp σ' σ => .comp (cut_ren σ' n) (cut_ren σ (offset_ren σ' n))
  | @REN.local_weaken σ => cut_ren σ n
  | @REN.cons σ => cut_ren σ n
  | @REN.global_lift σ => cut_ren σ n'
  | @REN.global_shift _p σ => cut_ren σ n

@[simp]
theorem cut_ren_zero (σ : REN) : cut_ren σ 0 = σ := by
  simp [cut_ren]

def ren_transport_left {Γ Δ Ψ} (Heq : Γ = Δ) (H : TYPED_REN σ Γ Ψ) : TYPED_REN σ Δ Ψ := by
  rw [←Heq]
  assumption

@[simp]
def local_weaken_list (n : Nat) (H : REN) : REN :=
  match n with
  | .zero => H
  | .succ xs => REN.local_weaken (local_weaken_list xs H)

def local_weaken_list_typed (Ψ : OCTX.{i}) (H : TYPED_REN σ (Γ :: Γs) (Δ :: Δs))
  : TYPED_REN (local_weaken_list Ψ.length σ) ((Ψ ++ Γ) :: Γs) (Δ :: Δs) :=
  match Ψ with
  | .nil => H
  | .cons τ Ψ' => TYPED_REN.local_weaken τ (local_weaken_list_typed Ψ' H)

def cut_ren_typing (σ : REN) (Hσ : TYPED_REN σ Γ Δ) (n : Nat)
  (Hn : n < Δ.length)
   : TYPED_REN (cut_ren σ n) (Γ.drop (offset_ren σ n)) (Δ.drop n) :=
match Hσ with
| .id _ =>
  match n with
  | Nat.zero => TYPED_REN.id Hn
  | Nat.succ n' => TYPED_REN.id (by simp; omega)
| @TYPED_REN.comp σ' _ _ σ _ H1 H2 =>
  match n with
  | Nat.zero => TYPED_REN.comp H1 H2
  | Nat.succ n' => TYPED_REN.comp (cut_ren_typing _ H1 _ Hn) (cut_ren_typing _ H2 _ (offset_ren_len _ H1 _ Hn))
| @TYPED_REN.local_weaken σ Ψ Γ _ _ τ H =>
  match n with
  | Nat.zero => TYPED_REN.local_weaken _ H
  | Nat.succ n' =>
    have EQ : List.drop (offset_ren σ (n' + 1)) (Ψ :: Γ) = List.drop (offset_ren σ (n' + 1)) ((τ :: Ψ) :: Γ) := by
      have T := offset_ren_pos σ (n' + 1) (by omega)
      have ⟨m, EQ⟩ : ∃ m, offset_ren σ (n' + 1) = m + 1 := by
        cases EQ : offset_ren σ (n' + 1) with
        | zero => rw [EQ] at T; simp at T
        | succ m => exists m
      rw [EQ]; simp
    ren_transport_left EQ (cut_ren_typing _ H (n' + 1) Hn)
| @TYPED_REN.cons σ Ψ Γ Φ Δ τ H =>
  match n with
  | Nat.zero => TYPED_REN.cons _ H
  | Nat.succ n' =>
    have EQ : List.drop (offset_ren σ (n' + 1)) (Ψ :: Γ) = List.drop (offset_ren σ (n' + 1)) ((τ :: Ψ) :: Γ) := by
      have T := offset_ren_pos σ (n' + 1) (by omega)
      have ⟨m, EQ⟩ : ∃ m, offset_ren σ (n' + 1) = m + 1 := by
        cases EQ : offset_ren σ (n' + 1) with
        | zero => rw [EQ] at T; simp at T
        | succ m => exists m
      rw [EQ]; simp
    ren_transport_left EQ (cut_ren_typing _ H (n' + 1) Hn)
| @TYPED_REN.global_lift σ Γ' _ H =>
  match n with
  | Nat.zero => TYPED_REN.global_lift H
  | Nat.succ n' =>
    have EQ : List.drop (offset_ren σ n') Γ' = (List.drop (offset_ren σ n' + 1) ([] :: Γ')) := by
      rw [List.drop_cons]; simp; omega
    ren_transport_left EQ (cut_ren_typing _ H n' (by simp at *; omega))
| @TYPED_REN.global_shift σ Γ' _ Ψ' H1 H2 H3 =>
  match n with
  | Nat.zero => TYPED_REN.global_shift H1 H2 H3
  | Nat.succ n' =>
    have EQ : (List.drop (offset_ren σ (n' + 1)) Γ') = (List.drop (offset_ren (REN.global_shift H1 σ) n'.succ) (Ψ' ++ Γ')) := by
      rw [H2, List.drop_append]; simp
    ren_transport_left EQ (cut_ren_typing _ H3 (n' + 1) (by omega))

@[simp]
def weaken (e : EXPR.{i}) (σ : REN) : EXPR.{i} :=
  match e with
  | .embed A a => .embed A a
  | .embed_apply A B f x => .embed_apply A B (weaken f σ) (weaken x σ)
  | .pure e => .pure (weaken e σ)
  | .var' n m => .var' (weaken_var' σ n m).fst (weaken_var' σ n m).snd
  | .app B e1 e2 => .app B (weaken e1 σ) (weaken e2 σ)
  | .lam' t e => .lam' t (weaken e (.cons σ))
  | .delay e => .delay (weaken e (.global_lift σ))
  | .adv n e => .adv (offset_ren σ n) (weaken e (cut_ren σ n))
  | .fix' t e => .fix' t (weaken e (.cons σ))
  | .pair e1 e2 => .pair (weaken e1 σ) (weaken e2 σ)
  | .proj B e d => .proj B (weaken e σ) d
  | .inl B e => .inl B (weaken e σ)
  | .inr A e => .inr A (weaken e σ)
  | .case A B e f g => .case A B (weaken e σ) (weaken f σ) (weaken g σ)
  | .or e1 e2 => .or (weaken e1 σ) (weaken e2 σ)
  | .and e1 e2 => .and (weaken e1 σ) (weaken e2 σ)
  | .impl e1 e2 => .impl (weaken e1 σ) (weaken e2 σ)
  | .forall' t e => .forall' t (weaken e (.cons σ))
  | .exists' t e => .exists' t (weaken e (.cons σ))
  | .lift e => .lift (weaken e σ)
  | .true => .true
  | .false => .false
  | .eq B e1 e2 => .eq B (weaken e1 σ) (weaken e2 σ)
  | .ax t f => .ax t f

@[simp]
theorem weaken_var : weaken (.var nm n m) σ = .var nm (weaken_var' σ n m).fst (weaken_var' σ n m).snd := by rfl

@[simp]
theorem weaken_lam : weaken (.lam nm τ e) σ = .lam nm τ (weaken e σ.cons) := by rfl

@[simp]
theorem weaken_forall : weaken (.forall nm τ e) σ = .forall nm τ (weaken e σ.cons) := by rfl

@[simp]
theorem weaken_exists : weaken (.exists nm τ e) σ = .exists nm τ (weaken e σ.cons) := by rfl

@[simp]
theorem weaken_fix : weaken (.fix nm τ e) σ = .fix nm τ (weaken e σ.cons) := by rfl

theorem weaken_typing {Γ : CTX.{i}} {e : EXPR.{i}} {τ : TYPE.{i}} (H : TYPED Γ e τ)
  (Hσ : TYPED_REN σ Δ Γ) : TYPED Δ (weaken e σ) τ :=
match H with
| .embed H => by
  constructor
  let _ := typing_ren_len Hσ
  omega
| .embed_apply H1 H2 => by
  simp [weaken]
  constructor
  . apply weaken_typing <;> assumption
  . apply weaken_typing <;> assumption
| .pure H => by
  simp [weaken]
  constructor
  apply weaken_typing <;> assumption
| @TYPED.var' Γ Δ τ p q Heq1 Heq2 => by
  apply weaken_var'_typing
  . constructor
    . exact Heq1
    . exact Heq2
  . assumption
| .app e1 e2 => by
  constructor
  . apply weaken_typing <;> assumption
  . apply weaken_typing <;> assumption
| @TYPED.lam' Δ' Ψ A B  _ e => by
  simp [weaken]
  let T := typing_ren_len Hσ
  let ⟨Φ, HEQ⟩ : Σ' Φ, Δ = (Φ :: Δ.drop 1) := by
    cases Δ with
    | nil => exfalso; simp at T
    | cons h t => exists h
  rw [HEQ]
  rw [HEQ] at Hσ
  constructor
  apply weaken_typing
  . assumption
  . constructor; assumption
| @TYPED.delay Γ' e τ H1 H2 => by
  constructor
  . let _ := typing_ren_len Hσ
    omega
  . apply (@weaken_typing (REN.global_lift σ) ([] :: Δ))
    . assumption
    . constructor
      assumption
| @TYPED.adv i Γ' _ t G e => by
  simp [weaken]
  constructor
  . exact offset_ren_pos σ i (by omega)
  . apply weaken_typing
    . assumption
    . apply cut_ren_typing
      . assumption
      . let T := typing_stack_len e
        simp at T
        omega
| .fix' e => by
  simp [weaken]
  let T := typing_ren_len Hσ
  let ⟨Φ, HEQ⟩ : Σ' Φ, Δ = (Φ :: Δ.drop 1) := by
    cases Δ with
    | nil => exfalso; simp at T
    | cons h t => exists h
  rw [HEQ]
  rw [HEQ] at Hσ
  constructor
  apply weaken_typing
  . assumption
  . constructor
    assumption
| .pair e1 e2 => by
  simp [weaken]
  constructor
  . apply weaken_typing <;> assumption
  . apply weaken_typing <;> assumption
| .projL e => by
  simp [weaken]
  constructor
  apply weaken_typing <;> assumption
| .projR e => by
  simp [weaken]
  constructor
  apply weaken_typing <;> assumption
| .inl e => by
  simp [weaken]
  constructor
  apply weaken_typing <;> assumption
| .inr e => by
  simp [weaken]
  constructor
  apply weaken_typing <;> assumption
| .case e f g => by
  simp [weaken]
  constructor
  · apply weaken_typing <;> assumption
  · apply weaken_typing <;> assumption
  · apply weaken_typing <;> assumption
| .or e1 e2 => by
  simp [weaken]
  constructor
  . apply weaken_typing <;> assumption
  . apply weaken_typing <;> assumption
| .and e1 e2 => by
  simp [weaken]
  constructor
  . apply weaken_typing <;> assumption
  . apply weaken_typing <;> assumption
| .impl e1 e2 => by
  simp [weaken]
  constructor
  . apply weaken_typing <;> assumption
  . apply weaken_typing <;> assumption
| @TYPED.forall' Δ' Ψ A _ e => by
  simp [weaken]
  let T := typing_ren_len Hσ
  let ⟨Φ, HEQ⟩ : Σ' Φ, Δ = (Φ :: Δ.drop 1) := by
    cases Δ with
    | nil => exfalso; simp at T
    | cons h t => exists h
  rw [HEQ]
  rw [HEQ] at Hσ
  constructor
  apply weaken_typing
  . assumption
  . constructor
    assumption
| @TYPED.exists' Δ' Ψ A _ e => by
  simp [weaken]
  let T := typing_ren_len Hσ
  let ⟨Φ, HEQ⟩ : Σ' Φ, Δ = (Φ :: Δ.drop 1) := by
    cases Δ with
    | nil => exfalso; simp at T
    | cons h t => exists h
  rw [HEQ]
  rw [HEQ] at Hσ
  constructor
  apply weaken_typing
  . assumption
  . constructor
    assumption
| .lift e => by
  simp [weaken]
  constructor
  apply weaken_typing <;> assumption
| .true H => by
  simp [weaken]
  constructor
  let T := typing_ren_len Hσ
  omega
| .false H => by
  simp [weaken]
  constructor
  let T := typing_ren_len Hσ
  omega
| .eq e1 e2 => by
  simp [weaken]
  constructor
  . apply weaken_typing <;> assumption
  . apply weaken_typing <;> assumption
| .ax h1 h2 h => by
  simp [weaken]
  constructor
  let T := typing_ren_len Hσ
  omega

inductive SUBST : Type (i + 1) where
| epsilon : SUBST
| cons : EXPR.{i} → SUBST → SUBST

inductive TSUBST : SUBST.{i} → CTX.{i} → OCTX.{i} → Type (i + 1) where
| epsilon : 0 < Γ.length → TSUBST SUBST.epsilon Γ []
| cons : TYPED Γ e τ → TSUBST σ Γ Δ → TSUBST (SUBST.cons e σ) Γ (τ :: Δ)

@[simp]
def SUBST.sr_compose (σ : SUBST.{i}) (δ : REN) : SUBST.{i} :=
  match σ with
  | SUBST.epsilon => SUBST.epsilon
  | SUBST.cons e σ => SUBST.cons (weaken e δ) (sr_compose σ δ)

def TSUBST.sr_compose_typing (Hσ : TSUBST σ Γs Γ) (Hδ : TYPED_REN δ Δ Γs) : TSUBST (σ.sr_compose δ) Δ Γ :=
  match Hσ with
  | .epsilon _ => by
    simp [SUBST.sr_compose]; constructor
    have T := typing_ren_len Hδ
    omega
  | .cons Hτ Hσ => by
    simp [SUBST.sr_compose]; constructor
    . apply weaken_typing
      . apply Hτ
      . apply Hδ
    . apply TSUBST.sr_compose_typing
      . assumption
      . apply Hδ

@[simp]
def SUBST.drop (σ : SUBST) : SUBST := sr_compose σ (REN.local_weaken REN.id)

def TSUBST.drop_typing (Hσ : TSUBST σ (Γ :: Γs) Δ) : TSUBST σ.drop ((τ :: Γ) :: Γs) Δ :=
  sr_compose_typing Hσ (TYPED_REN.local_weaken _ (TYPED_REN.id (by simp)))

def SUBST.ext' (σ : SUBST) : SUBST := .cons (.var' 0 0) σ.drop

@[simp]
def SUBST.ext (σ : SUBST) (nm : Name) : SUBST := .cons (.var nm 0 0) σ.drop

theorem SUBST.ext_simp (σ : SUBST) (nm : Name) : SUBST.ext σ nm = SUBST.ext' σ := by rfl

def TSUBST.ext_typing (Hσ : TSUBST σ (Γ :: Γs) Δ) : TSUBST σ.ext' ((τ :: Γ) :: Γs) (τ :: Δ) :=
  TSUBST.cons
    (@TYPED.var' ((τ :: Γ) :: Γs) (τ :: Γ) _ 0 0 (Eq.refl _) (Eq.refl _))
    (sr_compose_typing Hσ (TYPED_REN.local_weaken _ (TYPED_REN.id (by simp))))

def SUBST.id (Γ : Nat) : SUBST :=
  match Γ with
  | .zero => .epsilon
  | .succ Γ => ext' (SUBST.id Γ)

def TSUBST.id (Γ : OCTX.{i}) : TSUBST (SUBST.id Γ.length) (Γ :: Δ) Γ :=
  match Γ with
  | .nil => TSUBST.epsilon (by simp)
  | .cons τ Γ => ext_typing (TSUBST.id _)

inductive SSUBST : Type (i + 1) where
| single : SUBST.{i} → SSUBST
| wk : Nat → SSUBST → SUBST.{i} → SSUBST

inductive TSSUBST : SSUBST → CTX.{i} → CTX.{i} → Type (i + 1) where
| single σ : TSUBST σ Γ Δ → TSSUBST (.single σ) Γ [Δ]
| wk n : 0 < n → n = Ψ.length → TSSUBST σs Γ Δs → TSUBST σ (Ψ ++ Γ) Δ → TSSUBST (.wk n σs σ) (Ψ ++ Γ) (Δ :: Δs)

def ssubst_transport_left {Γ Δ Ψ} (Heq : Γ = Δ) (H : TSSUBST σ Γ Ψ) : TSSUBST σ Δ Ψ := by
  rw [←Heq]
  assumption

def ssubst_transport_right {Γ Δ Ψ} (Heq : Ψ = Γ) (H : TSSUBST σ Δ Ψ) : TSSUBST σ Δ Γ := by
  rw [←Heq]
  assumption

@[simp]
def SSUBST.id (Γ : List Nat) : SSUBST :=
  match Γ with
  | [] => .single .epsilon
  | Γ :: [] => .single (SUBST.id Γ)
  | Γ :: Γs => wk 1 (SSUBST.id Γs) (SUBST.id Γ)

def TSSUBST.id_cons (Γ : OCTX.{i}) (Γs : CTX.{i}) : TSSUBST (SSUBST.id ((Γ :: Γs).map List.length)) (Γ :: Γs) (Γ :: Γs) :=
  match Γs with
  | .nil => TSSUBST.single _ (TSUBST.id _)
  | .cons Δ Δs => TSSUBST.wk 1 (Ψ := [Γ]) (σs := SSUBST.id ((Δ :: Δs).map List.length))
      (by simp) (Eq.refl _) (TSSUBST.id_cons _ _) (TSUBST.id _)

def TSSUBST.id (Γ : CTX.{i}) (HΓ : 0 < Γ.length) : TSSUBST (SSUBST.id (Γ.map List.length)) Γ Γ :=
  let ⟨Δ, Δ', EQ⟩ : Σ' Δ Δ', Γ = Δ :: Δ' := by
    cases Γ with
    | nil => exfalso; cases HΓ
    | cons Δ Δs => exists Δ, Δs
  ssubst_transport_left (Eq.symm EQ) (ssubst_transport_right (Eq.symm EQ) (EQ ▸ TSSUBST.id_cons _ _))

def TSSUBST.pad_cons (Γ : OCTX.{i}) (Γs Γ' : CTX.{i}) :
    TSSUBST (SSUBST.id ((Γ :: Γs).map List.length)) ((Γ :: Γs) ++ Γ') (Γ :: Γs) :=
  match Γs with
  | .nil => TSSUBST.single _ (TSUBST.id _)
  | .cons Δ Δs => TSSUBST.wk 1 (Ψ := [Γ]) (σs := SSUBST.id ((Δ :: Δs).map List.length))
      (by simp) (Eq.refl _) (TSSUBST.pad_cons _ _ _) (TSUBST.id _)

def TSSUBST.pad : (Γ : CTX.{i}) → (Γ' : CTX.{i}) → 0 < Γ.length →
    TSSUBST (SSUBST.id (Γ.map List.length)) (Γ ++ Γ') Γ
  | [], _, HΓ => absurd HΓ (by simp)
  | Δ :: Δs, Γ', _ => TSSUBST.pad_cons Δ Δs Γ'

@[simp, implicit_reducible]
def offset_ssubst (σ : SSUBST) (n : Nat) : Nat :=
match n with
| .zero => 0
| .succ n' =>
  match σ with
  | .single _σ => n
  | .wk p σs _σ => p + offset_ssubst σs n'

@[simp]
theorem offset_ssubst_zero (σ : SSUBST) : offset_ssubst σ 0 = 0 := by
  simp [offset_ssubst]

@[simp]
theorem offset_ssubst_pos (σ : SSUBST) (Hσ : TSSUBST σ Γ Δ) (n : Nat) (Hn : 0 < n) : 0 < offset_ssubst σ n := by
  revert n Hn
  induction Hσ with
  | single =>
    intros n Hn
    cases n with
    | zero =>
      exfalso; simp at Hn
    | succ n' => simp
  | wk m G _  _ _ IH =>
    intros n Hn
    cases n with
    | zero =>
      exfalso; simp at Hn
    | succ n' =>
      simp
      specialize (IH _ G)
      omega

theorem subst_len (σ : SUBST) (Hσ : TSUBST σ Γ Δ)
  : 0 < Γ.length := by
  induction Hσ with
  | epsilon => assumption
  | cons => assumption

theorem ssubst_len (σ : SSUBST) (Hσ : TSSUBST σ Γ Δ)
  : 0 < Γ.length := by
  induction Hσ with
  | single σ Hσ =>
    apply subst_len σ Hσ
  | wk n _ _ σs σ =>
    apply subst_len _ σ

theorem ssubst_len' (σ : SSUBST) (Hσ : TSSUBST σ Γ Δ)
  : 0 < Δ.length := by
  cases Hσ with
  | single σ Hσ => simp
  | wk n _ _ σs σ => simp

theorem offset_ssubst_len (σ : SSUBST) (Hσ : TSSUBST σ Γ Δ) (n : Nat)
(Hn : n < Δ.length)
  : offset_ssubst σ n < Γ.length := by
  revert n
  induction Hσ with
    | single _ Hσ =>
      intros n Hn
      have EQ : n = 0 := by
        simp at Hn
        trivial
      rw [EQ]
      simp
      apply subst_len
      assumption
    | wk p Hp Hpeq Hσs Hσ IH =>
      intros n Hn
      simp at Hn
      cases n with
      | zero =>
        simp
        omega
      | succ n' =>
        simp
        rw [Hpeq]
        specialize (IH n' (by omega))
        omega

theorem offset_ssubst_len' (σ : SSUBST) (Hσ : TSSUBST σ Γ Δ) (n : Nat)
(Hn : n < Δ.length)
  : n ≤ offset_ssubst σ n := by
  revert n
  induction Hσ with
  | single _ Hσ =>
    intros n Hn
    have EQ : n = 0 := by
      simp at Hn
      trivial
    rw [EQ]
    simp
  | wk p Hp Hpeq Hσs Hσ IH =>
    intros n Hn
    simp at Hn
    cases n with
    | zero =>
      simp
    | succ n' =>
      simp
      rw [Hpeq]
      specialize (IH n' (by omega))
      omega

@[simp]
def cut_ssubst (σ : SSUBST) (n : Nat) : SSUBST :=
match n with
| .zero => σ
| .succ n' =>
  match σ with
  | .single δ => .single δ
  | @SSUBST.wk _p σs _σ => cut_ssubst σs n'

@[simp]
theorem cut_ssubst_zero (σ : SSUBST) : cut_ssubst σ 0 = σ := by
  simp [cut_ssubst]

def cut_ssubst_typing (σ : SSUBST) (Hσ : TSSUBST σ Γ Δ) (n : Nat)
  (Hn : n < Δ.length)
   : TSSUBST (cut_ssubst σ n) (Γ.drop (offset_ssubst σ n)) (Δ.drop n) :=
match Hσ with
| TSSUBST.single σ Hσ =>
  match n with
  | .zero => TSSUBST.single σ Hσ
  | .succ n => by exfalso; simp at Hn
| @TSSUBST.wk σ Γ Δ _ Ψ _ p H1 H2 H3 H4 =>
  match n with
  | .zero => TSSUBST.wk p H1 H2 H3 H4
  | .succ n' =>
    have EQ : (List.drop (offset_ssubst σ n') Γ) = (List.drop (p + offset_ssubst σ n') (Ψ ++ Γ)) := by
      rw [H2]
      rw [List.drop_append]
      simp
    ssubst_transport_left EQ (cut_ssubst_typing _ H3 n' (by simp at Hn; apply Hn))

@[simp]
def SSUBST.sr_compose (σ : SSUBST.{i}) (δ : REN) : SSUBST.{i} :=
  match σ with
  | SSUBST.single σ => SSUBST.single (SUBST.sr_compose σ δ)
  | SSUBST.wk n σs σ => SSUBST.wk (offset_ren δ n) (σs.sr_compose (cut_ren δ n)) (σ.sr_compose δ)

def TSSUBST.sr_compose_typing (Hσ : TSSUBST σ Γs Γ) (Hδ : TYPED_REN δ Δ Γs) : TSSUBST (σ.sr_compose δ) Δ Γ :=
  match Hσ with
  | TSSUBST.single σ Hσ => by
    simp [SSUBST.sr_compose]; constructor
    apply TSUBST.sr_compose_typing
    . assumption
    . assumption
  | @TSSUBST.wk _ _ _ _ Ψ _ n _ HEQ Hσs Hσ => by
    simp [SSUBST.sr_compose]
    have T := typing_ren_len Hδ
    have T' := offset_ren_len δ Hδ (List.length Ψ)
    rw [<-List.take_append_drop (offset_ren δ (List.length Ψ)) Δ]
    constructor
    . apply offset_ren_pos
      assumption
    . simp
      simp at T
      rw [Nat.min_eq_left]
      . rw [HEQ]
      . rw [<-HEQ]
        apply Nat.le_of_lt
        apply offset_ren_len
        assumption
        simp
        rw [<-HEQ]
        let T'' := ssubst_len _ Hσs
        try simp at T''
        omega
    . apply TSSUBST.sr_compose_typing
      . assumption
      . have Q := cut_ren_typing δ Hδ n (by
          simp at *; rw [HEQ]
          let T'' := ssubst_len _ Hσs
          try simp at T''
          omega
        )
        rw [HEQ] at Q
        simp at Q
        rw [HEQ]
        apply Q
    . apply TSUBST.sr_compose_typing
      . assumption
      . rw [List.take_append_drop (offset_ren δ (List.length Ψ)) Δ]
        assumption

@[simp]
def SSUBST.drop (σ : SSUBST) : SSUBST := sr_compose σ (REN.local_weaken REN.id)

def TSSUBST.drop_typing (Hσ : TSSUBST σ (Γ :: Γs) Δs) : TSSUBST σ.drop ((τ :: Γ) :: Γs) Δs := by
  simp [SSUBST.drop]
  apply sr_compose_typing
  . apply Hσ
  . constructor
    constructor
    simp

@[simp]
def SSUBST.ext' (σ : SSUBST) : SSUBST :=
  match σ with
  | SSUBST.single σ => SSUBST.single σ.ext'
  | SSUBST.wk n σs σ => SSUBST.wk n σs σ.ext'

@[simp]
def SSUBST.ext (σ : SSUBST) (nm : Name) : SSUBST :=
  match σ with
  | SSUBST.single σ => SSUBST.single (σ.ext nm)
  | SSUBST.wk n σs σ => SSUBST.wk n σs (σ.ext nm)

theorem SSUBST.ext_simp (σ : SSUBST) (nm : Name) : SSUBST.ext σ nm = SSUBST.ext' σ := by rfl

def TSSUBST.ext_typing' (HEQ1 : (Γ :: Γs) = G) (HEQ2 : (Δ :: Δs) = D)
  (Hσ : TSSUBST σ G D) : TSSUBST σ.ext' ((τ :: Γ) :: Γs) ((τ :: Δ) :: Δs) :=
  match Hσ with
  | .single σ Hσ => by
    simp [SSUBST.ext']
    simp at HEQ2
    let ⟨EQ1, EQ2⟩ := HEQ2
    rw [EQ2]
    constructor
    apply TSUBST.ext_typing
    rw [HEQ1]
    rw [EQ1]
    apply Hσ
  | @TSSUBST.wk _ Γ' _ _ Ψ _ n _ HEQ Hσs Hσ => by
    simp [SSUBST.ext']
    have ⟨ψ, HEQ3⟩ : Σ' ψ, Ψ = ψ :: Ψ.drop 1 := by
      cases Ψ with
      | nil => exfalso; simp at HEQ; omega
      | cons ψ ψs => exists ψ
    rw [HEQ3] at HEQ1
    simp at HEQ1
    let ⟨G1, G2⟩ := HEQ1
    rw [G1, G2]
    have G3 : ((τ :: ψ) :: (List.tail Ψ ++ Γ')) = (τ :: ψ) :: List.tail Ψ ++ Γ' := by simp
    rw [G3]
    constructor
    . assumption
    . simp; omega
    . simp at HEQ2
      let ⟨J1, J2⟩ := HEQ2
      rw [J2]
      assumption
    . apply TSUBST.ext_typing
      simp
      rw [<-List.cons_append]
      simp at HEQ3
      rw [<-HEQ3]
      simp at HEQ2
      let ⟨J1, J2⟩ := HEQ2
      rw [J1]
      assumption

def TSSUBST.ext_typing (Hσ : TSSUBST σ (Γ :: Γs) (Δ :: Δs)) : TSSUBST σ.ext' ((τ :: Γ) :: Γs) ((τ :: Δ) :: Δs) := by
  generalize HEQ1 : (Γ :: Γs) = G
  generalize HEQ2 : (Δ :: Δs) = D
  rw [HEQ1, HEQ2] at Hσ
  apply TSSUBST.ext_typing' HEQ1 HEQ2 Hσ

@[simp]
def REN.local_n_weak (n : Nat) : REN :=
  match n with
  | .zero => REN.id
  | .succ n => .local_weaken (.local_n_weak n)

def TYPED_REN.local_n_weak : TYPED_REN (.local_n_weak Γ'.length) ((Γ' ++ Γ) :: Γs) (Γ :: Γs) :=
  match Γ' with
  | .nil => by simp; apply TYPED_REN.id; simp
  | .cons Δ Δs => by simp; apply TYPED_REN.local_weaken; apply TYPED_REN.local_n_weak

def REN.global_n_weak' (n m : Nat) : REN :=
  .global_shift n (.local_n_weak m)

def TYPED_REN.global_n_weak' (Ψ : OCTX.{i}) (Ψs : CTX.{i}) : TYPED_REN (.global_n_weak' Ψs.length Ψ.length) (Ψs ++ [Ψ]) [[]] := by
  unfold REN.global_n_weak'
  constructor
  . rfl
  . have T := TYPED_REN.local_n_weak (Γs := []) (Γ := []) (Γ' := Ψ)
    simp at T
    apply T

def TYPED_REN.global_n_weak'' (Ψ : OCTX.{i}) : TYPED_REN (.global_n_weak' 0 Ψ.length) ([] ++ [Ψ]) [[]] := by
  unfold REN.global_n_weak'
  constructor
  . rfl
  . have T := TYPED_REN.local_n_weak (Γs := []) (Γ := []) (Γ' := Ψ)
    simp at T
    apply T

@[simp]
def REN.global_n_weak (n : Nat) (m : Option Nat) : REN :=
  match m with
  | none => REN.global_n_weak' n 0
  | some m => REN.global_n_weak' (n - 1) m

def TYPED_REN.global_n_weak (Ψ : CTX.{i}) (HΨ : 0 < Ψ.length) : TYPED_REN (.global_n_weak Ψ.length (Ψ.getLast?.map List.length)) Ψ [[]] :=
  match Ψ with
  | .nil => by
    simp at HΨ
  | .cons x xs => by
    simp
    rw [List.getLast?_cons]
    simp
    generalize HEQ : x :: xs = L
    let ⟨y, ys, HEQ'⟩ : Σ' y ys, L = ys ++ [y] := by
      exists (List.getLast L (by rw [<-HEQ]; simp))
      exists (L.take (L.length - 1))
      rw [List.take_append_getLast]
    rw [HEQ']
    have Hlen : xs.length = ys.length := by
      rw [<-HEQ] at HEQ'
      clear HEQ
      have HEQ : (x :: xs).length = (ys ++ [y]).length := by
        rw [HEQ']
      clear HEQ'
      revert ys
      induction xs with
      | nil =>
        intros ys HEQ
        cases ys with
        | nil => rfl
        | cons => simp at HEQ
      | cons _ _ IH =>
        intros ys HEQ
        cases ys with
        | nil => simp at HEQ
        | cons =>
          simp at HEQ
          simp
          apply HEQ
    rw [Hlen]
    have HEQ'' : (List.length (xs.getLast?.getD x)) = y.length := by
      rw [<-HEQ] at HEQ'
      clear HEQ
      have EQ : (xs.getLast?.getD x) = y := by
        calc
          xs.getLast?.getD x = (x :: xs).getLast?.getD x := by
            rw [List.getLast?_cons]
            simp
          (x :: xs).getLast?.getD x = (ys ++ [y]).getLast?.getD x := by
            rw [HEQ']
          _ = y := by simp
      rw [EQ]
    rw [HEQ'']
    apply TYPED_REN.global_n_weak'

@[simp]
def subst_var (σ : SUBST.{i}) (n m : Nat) : EXPR.{i} :=
  match σ, n, m with
  | SUBST.epsilon, n, m => .var' n m
  | SUBST.cons e _σ, _, 0 => e
  | SUBST.cons _e σ, n, (m + 1) => subst_var σ n m

theorem subst_var_typing (Hσ : TSUBST σ Γ Δ) (m : Nat)
  τ (Hm : Δ[m]? = some τ) : TYPED Γ (subst_var σ 0 m) τ :=
  match Hσ with
  | .epsilon _ => by
    simp at Hm
  | .cons e σ => by
    cases m with
    | zero =>
      cases Hm
      simp [subst_var]; assumption
    | succ m =>
      simp [subst_var]
      apply subst_var_typing
      . assumption
      . apply Hm

@[simp]
def ssubst_var (σ : SSUBST) (n m : Nat) : EXPR :=
  match σ, n with
  | SSUBST.single σ, n => subst_var σ n m
  | SSUBST.wk _ _ σ, 0 => subst_var σ n m
  | SSUBST.wk p' σs _, (n + 1) => weaken (ssubst_var σs n m) (REN.global_shift p' REN.id)

theorem ssubst_var_typing (Hσ : TSSUBST σ Γ Δ) (n m : Nat)
  (Ψ : OCTX.{i}) τ
  (Hn : Δ[n]? = some Ψ) (Hm : Ψ[m]? = some τ) : TYPED Γ (ssubst_var σ n m) τ :=
  match Hσ with
  | .single σ Hσ => by
    simp [ssubst_var]
    cases n with
    | zero =>
      cases Hn
      apply subst_var_typing
      assumption
      assumption
    | succ n =>
      cases Hn
  | .wk p σs σ Hσs Hσ => by
    cases n with
    | zero =>
      simp at *
      cases Hn
      apply subst_var_typing
      assumption
      assumption
    | succ n =>
      simp at Hn
      simp [ssubst_var]
      let IH := ssubst_var_typing Hσs n m Ψ τ Hn Hm
      apply weaken_typing
      . apply IH
      . constructor
        . assumption
        . constructor
          apply ssubst_len
          apply Hσs

def binds (σ : SSUBST) (e : EXPR) : EXPR :=
  match σ, e with
  | σ, .delay e => .delay (binds (SSUBST.wk 1 σ .epsilon) e)
  | σ, .adv i e => .adv (offset_ssubst σ i) (binds (cut_ssubst σ i) e)
  | σ, .lam' τ e => .lam' τ (binds σ.ext' e)
  | σ, .app B e e' => .app B (binds σ e) (binds σ e')
  | _, .embed _ a => .embed _ a
  | σ, .embed_apply A B f x => .embed_apply A B (binds σ f) (binds σ x)
  | σ, .pure e => .pure (binds σ e)
  | σ, .fix' t e => .fix' t (binds σ.ext' e)
  | σ, .pair e e' => .pair (binds σ e) (binds σ e')
  | σ, .proj B e d => .proj B (binds σ e) d
  | σ, .inl B e => .inl B (binds σ e)
  | σ, .inr A e => .inr A (binds σ e)
  | σ, .case A B e f g => .case A B (binds σ e) (binds σ f) (binds σ g)
  | σ, .or e e' => .or (binds σ e) (binds σ e')
  | σ, .and e e' => .and (binds σ e) (binds σ e')
  | σ, .impl e e' => .impl (binds σ e) (binds σ e')
  | σ, .forall' τ e => .forall' τ (binds σ.ext' e)
  | σ, .exists' τ e => .exists' τ (binds σ.ext' e)
  | _, .true => .true
  | _, .false => .false
  | σ, .lift e => .lift (binds σ e)
  | σ, .eq B e e' => .eq B (binds σ e) (binds σ e')
  | σ, .var' n m => ssubst_var σ n m
  | _, .ax t f => .ax t f

@[simp]
theorem delay_subst : binds δ (.delay e) = .delay (binds (SSUBST.wk 1 δ .epsilon) e) := by rfl
@[simp]
theorem adv_subst : binds δ (.adv i e) = .adv (offset_ssubst δ i) (binds (cut_ssubst δ i) e) := by rfl
@[simp]
theorem app_subst : binds δ (.app B e1 e2) = .app B (binds δ e1) (binds δ e2) := by rfl
@[simp]
theorem embed_subst : binds δ (.embed A a) = .embed A a := by rfl
@[simp]
theorem embed_apply_subst : binds δ (.embed_apply A B f x) = .embed_apply A B (binds δ f) (binds δ x) := by rfl
@[simp]
theorem pure_subst : binds δ (.pure e) = .pure (binds δ e) := by rfl
@[simp]
theorem pair_subst : binds δ (.pair e1 e2) = .pair (binds δ e1) (binds δ e2) := by rfl
@[simp]
theorem proj_subst : binds δ (.proj B e d) = .proj B (binds δ e) d := by rfl
@[simp]
theorem inl_subst : binds δ (.inl B e) = .inl B (binds δ e) := by rfl
@[simp]
theorem inr_subst : binds δ (.inr A e) = .inr A (binds δ e) := by rfl
@[simp]
theorem case_subst : binds δ (.case A B e f g) = .case A B (binds δ e) (binds δ f) (binds δ g) := by rfl
@[simp]
theorem and_subst : binds δ (.and e1 e2) = .and (binds δ e1) (binds δ e2) := by rfl
@[simp]
theorem or_subst : binds δ (.or e1 e2) = .or (binds δ e1) (binds δ e2) := by rfl
@[simp]
theorem impl_subst : binds δ (.impl e1 e2) = .impl (binds δ e1) (binds δ e2) := by rfl
@[simp]
theorem true_subst : binds δ (.true) = .true := by rfl
@[simp]
theorem false_subst : binds δ (.false) = .false := by rfl
@[simp]
theorem lift_subst : binds δ (.lift e) = .lift (binds δ e) := by rfl
@[simp]
theorem eq_subst : binds δ (.eq B e1 e2) = .eq B (binds δ e1) (binds δ e2) := by rfl
@[simp]
theorem ax_subst : binds δ (.ax t f) = .ax t f := by rfl

@[simp]
theorem var_subst1 : binds (.single .epsilon) (.var nm i j) = (.var nm i j) := by rfl
@[simp]
theorem var_subst2 : binds (.single (.cons e σ)) (.var nm i 0) = e := by rfl
@[simp]
theorem var_subst3 : binds (.single (.cons e σ)) (.var nm i (j + 1)) = binds (.single σ) (.var nm i j) := by rfl
@[simp]
theorem var_subst4 : binds (.wk n σs σ) (.var nm 0 j) = binds (.single σ) (.var nm 0 j) := by rfl
@[simp]
theorem var_subst5 :
  binds (.wk n σs σ) (.var nm (i + 1) j) = weaken (binds σs (.var nm i j)) (REN.global_shift n REN.id)
  := by rfl
@[simp]
theorem var_subst6 :
  binds (SSUBST.ext σs nm') (.var nm 0 0) = (.var nm 0 0) := by
  induction σs with
  | single σ =>
    induction σ with
    | epsilon => rfl
    | cons e σ => rfl
  | wk n σs' σ => rfl
@[simp]
theorem var_subst7 :
  binds (.single (SUBST.ext σ nm')) (.var nm n 0) = (.var nm 0 0) := by
  rfl
@[simp]
theorem var_subst8 :
  binds (.single (SUBST.ext σ nm')) (.var nm n (j + 1)) = binds (.single σ.drop) (.var nm n j) := by
  rfl

@[simp]
theorem var_subst7' :
  binds (.single (SUBST.ext' σ)) (.var nm n 0) = (.var nm 0 0) := by
  rfl
@[simp]
theorem var_subst8' :
  binds (.single (SUBST.ext' σ)) (.var nm n (j + 1)) = binds (.single σ.drop) (.var nm n j) := by
  rfl

@[simp]
theorem var_subst9 :
  binds (.single (SUBST.sr_compose .epsilon δ)) (.var nm i j) = (.var nm i j) := by
  rfl
@[simp]
theorem var_subst10 :
  binds (.single (SUBST.sr_compose (.cons e σ) δ)) (.var nm i 0) = weaken e δ := by
  simp
@[simp]
theorem var_subst11 :
  binds (.single (SUBST.sr_compose (.cons e σ) δ)) (.var nm i (j + 1)) = binds (.single (SUBST.sr_compose σ δ)) (.var nm i j) := by
  simp
@[simp]
theorem var_subst12 :
  binds (SSUBST.sr_compose (.single σ) δ) (.var nm i j) = binds (.single (SUBST.sr_compose σ δ)) (.var nm i j) := by
  simp
@[simp]
theorem var_subst13 :
  binds (SSUBST.sr_compose (.wk p σs σ) δ) (.var nm i j) = binds (.wk (offset_ren δ p) (σs.sr_compose (cut_ren δ p)) (σ.sr_compose δ)) (.var nm i j) := by
  simp

@[simp]
theorem lam_subst : binds σ (.lam nm τ e) = .lam nm τ (binds (σ.ext nm) e) := by rfl

@[simp]
theorem forall_subst : binds σ (.forall nm τ e) = .forall nm τ (binds (σ.ext nm) e) := by rfl

@[simp]
theorem exists_subst : binds σ (.exists nm τ e) = .exists nm τ (binds (σ.ext nm) e) := by rfl

@[simp]
theorem fix_subst : binds σ (.fix nm t e) = .fix nm t (binds (σ.ext nm) e) := by rfl

theorem subst_typing {Γ : CTX.{i}} {e : EXPR.{i}} {τ : TYPE.{i}} (H : TYPED Γ e τ)
  (Hσ : TSSUBST σ Δ Γ) : TYPED Δ (binds σ e) τ :=
match H with
| .embed H => by
  constructor
  let _ := ssubst_len _ Hσ
  omega
| .embed_apply H1 H2 => by
  simp [binds]
  constructor
  . apply subst_typing <;> assumption
  . apply subst_typing <;> assumption
| .pure H => by
  simp [binds]
  constructor
  apply subst_typing <;> assumption
| @TYPED.var' Γ Δ τ p q Heq1 Heq2 => by
  apply ssubst_var_typing
  . assumption
  . assumption
  . assumption
| .app e1 e2 => by
  constructor
  . apply subst_typing <;> assumption
  . apply subst_typing <;> assumption
| @TYPED.lam' Δ' Ψ A B  _ e => by
  simp [binds]
  let T := ssubst_len _ Hσ
  let ⟨Φ, HEQ⟩ : Σ' Φ, Δ = (Φ :: Δ.drop 1) := by
    cases Δ with
    | nil => exfalso; simp at T
    | cons h t => exists h
  rw [HEQ]
  rw [HEQ] at Hσ
  constructor
  apply subst_typing
  . assumption
  . apply TSSUBST.ext_typing
    rw [<-HEQ]
    assumption
| @TYPED.delay Γ' e τ H1 H2 => by
  constructor
  . let _ := ssubst_len _ Hσ
    omega
  . apply subst_typing
    . assumption
    . have HEQ : [] :: Δ = [[]] ++ Δ := by simp
      rw [HEQ]
      constructor
      . simp
      . simp
      . assumption
      . constructor
        simp
| @TYPED.adv i Γ' _ t G e => by
  simp [binds]
  constructor
  . apply offset_ssubst_pos σ Hσ; assumption
  . apply subst_typing
    . assumption
    . apply cut_ssubst_typing
      . assumption
      . let T := typing_stack_len e
        simp at T
        omega
| .fix' e => by
  simp [binds]
  let T := ssubst_len _ Hσ
  let ⟨Φ, HEQ⟩ : Σ' Φ, Δ = (Φ :: Δ.drop 1) := by
    cases Δ with
    | nil => exfalso; simp at T
    | cons h t => exists h
  rw [HEQ]
  rw [HEQ] at Hσ
  constructor
  apply subst_typing
  . assumption
  . apply TSSUBST.ext_typing
    rw [<-HEQ]
    assumption
| .pair e1 e2 => by
  simp [binds]
  constructor
  . apply subst_typing <;> assumption
  . apply subst_typing <;> assumption
| .projL e => by
  simp [binds]
  constructor
  apply subst_typing <;> assumption
| .projR e => by
  simp [binds]
  constructor
  apply subst_typing <;> assumption
| .inl e => by
  simp [binds]
  constructor
  apply subst_typing <;> assumption
| .inr e => by
  simp [binds]
  constructor
  apply subst_typing <;> assumption
| .case e f g => by
  simp [binds]
  constructor
  · apply subst_typing <;> assumption
  · apply subst_typing <;> assumption
  · apply subst_typing <;> assumption
| .or e1 e2 => by
  simp [binds]
  constructor
  . apply subst_typing <;> assumption
  . apply subst_typing <;> assumption
| .and e1 e2 => by
  simp [binds]
  constructor
  . apply subst_typing <;> assumption
  . apply subst_typing <;> assumption
| .impl e1 e2 => by
  simp [binds]
  constructor
  . apply subst_typing <;> assumption
  . apply subst_typing <;> assumption
| @TYPED.forall' Δ' Ψ A _ e => by
  simp [binds]
  let T := ssubst_len _ Hσ
  let ⟨Φ, HEQ⟩ : Σ' Φ, Δ = (Φ :: Δ.drop 1) := by
    cases Δ with
    | nil => exfalso; simp at T
    | cons h t => exists h
  rw [HEQ]
  rw [HEQ] at Hσ
  constructor
  apply subst_typing
  . assumption
  . apply TSSUBST.ext_typing
    rw [<-HEQ]
    assumption
| @TYPED.exists' Δ' Ψ A _ e => by
  simp [binds]
  let T := ssubst_len _ Hσ
  let ⟨Φ, HEQ⟩ : Σ' Φ, Δ = (Φ :: Δ.drop 1) := by
    cases Δ with
    | nil => exfalso; simp at T
    | cons h t => exists h
  rw [HEQ]
  rw [HEQ] at Hσ
  constructor
  apply subst_typing
  . assumption
  . apply TSSUBST.ext_typing
    rw [<-HEQ]
    assumption
| .lift e => by
  simp [binds]
  constructor
  apply subst_typing <;> assumption
| .true H => by
  simp [binds]
  constructor
  let _ := ssubst_len _ Hσ
  omega
| .false H => by
  simp [binds]
  constructor
  let _ := ssubst_len _ Hσ
  omega
| .eq e1 e2 => by
  simp [binds]
  constructor
  . apply subst_typing <;> assumption
  . apply subst_typing <;> assumption
| .ax H1 H2 H => by
  simp [binds]
  constructor
  let _ := ssubst_len _ Hσ
  omega

def SUBST.apply_ssub (σ : SUBST) (σs : SSUBST) : SUBST :=
  match σ with
  | .epsilon => .epsilon
  | .cons e σ => .cons (binds σs e) (σ.apply_ssub σs)

def TSUBST.apply_ssub (Hσ : TSUBST σ Γ Δ) (Hσs : TSSUBST σs Ψ Γ) :
  TSUBST (σ.apply_ssub σs) Ψ Δ :=
  match Hσ with
  | .epsilon Hl => by
    simp [SUBST.apply_ssub]
    constructor
    apply ssubst_len
    assumption
  | .cons Ht Hσ => by
    simp [SUBST.apply_ssub]
    constructor
    . apply subst_typing
      . assumption
      . assumption
    . apply (TSUBST.apply_ssub Hσ Hσs)

def SSUBST.comp (σ σ' : SSUBST) : SSUBST :=
  match σ with
  | .single σ => .single (σ.apply_ssub σ')
  | .wk n σs σ => (.wk (offset_ssubst σ' n) (σs.comp (cut_ssubst σ' n)) (σ.apply_ssub σ'))

def TSSUBST.comp (Hσ : TSSUBST σ Δ Ψ) (Hσ' : TSSUBST σ' Γ Δ) : TSSUBST (σ.comp σ') Γ Ψ :=
  match Hσ with
  | .single Hl Hσ => TSSUBST.single _ (TSUBST.apply_ssub Hσ Hσ')
  | .wk n Hn Hneq Hσs Hσ => by
    simp [SSUBST.comp]
    have T0 := ssubst_len _ Hσs
    have T1 := cut_ssubst_typing _ Hσ' n (by simp; rw [Hneq]; omega)
    rw [Hneq] at T1
    simp at T1
    rw [<-Hneq] at T1
    have EQ0 : Γ = Γ.take (offset_ssubst σ' n) ++ Γ.drop (offset_ssubst σ' n) := by
      rw [List.take_append_drop]
    rw [EQ0]
    constructor
    . apply offset_ssubst_pos
      . assumption
      . assumption
    . simp
      have T2 := offset_ssubst_len _ Hσ' n (by simp; rw [Hneq]; omega)
      omega
    . apply TSSUBST.comp
      . assumption
      . assumption
    . rw [<-EQ0]
      apply TSUBST.apply_ssub
      . assumption
      . assumption

def REN.subst_of_ren (δ : REN) (Γ : List Nat) : SSUBST := SSUBST.sr_compose (SSUBST.id Γ) δ

def TYPED_REN.subst_of_ren (Hδ : TYPED_REN δ Γ Δ) : TSSUBST (δ.subst_of_ren (Δ.map List.length)) Γ Δ :=
  TSSUBST.sr_compose_typing (TSSUBST.id _ (ren_len _ Hδ)) Hδ

@[simp]
def SSUBST.cons (σ : SSUBST) (e : EXPR) : SSUBST :=
  match σ with
  | .single σ => .single (σ.cons e)
  | .wk n σs σ => .wk n σs (σ.cons e)

def TSSUBST.cons (Hσs : TSSUBST σs Γs (Δ :: Δs)) (He : TYPED Γs e τ) : TSSUBST (σs.cons e) Γs ((τ :: Δ) :: Δs) :=
  match Hσs with
  | single _ Hσ => TSSUBST.single _ (TSUBST.cons He Hσ)
  | wk n Hn Hneq Hσs Hσ => TSSUBST.wk n Hn Hneq Hσs (TSUBST.cons He Hσ)

def EXPR.quote.{i} (e : SYNT τ) (n : Nat) (m : Option Nat) : EXPR.{i} := weaken e.expr (.global_n_weak n m)
@[simp]
theorem quote_synt : EXPR.quote (SYNT.mk e prf) n m = weaken e (.global_n_weak n m) := by
  with_unfolding_all rfl
theorem TYPED.quote.{i} (Ψ : CTX.{i}) (H : 0 < Ψ.length) (e : SYNT τ) : TYPED Ψ (EXPR.quote e Ψ.length (Ψ.getLast?.map List.length)) τ := by
  simp [EXPR.quote]
  apply weaken_typing
  . apply e.proof
  . apply TYPED_REN.global_n_weak
    . assumption

end expr
end
