module

public import SynthDom.Syntax.Expr.Core
public import SynthDom.Interp.Tm

@[expose] public section

section prf

abbrev PROPOSITION.{i} := EXPR.{i}
abbrev POCTX.{i} := List PROPOSITION.{i}
abbrev PCTX.{i} := List POCTX.{i}

@[simp]
def SUBST.id' (Γ : List Lean.Name) : SUBST :=
  match Γ with
  | .nil => .epsilon
  | .cons n Γ => ext (SUBST.id' Γ) n

lemma SUBST.id_eq (Γ : List Lean.Name) : SUBST.id' Γ = SUBST.id Γ.length := by
  induction Γ with
  | nil => rfl
  | cons x xs IH =>
    simp [SUBST.id, SUBST.ext']
    constructor
    . simp [EXPR.var]
    . rw [IH]

@[simp]
def SSUBST.id' (Γ : List (List Lean.Name)) : SSUBST :=
  match Γ with
  | [] => .single .epsilon
  | Γ :: [] => .single (SUBST.id' Γ)
  | Γ :: Γs => wk 1 (SSUBST.id' Γs) (SUBST.id' Γ)

lemma SSUBST.id_eq (Γ : List (List Lean.Name)) : SSUBST.id' Γ = SSUBST.id (Γ.map List.length) := by
  induction Γ with
  | nil => rfl
  | cons x xs IH =>
    simp [List.map]
    cases xs with
    | nil =>
      simp
      rw [SUBST.id_eq]
    | cons y ys =>
      simp
      rw [SUBST.id_eq]
      constructor
      . rw [IH]
        rfl
      . rfl

@[simp]
def single_subst (Γ : List Nat) (e' : EXPR) := (SSUBST.cons (SSUBST.id Γ) e')
def TSSUBST.single_subst (H : TYPED (Γ :: Γs) e' τ) : TSSUBST (single_subst (List.map List.length (Γ :: Γs)) e') (Γ :: Γs) ((τ :: Γ) :: Γs) :=
  TSSUBST.cons (TSSUBST.id (Γ :: Γs) (by simp)) H
@[simp]
def octx_wk := REN.id.local_weaken

@[simp]
def wk_delay (Γ : Nat) (n : Nat) : REN :=
  local_weaken_list Γ (REN.global_lift (REN.global_shift n REN.id))
def TYPED_REN.wk_delay (Γ : CTX.{i}) (n : Nat) (Hlt' : n + 1 < Γ.length) (Hlt'' : 0 < Γ.length)
  : TYPED_REN (wk_delay (Γ[0]'Hlt'').length n) Γ ([] :: List.drop (n + 1) Γ) :=
  have eq : ((Γ[0] ++ []) :: (List.take n (List.tail Γ) ++ List.drop (n + 1) Γ)) = Γ := by
    cases Γ
    . exfalso; simp at Hlt'
    . simp
  ren_transport_left eq
    (local_weaken_list_typed (σ := REN.global_lift (REN.global_shift n REN.id))
      (Γ := []) (Γs := List.take n (List.tail Γ) ++ List.drop (n + 1) Γ)
      (Δ := []) (Δs := List.drop (n + 1) Γ) (Γ[0]'Hlt'')
      (TYPED_REN.global_lift (TYPED_REN.global_shift n (by simp; grind only)
      (TYPED_REN.id (by simp; grind only)))))

@[simp]
def intro_wrap' (Ψ : POCTX) : POCTX := Ψ.map (fun z => weaken z octx_wk)

@[simp]
def intro_wrap : PCTX → PCTX
  | [] => []
  | Ψ :: Ψs => intro_wrap' Ψ :: Ψs

inductive EQ : CTX.{i} → TYPE.{i} → EXPR.{i} → EXPR.{i} → Prop where
| rfl : TYPED Γ e τ → EQ Γ τ e e
| sym : TYPED Γ e2 τ → EQ Γ τ e1 e2 → EQ Γ τ e2 e1
| tran : EQ Γ τ e1 e2 → EQ Γ τ e2 e3 → EQ Γ τ e1 e3
| beta_lam' : TYPED (Γ :: Γs) e' τ → TYPED ((τ :: Γ) :: Γs) e σ
  → EQ (Γ :: Γs) σ (.app τ (.lam' τ e) e') (binds (single_subst (List.map List.length (Γ :: Γs)) e') e)
| eta_lam' : TYPED Γ e (TYPE.arr τ σ)
  → EQ Γ (TYPE.arr τ σ) e (.lam' τ (.app τ (weaken e (REN.local_weaken REN.id)) (.var' 0 0)))
| beta_delay (n : Nat) (Hlt : 0 < n) (Hlt' : n < Γ.length) : TYPED ([] :: List.drop n Γ) e τ
  → EQ Γ τ (.adv n (.delay e)) (weaken e (wk_delay (Γ[0]'(Nat.lt_trans Hlt Hlt')).length (n - 1)))
| eta_delay : TYPED Γ e (TYPE.later τ) → EQ Γ (TYPE.later τ) e (.delay (.adv 1 e))
| beta_embed_apply {A : Type (imax i 0)} {B : Type (imax i 0)} (f : A → B) (x : A)
  : 0 < Γ.length → EQ Γ (TYPE.embed B) (.embed_apply A B (.embed (A → B) f) (.embed A x)) (.embed B (f x))
| unfold' : TYPED ((TYPE.later τ :: Δ) :: Γ) e τ
  → EQ (Δ :: Γ) τ (.fix' (TYPE.later τ) e) (binds (single_subst (List.map List.length (Δ :: Γ)) (.delay (weaken (.fix' (TYPE.later τ) e) (REN.global_shift 1 REN.id)))) e)
| beta_prod_l : TYPED Γ e τ → TYPED Γ e' σ
  → EQ Γ τ (.proj σ (.pair e e') .L) e
| beta_prod_r : TYPED Γ e τ → TYPED Γ e' σ
  → EQ Γ σ (.proj τ (.pair e e') .R) e'
| eta_prod : TYPED Γ e (TYPE.prod τ σ)
  → EQ Γ (TYPE.prod τ σ) e (.pair (.proj σ e .L) (.proj τ e .R))
| beta_case_inl {A B C : TYPE.{i}} : TYPED Γ a A → TYPED Γ f (TYPE.arr A C) → TYPED Γ g (TYPE.arr B C)
  → EQ Γ C (.case A B (.inl B a) f g) (.app A f a)
| beta_case_inr {A B C : TYPE.{i}} : TYPED Γ b B → TYPED Γ f (TYPE.arr A C) → TYPED Γ g (TYPE.arr B C)
  → EQ Γ C (.case A B (.inr A b) f g) (.app B g b)
| cong_inl {A B : TYPE.{i}} : EQ Γ A e e' → EQ Γ (TYPE.sum A B) (.inl B e) (.inl B e')
| cong_inr {A B : TYPE.{i}} : EQ Γ B e e' → EQ Γ (TYPE.sum A B) (.inr A e) (.inr A e')
| cong_case {A B C : TYPE.{i}} : EQ Γ (TYPE.sum A B) e e' → EQ Γ (TYPE.arr A C) f f' → EQ Γ (TYPE.arr B C) g g'
  → EQ Γ C (.case A B e f g) (.case A B e' f' g')
| cong_app : EQ Γ (TYPE.arr B C) e e' → EQ Γ B e'' e''' → EQ Γ C (.app B e e'') (.app B e' e''')
| cong_embed_apply : EQ Γ (TYPE.embed (A → X)) e e'  → EQ Γ (TYPE.embed A) e'' e'''
  → EQ Γ (TYPE.embed X) (.embed_apply A X e e'') (.embed_apply A X e' e''')
| cong_pure : EQ Γ (TYPE.embed Prop) e e'  → EQ Γ TYPE.prop (.pure e) (.pure e')
| cong_lam' : EQ ((τ :: Δ) :: Γ) σ e e' → EQ (Δ :: Γ) (TYPE.arr τ σ) (.lam' τ e) (.lam' τ e')
| cong_delay : 0 < Γ.length → EQ ([] :: Γ) A e e' → EQ Γ (TYPE.later A) (.delay e) (.delay e')
| cong_adv n : EQ (List.drop n Γ) (TYPE.later A) e e' → 0 < n → EQ Γ A (.adv n e) (.adv n e')
| cong_fix' : EQ ((TYPE.later τ :: Δ) :: Γ) τ e e'
  → EQ (Δ :: Γ) τ (.fix' (TYPE.later τ) e) (.fix' (TYPE.later τ) e')
| cong_pair : EQ Γ τ e e' → EQ Γ σ e'' e''' → EQ Γ (TYPE.prod τ σ) (.pair e e'') (.pair e' e''')
| cong_or : EQ Γ TYPE.prop e e' → EQ Γ TYPE.prop e'' e''' → EQ Γ TYPE.prop (.or e e'') (.or e' e''')
| cong_and : EQ Γ TYPE.prop e e' → EQ Γ TYPE.prop e'' e''' → EQ Γ TYPE.prop (.and e e'') (.and e' e''')
| cong_impl : EQ Γ TYPE.prop e e' → EQ Γ TYPE.prop e'' e''' → EQ Γ TYPE.prop (.impl e e'') (.impl e' e''')
| cong_forall' : EQ ((τ :: Δ) :: Γ) TYPE.prop e e' → EQ (Δ :: Γ) TYPE.prop (.forall' τ e) (.forall' τ e')
| cong_exists' : EQ ((τ :: Δ) :: Γ) TYPE.prop e e' → EQ (Δ :: Γ) TYPE.prop (.exists' τ e) (.exists' τ e')
| cong_proj1 : EQ Γ (TYPE.prod A B) e e' → EQ Γ A (.proj B e .L) (.proj B e' .L)
| cong_proj2 : EQ Γ (TYPE.prod A B) e e' → EQ Γ B (.proj A e .R) (.proj A e' .R)
| cong_lift : EQ Γ (TYPE.later TYPE.prop) e e' → EQ Γ TYPE.prop (.lift e) (.lift e')
| cong_eq : EQ Γ B e e' → EQ Γ B e'' e''' → EQ Γ TYPE.prop (.eq B e e'') (.eq B e' e''')
| ax : TYPED Γ e τ → TYPED Γ e' τ → (expr_interp Γ e τ = expr_interp Γ e' τ) → EQ Γ τ e e'

lemma EQ.typed (H : EQ Γ τ e1 e2) : TYPED Γ e1 τ := by
  induction H <;> try (repeat (first | assumption | constructor))
  . grind only [= List.length_drop]
  . assumption

lemma EQ.typed' (H : EQ Γ τ e1 e2) : TYPED Γ e2 τ := by
  induction H <;> try (repeat (first | assumption | constructor))
  . apply EQ.typed; assumption
  . apply subst_typing
    . assumption
    . apply TSSUBST.single_subst
      . assumption
  . rename_i Γ e τ σ H
    have H' := typing_stack_len H
    cases Γ
    . simp at H'
    . constructor
      constructor
      . apply weaken_typing
        . assumption
        . constructor
          constructor
          assumption
      . constructor
        . simp; rfl
        . simp
  . apply weaken_typing
    . assumption
    . rename_i Γ e τ n Hlt Hlt' H
      have G := TYPED_REN.wk_delay Γ (n - 1) (by grind only) (by grind only)
      have eq : n - 1 + 1 = n := by grind only
      rw [eq] at G; clear eq
      apply G
  . apply typing_stack_len; assumption
  . constructor
    . simp
    . simp
      assumption
  . apply subst_typing
    . assumption
    . apply TSSUBST.single_subst
      constructor
      . rename_i H
        have H' := typing_stack_len H
        apply H'
      . apply weaken_typing
        . constructor
          assumption
        . rename_i τ Δ Γ e H
          apply TYPED_REN.global_shift (Ψ := [[]]) (Γ := Δ :: Γ) (Δ := Δ :: Γ) (σ := REN.id) 1 (by simp)
          constructor
          simp

lemma EQ.subst_l (H : EQ Γ τ e1 e2) (eq : e1 = e1') : EQ Γ τ e1' e2 := by
  rw [←eq]
  assumption

lemma EQ.subst_r (H : EQ Γ τ e1 e2) (eq : e2 = e2') : EQ Γ τ e1 e2' := by
  rw [←eq]
  assumption

lemma EQ.sym' (H : EQ Γ τ e1 e2) : EQ Γ τ e2 e1 := by
  apply EQ.sym
  . apply EQ.typed'; assumption
  . assumption

unseal EXPR.lam in
theorem EQ.beta_lam : TYPED (Γ :: Γs) e' τ → TYPED ((τ :: Γ) :: Γs) e σ →
  EQ (Γ :: Γs) σ (.app τ (.lam nm τ e) e') (binds (single_subst (List.map List.length (Γ :: Γs)) e') e) := EQ.beta_lam'
unseal EXPR.lam in unseal EXPR.var in
theorem EQ.eta_lam : TYPED Γ e (TYPE.arr τ σ)
  → EQ Γ (TYPE.arr τ σ) e (.lam nm τ (.app τ (weaken e (REN.local_weaken REN.id)) (.var `x 0 0))) := EQ.eta_lam'
unseal EXPR.lam in
theorem EQ.cong_lam : EQ ((τ :: Δ) :: Γ) σ e e'
  → EQ (Δ :: Γ) (TYPE.arr τ σ) (.lam nm τ e) (.lam nm τ e') := EQ.cong_lam'
unseal EXPR.fix in
theorem EQ.cong_fix : EQ ((TYPE.later τ :: Δ) :: Γ) τ e e'
  → EQ (Δ :: Γ) τ (.fix nm (TYPE.later τ) e) (.fix nm (TYPE.later τ) e') := EQ.cong_fix'
unseal EXPR.forall in
theorem EQ.cong_forall : EQ ((τ :: Δ) :: Γ) TYPE.prop e e'
  → EQ (Δ :: Γ) TYPE.prop (.forall nm τ e) (.forall nm τ e') := EQ.cong_forall'
unseal EXPR.exists in
theorem EQ.cong_exists : EQ ((τ :: Δ) :: Γ) TYPE.prop e e'
  → EQ (Δ :: Γ) TYPE.prop (.exists nm τ e) (.exists nm τ e') := EQ.cong_exists'
unseal EXPR.fix in
theorem EQ.unfold : TYPED ((TYPE.later τ :: Δ) :: Γ) e τ
  → EQ (Δ :: Γ) τ (.fix nm (TYPE.later τ) e) (binds (single_subst (List.map List.length (Δ :: Γ)) (.delay (weaken (.fix nm (TYPE.later τ) e) (REN.global_shift 1 REN.id)))) e) := EQ.unfold'

macro "prf_side" : tactic =>
  `(tactic| first
    | assumption
    | rfl
    | omega
    | (simp_all only [List.length_cons, List.length_nil, List.length_map,
        List.length_append, List.length_drop, List.length_take, List.length_set]; done)
    | (simp_all only [List.length_cons, List.length_nil, List.length_map,
        List.length_append, List.length_drop, List.length_take, List.length_set]; omega)
    | decide)

def weaken_pctx (σ : REN) (Ψ : PCTX.{i}) : PCTX.{i} :=
  Ψ.mapIdx (fun n Ψn => Ψn.map (fun p => weaken p (cut_ren σ n)))

inductive PROVES : CTX.{i} → PCTX.{i} → PROPOSITION.{i} → Prop where
| asm (n m : Nat) : Ψ[n]? = some Ψ' → Ψ'[m]? = some Φ →
    (Htyped : TYPED Γ (weaken Φ (REN.global_shift n REN.id)) TYPE.prop := by prf_side) →
    (Hlen : Γ.length = Ψ.length := by prf_side) →
    PROVES Γ Ψ (weaken Φ (REN.global_shift n REN.id))
| true_intro :
    (Hpos : 0 < Γ.length := by prf_side) →
    (Hlen : Γ.length = Ψ.length := by prf_side) →
    PROVES Γ Ψ EXPR.true
| and_intro : PROVES Γ Ψ Φ1 → PROVES Γ Ψ Φ2 → PROVES Γ Ψ (.and Φ1 Φ2)
| and_elim_l : PROVES Γ Ψ (.and Φ1 Φ2) → PROVES Γ Ψ Φ1
| and_elim_r : PROVES Γ Ψ (.and Φ1 Φ2) → PROVES Γ Ψ Φ2
| or_intro_l : (Htyped : TYPED Γ Φ2 TYPE.prop := by prf_side) → PROVES Γ Ψ Φ1 → PROVES Γ Ψ (.or Φ1 Φ2)
| or_intro_r : (Htyped : TYPED Γ Φ1 TYPE.prop := by prf_side) → PROVES Γ Ψ Φ2 → PROVES Γ Ψ (.or Φ1 Φ2)
| or_elim : PROVES Γ ((P :: Ψ) :: Ψs) Φ → PROVES Γ ((Q :: Ψ) :: Ψs) Φ → PROVES Γ (Ψ :: Ψs) (.or P Q) → PROVES Γ (Ψ :: Ψs) Φ
| impl_intro : (Htyped : TYPED Γ Φ1 TYPE.prop := by prf_side) → PROVES Γ ((Φ1 :: Ψ) :: Ψs) Φ2 → PROVES Γ (Ψ :: Ψs) (.impl Φ1 Φ2)
| impl_elim : PROVES Γ Ψ (.impl Φ1 Φ2) → PROVES Γ Ψ Φ1 → PROVES Γ Ψ Φ2
| forall_intro' : PROVES ((τ :: Γ) :: Γs) (intro_wrap Ψ) Φ → PROVES (Γ :: Γs) Ψ (.forall' τ Φ)
| forall_elim' τ Φ e : TYPED ((τ :: Γ) :: Γs) Φ TYPE.prop → PROVES (Γ :: Γs) Ψ (.forall' τ Φ) → TYPED (Γ :: Γs) e τ → PROVES (Γ :: Γs) Ψ (binds (single_subst (List.map List.length (Γ :: Γs)) e) Φ)
| lift_intro : (Hpos : 0 < Γ.length := by prf_side) → PROVES ([] :: Γ) ([] :: Ψ) Φ → PROVES Γ Ψ (.lift (.delay Φ))
| later_mono : (Hpos : 0 < Γ.length := by prf_side) → PROVES Γ Ψ (.lift (.delay P)) → PROVES ([] :: Γ) ([P] :: Ψ) Q → PROVES Γ Ψ (.lift (.delay Q))

| later_and : PROVES Γ Ψ (.lift (.delay P)) → PROVES Γ Ψ (.lift (.delay Q)) → PROVES Γ Ψ (.lift (.delay (.and P Q)))

| later_or : PROVES Γ Ψ (.lift (.delay (.or P Q))) → PROVES Γ Ψ (.or (.lift (.delay P)) (.lift (.delay Q)))
| loeb_ind : PROVES Γ ((.lift (.delay (weaken Φ (REN.global_shift 1 REN.id))) :: Ψs) :: Φs) Φ → PROVES Γ (Ψs :: Φs) Φ
| eq_def : EQ Γ τ e1 e2 → (Hlen : Γ.length = Ψ.length := by prf_side) → PROVES Γ Ψ (.eq τ e1 e2)
| eq_elim : TYPED ((B :: Γ) :: Γs) Φ TYPE.prop → TYPED (Γ :: Γs) e1 B → TYPED (Γ :: Γs) e2 B → PROVES (Γ :: Γs) Ψ (.eq B e1 e2) → PROVES (Γ :: Γs) Ψ (binds (single_subst (List.map List.length (Γ :: Γs)) e1) Φ) → PROVES (Γ :: Γs) Ψ (binds (single_subst (List.map List.length (Γ :: Γs)) e2) Φ)
| false_elim P : (Htyped : TYPED Γ P TYPE.prop := by prf_side) → PROVES Γ Ψ EXPR.false → PROVES Γ Ψ P
| pure_intro : P →
    (Htyped : TYPED Γ (.pure (.embed Prop P)) TYPE.prop := by prf_side) →
    (Hlen : Γ.length = Ψ.length := by prf_side) →
    PROVES Γ Ψ (.pure (.embed Prop P))

| delay_eq : PROVES Γ Ψ (.lift (.delay (.eq A e1 e2))) →
    PROVES Γ Ψ (.eq (TYPE.later A) (.delay e1) (.delay e2))

| exists_intro' τ Φ e : TYPED ((τ :: Γ) :: Γs) Φ TYPE.prop → TYPED (Γ :: Γs) e τ →
    PROVES (Γ :: Γs) Ψ (binds (single_subst (List.map List.length (Γ :: Γs)) e) Φ) →
    PROVES (Γ :: Γs) Ψ (.exists' τ Φ)

| exists_elim' {τ : TYPE} {Φ Q : PROPOSITION} :
    TYPED (Γ :: Γs) Q TYPE.prop →
    PROVES (Γ :: Γs) (Ψ :: Ψs) (.exists' τ Φ) →
    PROVES ((τ :: Γ) :: Γs) ((Φ :: intro_wrap' Ψ) :: Ψs) (weaken Q octx_wk) →
    PROVES (Γ :: Γs) (Ψ :: Ψs) Q
| sum_elim {A B : TYPE} {Φ : PROPOSITION} (e : EXPR) :
    TYPED (Γ :: Γs) Φ TYPE.prop →
    TYPED (Γ :: Γs) e (TYPE.sum A B) →
    PROVES ((A :: Γ) :: Γs)
      ((.eq (TYPE.sum A B) (weaken e octx_wk) (.inl B (.var' 0 0)) :: intro_wrap' Ψ) :: Ψs)
      (weaken Φ octx_wk) →
    PROVES ((B :: Γ) :: Γs)
      ((.eq (TYPE.sum A B) (weaken e octx_wk) (.inr A (.var' 0 0)) :: intro_wrap' Ψ) :: Ψs)
      (weaken Φ octx_wk) →
    PROVES (Γ :: Γs) (Ψ :: Ψs) Φ

| forall_intro_points (A : Type (imax i 0)) (Φ : PROPOSITION.{i}) :
    TYPED ((TYPE.embed A :: Γ) :: Γs) Φ TYPE.prop →
    ((Γ :: Γs).length = Ψ.length) →
    (∀ a : A, PROVES (Γ :: Γs) Ψ
      (binds (single_subst (List.map List.length (Γ :: Γs)) (EXPR.embed A a)) Φ)) →
    PROVES (Γ :: Γs) Ψ (.forall' (TYPE.embed A) Φ)

| inl_inj : PROVES Γ Ψ (.eq (TYPE.sum A B) (.inl B a) (.inl B a')) →
    PROVES Γ Ψ (.eq A a a')
| inr_inj : PROVES Γ Ψ (.eq (TYPE.sum A B) (.inr A b) (.inr A b')) →
    PROVES Γ Ψ (.eq B b b')
| inl_inr_disj : PROVES Γ Ψ (.eq (TYPE.sum A B) (.inl B a) (.inr A b)) →
    PROVES Γ Ψ EXPR.false

@[simp] theorem intro_wrap_length (Ψ : PCTX) : (intro_wrap Ψ).length = Ψ.length := by
  cases Ψ <;> simp [intro_wrap]

theorem PROVES.len (H : PROVES Γ Ψ Φ) : Γ.length = Ψ.length := by
  induction H with
  | forall_intro' h IH =>
      simp only [intro_wrap_length, List.length_cons] at IH ⊢; omega
  | forall_intro_points A Φ HΦ Hlen Hfam IH => exact Hlen
  | _ => simp_all

theorem PROVES.typed (H : PROVES Γ Ψ Φ) : TYPED Γ Φ TYPE.prop := by
  induction H with
  | asm n m Hn Hm Htyped Hlen => exact Htyped
  | true_intro Hpos Hlen => constructor; exact Hpos
  | and_intro _ _ IH1 IH2 => constructor <;> assumption
  | and_elim_l _ IH => cases IH with | and H1 H2 => exact H1
  | and_elim_r _ IH => cases IH with | and H1 H2 => exact H2
  | or_intro_l HΦ2 _ IH => constructor <;> [exact IH; exact HΦ2]
  | or_intro_r HΦ1 _ IH => constructor <;> [exact HΦ1; exact IH]
  | or_elim _ _ _ IH1 _ _ => assumption
  | impl_intro HΦ1 _ IH => constructor <;> [exact HΦ1; exact IH]
  | impl_elim _ _ IH1 _ => cases IH1 with | impl H1 H2 => exact H2
  | forall_intro' _ IH => constructor; assumption
  | forall_elim' τ Φ e HΦ Hforall He IH =>
      exact subst_typing HΦ (TSSUBST.single_subst He)
  | lift_intro Hpos _ IH => exact TYPED.lift (TYPED.delay Hpos IH)
  | later_mono Hpos _ _ _ IH2 => exact TYPED.lift (TYPED.delay Hpos IH2)
  | later_and _ _ IH1 IH2 =>
      obtain ⟨_, hd1⟩ := TYPED.lift_inversion IH1
      obtain ⟨_, hd2⟩ := TYPED.lift_inversion IH2
      cases hd1 with
      | delay hpos hbody1 =>
        cases hd2 with
        | delay _ hbody2 =>
          exact TYPED.lift (TYPED.delay hpos (TYPED.and hbody1 hbody2))
  | later_or _ IH =>
      obtain ⟨_, hd⟩ := TYPED.lift_inversion IH
      cases hd with
      | delay hpos hbody =>
        obtain ⟨_, h1, h2⟩ := TYPED.or_inversion hbody
        exact TYPED.or (TYPED.lift (TYPED.delay hpos h1)) (TYPED.lift (TYPED.delay hpos h2))
  | loeb_ind _ IH => assumption
  | eq_def Heq Hlen => exact TYPED.eq (EQ.typed Heq) (EQ.typed' Heq)
  | eq_elim HΦ He1 He2 Heq Hb1 IH1 IH2 =>
      exact subst_typing HΦ (TSSUBST.single_subst He2)
  | false_elim P HP _ IH => exact HP
  | pure_intro Hprop Htyped Hlen => exact Htyped
  | delay_eq H IH =>
      obtain ⟨_, hd⟩ := TYPED.lift_inversion IH
      cases hd with
      | delay hpos hbody =>
        obtain ⟨_, he1, he2⟩ := TYPED.eq_inversion hbody
        exact TYPED.eq (TYPED.delay hpos he1) (TYPED.delay hpos he2)
  | exists_intro' τ Φ e HΦ He Hb IH => exact TYPED.exists' HΦ
  | forall_intro_points A Φ HΦ Hlen Hfam IH => exact TYPED.forall' HΦ
  | exists_elim' HQ Hex Hbr IH1 IH2 => exact HQ
  | sum_elim e HΦ He Hinl Hinr IHinl IHinr => exact HΦ
  | inl_inj H IH =>
      obtain ⟨_, h1, h2⟩ := TYPED.eq_inversion IH
      rcases TYPED.inl_inversion h1 with ⟨A1, hτ1, ha⟩
      rcases TYPED.inl_inversion h2 with ⟨A2, hτ2, ha'⟩
      injection hτ1 with e11 _; injection hτ2 with e21 _
      exact TYPED.eq (e11 ▸ ha) (e21 ▸ ha')
  | inr_inj H IH =>
      obtain ⟨_, h1, h2⟩ := TYPED.eq_inversion IH
      rcases TYPED.inr_inversion h1 with ⟨B1, hτ1, hb⟩
      rcases TYPED.inr_inversion h2 with ⟨B2, hτ2, hb'⟩
      injection hτ1 with _ e12; injection hτ2 with _ e22
      exact TYPED.eq (e12 ▸ hb) (e22 ▸ hb')
  | inl_inr_disj H IH => exact TYPED.false (typing_stack_len IH)

end prf
