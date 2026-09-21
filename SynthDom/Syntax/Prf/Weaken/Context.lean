module

public import SynthDom.Syntax.Prf.Weaken.Proof

@[expose] public section

section prf
open Lean

def pctx_ins (Ψ : PCTX.{i}) (k m : Nat) (P : EXPR.{i}) : PCTX.{i} :=
  Ψ.modify k (fun fr => fr.insertIdx m P)

@[simp] theorem pctx_ins_nil (k m : Nat) (P : EXPR.{i}) :
    pctx_ins ([] : PCTX.{i}) k m P = [] := by
  simp [pctx_ins]

@[simp] theorem pctx_ins_zero (Ψ0 : POCTX.{i}) (Ψs : PCTX.{i}) (m : Nat) (P : EXPR.{i}) :
    pctx_ins (Ψ0 :: Ψs) 0 m P = (Ψ0.insertIdx m P) :: Ψs := by
  simp [pctx_ins]

@[simp] theorem pctx_ins_succ (Ψ0 : POCTX.{i}) (Ψs : PCTX.{i}) (k m : Nat) (P : EXPR.{i}) :
    pctx_ins (Ψ0 :: Ψs) (k + 1) m P = Ψ0 :: pctx_ins Ψs k m P := by
  simp [pctx_ins]

@[simp] theorem pctx_ins_length (Ψ : PCTX.{i}) (k m : Nat) (P : EXPR.{i}) :
    (pctx_ins Ψ k m P).length = Ψ.length := by
  simp [pctx_ins]

theorem pctx_ins_getElem?_self {Ψ : PCTX.{i}} {k : Nat} {Ψ' : POCTX.{i}}
    (h : Ψ[k]? = some Ψ') (m : Nat) (P : EXPR.{i}) :
    (pctx_ins Ψ k m P)[k]? = some (Ψ'.insertIdx m P) := by
  simp [pctx_ins, h]

theorem pctx_ins_getElem?_ne {Ψ : PCTX.{i}} {n k : Nat} (hnk : n ≠ k) (m : Nat)
    (P : EXPR.{i}) : (pctx_ins Ψ k m P)[n]? = Ψ[n]? := by
  simp only [pctx_ins, List.getElem?_modify]
  cases Ψ[n]? with
  | none => rfl
  | some fr => simp [if_neg (Ne.symm hnk)]

theorem pctx_ins_zero_intro_wrap (Ψ : PCTX.{i}) (m : Nat) (P : EXPR.{i}) :
    pctx_ins (intro_wrap Ψ) 0 m (weaken P octx_wk) = intro_wrap (pctx_ins Ψ 0 m P) := by
  cases Ψ with
  | nil => rfl
  | cons a as =>
    simp only [intro_wrap, pctx_ins_zero, intro_wrap', List.map_insertIdx]

theorem PROVES.assum_insert_at {Γ : CTX.{i}} {Ψ : PCTX.{i}} {Φ : EXPR.{i}}
    (H : PROVES Γ Ψ Φ) :
    ∀ (k m : Nat) (Pin : EXPR.{i}), PROVES Γ (pctx_ins Ψ k m Pin) Φ := by
  induction H with
  | @asm Ψ Ψ' Φ Γ n m' Hn Hm Htyped Hlen =>
    intro k m Pin
    by_cases hnk : n = k
    · subst hnk
      by_cases hml : Ψ'.length < m
      ·
        refine PROVES.asm n m' ?_ Hm (Htyped := Htyped)
          (Hlen := by rw [pctx_ins_length]; exact Hlen)
        rw [pctx_ins_getElem?_self Hn m Pin, List.insertIdx_of_length_lt hml]
      · by_cases hmm : m' < m
        · refine PROVES.asm n m' (pctx_ins_getElem?_self Hn m Pin) ?_ (Htyped := Htyped)
            (Hlen := by rw [pctx_ins_length]; exact Hlen)
          rw [List.getElem?_insertIdx_of_lt hmm]; exact Hm
        ·
          refine PROVES.asm n (m' + 1) (pctx_ins_getElem?_self Hn m Pin) ?_ (Htyped := Htyped)
            (Hlen := by rw [pctx_ins_length]; exact Hlen)
          rw [List.getElem?_insertIdx]
          simp only [if_neg (by omega : ¬ (m' + 1 < m)), if_neg (by omega : ¬ (m' + 1 = m))]
          simpa using Hm
    · exact PROVES.asm n m' (by rw [pctx_ins_getElem?_ne hnk]; exact Hn) Hm
        (Htyped := Htyped) (Hlen := by rw [pctx_ins_length]; exact Hlen)
  | true_intro Hpos Hlen =>
    intro k m Pin
    exact PROVES.true_intro (Hpos := Hpos) (Hlen := by rw [pctx_ins_length]; exact Hlen)
  | and_intro _ _ IH1 IH2 => intro k m Pin; exact PROVES.and_intro (IH1 k m Pin) (IH2 k m Pin)
  | and_elim_l _ IH => intro k m Pin; exact PROVES.and_elim_l (IH k m Pin)
  | and_elim_r _ IH => intro k m Pin; exact PROVES.and_elim_r (IH k m Pin)
  | or_intro_l Htyped _ IH => intro k m Pin; exact PROVES.or_intro_l (Htyped := Htyped) (IH k m Pin)
  | or_intro_r Htyped _ IH => intro k m Pin; exact PROVES.or_intro_r (Htyped := Htyped) (IH k m Pin)
  | @or_elim Γ Pl Ψf Ψs Q Φ _ _ _ IH1 IH2 IH3 =>
    intro k m Pin
    cases k with
    | zero =>
      have h1 := IH1 0 (m + 1) Pin
      have h2 := IH2 0 (m + 1) Pin
      have h3 := IH3 0 m Pin
      simp only [pctx_ins_zero, List.insertIdx_succ_cons] at h1 h2 ⊢
      exact PROVES.or_elim h1 h2 h3
    | succ k' =>
      have h1 := IH1 (k' + 1) m Pin
      have h2 := IH2 (k' + 1) m Pin
      have h3 := IH3 (k' + 1) m Pin
      simp only [pctx_ins_succ] at h1 h2 ⊢
      exact PROVES.or_elim h1 h2 h3
  | @impl_intro Γ Φ1 Ψf Ψs Φ2 Htyped _ IH =>
    intro k m Pin
    cases k with
    | zero =>
      have h := IH 0 (m + 1) Pin
      simp only [pctx_ins_zero, List.insertIdx_succ_cons] at h ⊢
      exact PROVES.impl_intro (Htyped := Htyped) h
    | succ k' =>
      have h := IH (k' + 1) m Pin
      simp only [pctx_ins_succ] at h ⊢
      exact PROVES.impl_intro (Htyped := Htyped) h
  | impl_elim _ _ IH1 IH2 => intro k m Pin; exact PROVES.impl_elim (IH1 k m Pin) (IH2 k m Pin)
  | @forall_intro' τ Γ Γs Ψf Φ _ IH =>
    intro k m Pin
    cases k with
    | zero =>
      have h := IH 0 m (_root_.weaken Pin octx_wk)
      rw [pctx_ins_zero_intro_wrap] at h
      exact PROVES.forall_intro' h
    | succ k' =>
      have h := IH (k' + 1) m Pin
      cases Ψf with
      | nil => simp only [intro_wrap, pctx_ins_nil] at h ⊢; exact PROVES.forall_intro' h
      | cons b bs =>
        simp only [intro_wrap, intro_wrap', pctx_ins_succ] at h ⊢
        exact PROVES.forall_intro' h
  | @forall_elim' Γ Γs Ψf τ Φ e HΦ H He IH =>
    intro k m Pin
    exact PROVES.forall_elim' τ Φ e HΦ (IH k m Pin) He
  | @lift_intro Γ Ψf Φ Hpos _ IH =>
    intro k m Pin
    have h := IH (k + 1) m Pin
    simp only [pctx_ins_succ] at h
    exact PROVES.lift_intro (Hpos := Hpos) h
  | @later_mono Γ Ψf P Q Hpos H1 H2 IH1 IH2 =>
    intro k m Pin
    have h1 := IH1 k m Pin
    have h2 := IH2 (k + 1) m Pin
    simp only [pctx_ins_succ] at h2
    exact PROVES.later_mono (Hpos := Hpos) h1 h2
  | later_and _ _ IH1 IH2 => intro k m Pin; exact PROVES.later_and (IH1 k m Pin) (IH2 k m Pin)
  | later_or _ IH => intro k m Pin; exact PROVES.later_or (IH k m Pin)
  | @loeb_ind Γ Φ Ψs Φs _ IH =>
    intro k m Pin
    cases k with
    | zero =>
      have h := IH 0 (m + 1) Pin
      simp only [pctx_ins_zero, List.insertIdx_succ_cons] at h ⊢
      exact PROVES.loeb_ind h
    | succ k' =>
      have h := IH (k' + 1) m Pin
      simp only [pctx_ins_succ] at h ⊢
      exact PROVES.loeb_ind h
  | @eq_def Γ τ e1 e2 Ψf Heq Hlen =>
    intro k m Pin
    exact PROVES.eq_def Heq (Hlen := by rw [pctx_ins_length]; exact Hlen)
  | eq_elim HΦ He1 He2 Heq _ IH1 IH2 =>
    intro k m Pin
    exact PROVES.eq_elim HΦ He1 He2 (IH1 k m Pin) (IH2 k m Pin)
  | false_elim P Htyped _ IH =>
    intro k m Pin; exact PROVES.false_elim _ (Htyped := Htyped) (IH k m Pin)
  | delay_eq H IH => intro k m Pin; exact PROVES.delay_eq (IH k m Pin)
  | inl_inj H IH => intro k m Pin; exact PROVES.inl_inj (IH k m Pin)
  | inr_inj H IH => intro k m Pin; exact PROVES.inr_inj (IH k m Pin)
  | inl_inr_disj H IH => intro k m Pin; exact PROVES.inl_inr_disj (IH k m Pin)
  | @exists_intro' Γ Γs Ψf τ Φ e HΦ He H IH =>
    intro k m Pin
    exact PROVES.exists_intro' τ Φ e HΦ He (IH k m Pin)
  | @forall_intro_points Γ Γs Ψf A Φ HΦ Hlen Hfam IH =>
    intro k m Pin
    exact PROVES.forall_intro_points A Φ HΦ
      (by rw [pctx_ins_length]; exact Hlen) (fun a => IH a k m Pin)
  | @exists_elim' Γ Γs Ψf Ψs τ Φ Q HQ Hex Hbr IH1 IH2 =>
    intro k m Pin
    cases k with
    | zero =>
      have h1 := IH1 0 m Pin
      have h2 := IH2 0 (m + 1) (_root_.weaken Pin octx_wk)
      simp only [pctx_ins_zero, List.insertIdx_succ_cons, intro_wrap',
        ← List.map_insertIdx] at h1 h2 ⊢
      exact PROVES.exists_elim' HQ h1 h2
    | succ k' =>
      have h1 := IH1 (k' + 1) m Pin
      have h2 := IH2 (k' + 1) m Pin
      simp only [pctx_ins_succ] at h1 h2 ⊢
      exact PROVES.exists_elim' HQ h1 h2
  | @sum_elim Γ Γs Ψ Ψs A B Φ e HΦ He _ _ IHinl IHinr =>
    intro k m Pin
    cases k with
    | zero =>
      have h1 := IHinl 0 (m + 1) (_root_.weaken Pin octx_wk)
      have h2 := IHinr 0 (m + 1) (_root_.weaken Pin octx_wk)
      simp only [pctx_ins_zero, List.insertIdx_succ_cons, intro_wrap',
        ← List.map_insertIdx] at h1 h2 ⊢
      exact PROVES.sum_elim e HΦ He h1 h2
    | succ k' =>
      have h1 := IHinl (k' + 1) m Pin
      have h2 := IHinr (k' + 1) m Pin
      simp only [pctx_ins_succ] at h1 h2 ⊢
      exact PROVES.sum_elim e HΦ He h1 h2
  | @pure_intro Pr Γ Ψf p Htyped Hlen =>
    intro k m Pin
    exact PROVES.pure_intro p (Htyped := Htyped)
      (Hlen := by rw [pctx_ins_length]; exact Hlen)

theorem PROVES.assum_mono {Γ : CTX.{i}} {Ψa : POCTX.{i}} {Γs : PCTX.{i}} {Φ : EXPR.{i}}
    (H : PROVES Γ (Ψa :: Γs) Φ) (Ψ0 : POCTX.{i}) : PROVES Γ ((Ψa ++ Ψ0) :: Γs) Φ := by
  induction Ψ0 generalizing Ψa with
  | nil => simpa using H
  | cons P Ψ0 IH =>
    have h := PROVES.assum_insert_at H 0 Ψa.length P
    have h' : PROVES Γ ((Ψa ++ [P]) :: Γs) Φ := by
      simpa using h
    simpa [List.append_assoc] using IH h' (Ψa := Ψa ++ [P])

theorem intro_wrap_append {Ψ Ψ' : PCTX.{i}} (h : Ψ ≠ []) :
    intro_wrap (Ψ ++ Ψ') = intro_wrap Ψ ++ Ψ' := by
  cases Ψ with
  | nil => exact absurd rfl h
  | cons Ψ0 Ψs => rfl

theorem PROVES.ctx_pad {Γ : CTX.{i}} {Ψ : PCTX.{i}} {Φ : EXPR.{i}} (H : PROVES Γ Ψ Φ) :
    ∀ (Δ : CTX.{i}) (Ψ' : PCTX.{i}), Δ.length = Ψ'.length → PROVES (Γ ++ Δ) (Ψ ++ Ψ') Φ := by
  induction H with
  | @asm Ψ Ψ0 Φ0 Γ0 n m Hn Hm Htyped Hlen =>
    intro Δ Ψ' hΔ
    have hn : n < Ψ.length := by
      rcases Nat.lt_or_ge n Ψ.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at Hn; simp at Hn
    exact PROVES.asm n m (by rw [List.getElem?_append_left hn]; exact Hn) Hm
      (Htyped := Htyped.ctx_pad Δ) (Hlen := by simp [Hlen, hΔ])
  | true_intro Hpos Hlen =>
    intro Δ Ψ' hΔ
    exact PROVES.true_intro (Hpos := by simp; omega) (Hlen := by simp [Hlen, hΔ])
  | and_intro _ _ IH1 IH2 => intro Δ Ψ' hΔ; exact PROVES.and_intro (IH1 Δ Ψ' hΔ) (IH2 Δ Ψ' hΔ)
  | and_elim_l _ IH => intro Δ Ψ' hΔ; exact PROVES.and_elim_l (IH Δ Ψ' hΔ)
  | and_elim_r _ IH => intro Δ Ψ' hΔ; exact PROVES.and_elim_r (IH Δ Ψ' hΔ)
  | or_intro_l Htyped _ IH =>
    intro Δ Ψ' hΔ; exact PROVES.or_intro_l (Htyped := Htyped.ctx_pad Δ) (IH Δ Ψ' hΔ)
  | or_intro_r Htyped _ IH =>
    intro Δ Ψ' hΔ; exact PROVES.or_intro_r (Htyped := Htyped.ctx_pad Δ) (IH Δ Ψ' hΔ)
  | or_elim _ _ _ IH1 IH2 IH3 =>
    intro Δ Ψ' hΔ; exact PROVES.or_elim (IH1 Δ Ψ' hΔ) (IH2 Δ Ψ' hΔ) (IH3 Δ Ψ' hΔ)
  | impl_intro Htyped _ IH =>
    intro Δ Ψ' hΔ; exact PROVES.impl_intro (Htyped := Htyped.ctx_pad Δ) (IH Δ Ψ' hΔ)
  | impl_elim _ _ IH1 IH2 => intro Δ Ψ' hΔ; exact PROVES.impl_elim (IH1 Δ Ψ' hΔ) (IH2 Δ Ψ' hΔ)
  | @forall_intro' τ Γ0 Γs Ψ Φ0 Hsub IH =>
    intro Δ Ψ' hΔ
    have hne : Ψ ≠ [] := by
      have hl := Hsub.len
      rw [intro_wrap_length] at hl
      intro hnil; rw [hnil] at hl; simp at hl
    have h := IH Δ Ψ' hΔ
    rw [← intro_wrap_append hne] at h
    exact PROVES.forall_intro' h
  | @forall_elim' Γ0 Γs Ψ τ Φ0 e HΦ _ He IH =>
    intro Δ Ψ' hΔ
    have h := PROVES.forall_elim' τ Φ0 e (HΦ.ctx_pad Δ) (IH Δ Ψ' hΔ) (He.ctx_pad Δ)
    simp only [List.append_eq] at h
    rwa [binds_single_subst_pad HΦ] at h
  | lift_intro Hpos _ IH =>
    intro Δ Ψ' hΔ; exact PROVES.lift_intro (Hpos := by simp; omega) (IH Δ Ψ' hΔ)
  | later_mono Hpos _ _ IH1 IH2 =>
    intro Δ Ψ' hΔ
    exact PROVES.later_mono (Hpos := by simp; omega) (IH1 Δ Ψ' hΔ) (IH2 Δ Ψ' hΔ)
  | later_and _ _ IH1 IH2 => intro Δ Ψ' hΔ; exact PROVES.later_and (IH1 Δ Ψ' hΔ) (IH2 Δ Ψ' hΔ)
  | later_or _ IH => intro Δ Ψ' hΔ; exact PROVES.later_or (IH Δ Ψ' hΔ)
  | loeb_ind _ IH => intro Δ Ψ' hΔ; exact PROVES.loeb_ind (IH Δ Ψ' hΔ)
  | eq_def HEQ Hlen =>
    intro Δ Ψ' hΔ
    exact PROVES.eq_def (HEQ.ctx_pad Δ) (Hlen := by simp [Hlen, hΔ])
  | @eq_elim B Γ0 Γs Φ0 e1 e2 Ψ HΦ He1 He2 _ _ IH1 IH2 =>
    intro Δ Ψ' hΔ
    have h2 := IH2 Δ Ψ' hΔ
    rw [← binds_single_subst_pad (Γ' := Δ) HΦ] at h2
    have h := PROVES.eq_elim (HΦ.ctx_pad Δ) (He1.ctx_pad Δ) (He2.ctx_pad Δ) (IH1 Δ Ψ' hΔ) h2
    simp only [List.append_eq] at h
    rwa [binds_single_subst_pad HΦ] at h
  | false_elim P Htyped _ IH =>
    intro Δ Ψ' hΔ; exact PROVES.false_elim P (Htyped := Htyped.ctx_pad Δ) (IH Δ Ψ' hΔ)
  | pure_intro p Htyped Hlen =>
    intro Δ Ψ' hΔ
    exact PROVES.pure_intro p (Htyped := Htyped.ctx_pad Δ) (Hlen := by simp [Hlen, hΔ])
  | delay_eq _ IH => intro Δ Ψ' hΔ; exact PROVES.delay_eq (IH Δ Ψ' hΔ)
  | @exists_intro' Γ0 Γs Ψ τ Φ0 e HΦ He _ IH =>
    intro Δ Ψ' hΔ
    refine PROVES.exists_intro' τ Φ0 e (HΦ.ctx_pad Δ) (He.ctx_pad Δ) ?_
    have h := IH Δ Ψ' hΔ
    rw [← binds_single_subst_pad (Γ' := Δ) HΦ] at h
    exact h
  | exists_elim' HQ _ _ IH1 IH2 =>
    intro Δ Ψ' hΔ; exact PROVES.exists_elim' (HQ.ctx_pad Δ) (IH1 Δ Ψ' hΔ) (IH2 Δ Ψ' hΔ)
  | sum_elim e HΦ He _ _ IHl IHr =>
    intro Δ Ψ' hΔ
    exact PROVES.sum_elim e (HΦ.ctx_pad Δ) (He.ctx_pad Δ) (IHl Δ Ψ' hΔ) (IHr Δ Ψ' hΔ)
  | @forall_intro_points Γ0 Γs Ψ A Φ0 HΦ Hlen _ IH =>
    intro Δ Ψ' hΔ
    refine PROVES.forall_intro_points A Φ0 (HΦ.ctx_pad Δ) ?_ ?_
    · simp only [List.length_cons, List.append_eq, List.length_append] at Hlen ⊢
      omega
    intro a
    have h := IH a Δ Ψ' hΔ
    rw [← binds_single_subst_pad (Γ' := Δ) HΦ] at h
    exact h
  | inl_inj _ IH => intro Δ Ψ' hΔ; exact PROVES.inl_inj (IH Δ Ψ' hΔ)
  | inr_inj _ IH => intro Δ Ψ' hΔ; exact PROVES.inr_inj (IH Δ Ψ' hΔ)
  | inl_inr_disj _ IH => intro Δ Ψ' hΔ; exact PROVES.inl_inr_disj (IH Δ Ψ' hΔ)

theorem PROVES.import_ctx0 {Γ0 : OCTX.{i}} {Ψ : PCTX.{i}} {Φ : EXPR.{i}}
    (H : PROVES ([[]] : CTX.{i}) [[]] Φ)
    (Hlen : (Γ0 :: ([] : CTX.{i})).length = Ψ.length) :
    PROVES (Γ0 :: []) Ψ (_root_.weaken Φ (local_weaken_list Γ0.length REN.id)) := by
  obtain ⟨Ψ0, rfl⟩ : ∃ Ψ0, Ψ = [Ψ0] := by
    rcases Ψ with _ | ⟨Ψ0, rest⟩
    · simp at Hlen
    · rcases rest with _ | ⟨a, b⟩
      · exact ⟨Ψ0, rfl⟩
      · simp at Hlen
  have Hσ : TYPED_REN (local_weaken_list Γ0.length REN.id) (Γ0 :: []) ([[]] : CTX.{i}) := by
    have h := local_weaken_list_typed (σ := REN.id) (Γ := ([] : OCTX.{i}))
      (Γs := ([] : CTX.{i})) (Δ := ([] : OCTX.{i})) (Δs := ([] : CTX.{i})) Γ0
      (TYPED_REN.id (by simp))
    simpa using h
  have key := PROVES.weaken H (TickPres.local_weaken_list Γ0.length) Hσ
  have hpctx : weaken_pctx (local_weaken_list Γ0.length REN.id) ([[]] : PCTX.{i})
      = [[]] := by simp [weaken_pctx]
  rw [hpctx] at key
  have final := PROVES.assum_mono (Γ := Γ0 :: []) (Ψa := []) (Γs := []) key Ψ0
  simpa using final

theorem PROVES.import_ctx {Γ0 : OCTX.{i}} {Γs : CTX.{i}} {Ψ : PCTX.{i}} {Φ : EXPR.{i}}
    (H : PROVES ([[]] : CTX.{i}) [[]] Φ)
    (Hlen : (Γ0 :: Γs).length = Ψ.length) :
    PROVES (Γ0 :: Γs) Ψ (_root_.weaken Φ (local_weaken_list Γ0.length REN.id)) := by
  obtain ⟨Ψ0, Ψs, rfl⟩ : ∃ Ψ0 Ψs, Ψ = Ψ0 :: Ψs := by
    rcases Ψ with _ | ⟨Ψ0, Ψs⟩
    · simp at Hlen
    · exact ⟨Ψ0, Ψs, rfl⟩
  have base := PROVES.import_ctx0 (Γ0 := Γ0) (Ψ := [Ψ0]) H (by simp)
  exact base.ctx_pad Γs Ψs (by simpa using Hlen)

end prf
