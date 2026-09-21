module

public import SynthDom.Interp.Interp
public import SynthDom.Syntax.Prf.Weaken

@[expose] public section

section prf

namespace Soundness

section soundness
  open CategoryTheory
  open Opposite
  open Functor
  open CartesianMonoidalCategory
  open MonoidalCategory
  open MonoidalClosed
  open Logic

  @[simp] theorem weaken_global_shift_zero_id (Φ : EXPR.{i}) :
      weaken Φ (REN.global_shift 0 REN.id) = Φ :=
    weaken_eq_self equiv_global_shift_zero_id Φ

  def interp_poctx_at {Γ : CTX.{i}} (d : Nat) (Ψ : POCTX.{i}) : Part (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)) :=
    match Ψ with
    | .nil => pure []
    | .cons Φ Ψs => do
      let Φ' ← expr_interp Γ (weaken Φ (REN.global_shift d REN.id)) TYPE.prop
      let Ψs' ← interp_poctx_at d Ψs
      pure (Φ' :: Ψs')

  def interp_pctx_at {Γ : CTX.{i}} (d : Nat) (Ψ : PCTX.{i}) : Part (List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) :=
    match Ψ with
    | .nil => pure []
    | .cons Ψ Ψs => do
      let Ψ' ← interp_poctx_at d Ψ
      let Ψs' ← interp_pctx_at (d + 1) Ψs
      pure (Ψ' :: Ψs')

  abbrev interp_poctx {Γ : CTX.{i}} (Ψ : POCTX.{i}) : Part (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)) :=
    interp_poctx_at (Γ := Γ) 0 Ψ
  abbrev interp_pctx {Γ : CTX.{i}} (Ψ : PCTX.{i}) : Part (List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) :=
    interp_pctx_at (Γ := Γ) 0 Ψ

   lemma interp_pctx_at_cons_decomp {Γ : CTX.{i}} {d : Nat} {Ψ : POCTX.{i}} {Ψs : PCTX.{i}}
      {Ψ_interp : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))}
      (H : interp_pctx_at d (Ψ :: Ψs) = Pure.pure Ψ_interp)
      : ∃ (Ψ' : List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)) (Ψs' : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))),
        interp_poctx_at d Ψ = Pure.pure Ψ' ∧
        interp_pctx_at (d + 1) Ψs = Pure.pure Ψs' ∧
        Ψ_interp = Ψ' :: Ψs' := by
    simp only [interp_pctx_at] at H
    obtain ⟨Ψ', hΨ', Ψs', hΨs', heq⟩ : ∃ Ψ' Ψs',
        interp_poctx_at d Ψ = Part.some Ψ' ∧
        interp_pctx_at (d + 1) Ψs = Part.some Ψs' ∧
        Ψ_interp = Ψ' :: Ψs' := by
      rw [show (do let Ψ' ← interp_poctx_at d Ψ; let Ψs' ← interp_pctx_at (d + 1) Ψs; pure (Ψ' :: Ψs'))
               = (interp_poctx_at d Ψ).bind (fun Ψ' => (interp_pctx_at (d + 1) Ψs).bind (fun Ψs' => Part.some (Ψ' :: Ψs'))) by rfl] at H
      simp only [Part.bind_some_eq_map, Part.pure_eq_some] at H
      revert H
      cases (interp_poctx_at d Ψ) using Part.induction_on with
      | hnone => simp
      | hsome a =>
        simp only [Part.bind_some, Part.some_inj, exists_and_left, exists_eq_left']
        cases (interp_pctx_at (d + 1) Ψs) using Part.induction_on with
        | hnone => simp
        | hsome as =>
          simp only [Part.map_some, Part.some_inj, exists_eq_left']; intro H; symm; exact H
    exact ⟨Ψ', hΨ', Ψs', hΨs', heq⟩

   lemma interp_pctx_cons_decomp {Γ : CTX.{i}} {Ψ : POCTX.{i}} {Ψs : PCTX.{i}}
      {Ψ_interp : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))}
      (H : interp_pctx (Ψ :: Ψs) = Pure.pure Ψ_interp)
      : ∃ (Ψ' : List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)) (Ψs' : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))),
        interp_poctx Ψ = Pure.pure Ψ' ∧
        interp_pctx_at 1 Ψs = Pure.pure Ψs' ∧
        Ψ_interp = Ψ' :: Ψs' :=
    interp_pctx_at_cons_decomp H

  def ctx_typed (Γ : CTX.{i}) (Ψ : PCTX.{i}) : Prop :=
    ∀ (n m : Nat) (Ψ' : POCTX.{i}) (Φ : EXPR.{i}),
      Ψ[n]? = some Ψ' → Ψ'[m]? = some Φ → TYPED (Γ.drop n) Φ TYPE.prop

  lemma ctx_typed_lift {Γ : CTX.{i}} {Ψ : PCTX.{i}} (H : ctx_typed Γ Ψ) :
      ctx_typed ([] :: Γ) ([] :: Ψ) := by
    intro n m Ψ' Φ Hn Hm
    cases n with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at Hn; subst Hn; simp at Hm
    | succ n' =>
      simp only [List.getElem?_cons_succ] at Hn
      simp only [List.drop_succ_cons]
      exact H n' m Ψ' Φ Hn Hm

  lemma ctx_typed_drop {Γ : CTX.{i}} {Ψ : PCTX.{i}} (k : Nat) (H : ctx_typed Γ Ψ) :
      ctx_typed (Γ.drop k) (Ψ.drop k) := by
    intro n m Ψ' Φ Hn Hm
    rw [List.getElem?_drop] at Hn
    rw [List.drop_drop]
    exact H (k + n) m Ψ' Φ Hn Hm

  lemma ctx_typed_cons0 {Γ : CTX.{i}} {Ψ : POCTX.{i}} {Ψs : PCTX.{i}} {Φ1 : EXPR.{i}}
      (H : ctx_typed Γ (Ψ :: Ψs)) (HΦ1 : TYPED (Γ.drop 0) Φ1 TYPE.prop) :
      ctx_typed Γ ((Φ1 :: Ψ) :: Ψs) := by
    intro n m Ψ' Φ Hn Hm
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at Hn; subst Hn
      cases m with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at Hm; subst Hm; exact HΦ1
      | succ m' =>
        simp only [List.getElem?_cons_succ] at Hm
        exact H 0 m' Ψ Φ (by simp) Hm
    | succ n' =>
      simp only [List.getElem?_cons_succ] at Hn
      exact H (n' + 1) m Ψ' Φ (by simp only [List.getElem?_cons_succ]; exact Hn) Hm

  lemma soundness_true_intro {Γ : CTX.{i}} {Ψ : PCTX.{i}}
    (_Hlen : 0 < Γ.length)
    (Ψ_interp : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
    (_HΨ : interp_pctx Ψ = pure Ψ_interp)
    (HΦ : expr_interp Γ EXPR.true TYPE.prop = pure Φ_interp)
    : pctx Ψ_interp ⊢ᵢ Φ_interp := by

    simp [interp_true] at HΦ
    rw [← HΦ]
    apply true_intro

  lemma soundness_and_intro {Γ : CTX.{i}} {Ψ : PCTX.{i}} {Φ₁ Φ₂ : PROPOSITION.{i}}
    (H1 : PROVES Γ Ψ Φ₁) (H2 : PROVES Γ Ψ Φ₂)
    (IH1 : ∀ (Ψ_interp : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ),
      interp_pctx Ψ = pure Ψ_interp → expr_interp Γ Φ₁ TYPE.prop = pure Φ_interp → pctx Ψ_interp ⊢ᵢ Φ_interp)
    (IH2 : ∀ (Ψ_interp : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ),
      interp_pctx Ψ = pure Ψ_interp → expr_interp Γ Φ₂ TYPE.prop = pure Φ_interp → pctx Ψ_interp ⊢ᵢ Φ_interp)
    (Ψ_interp : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
    (HΨ : interp_pctx Ψ = pure Ψ_interp)
    (HΦ : expr_interp Γ (.and Φ₁ Φ₂) TYPE.prop = pure Φ_interp)
    : pctx Ψ_interp ⊢ᵢ Φ_interp := by

    simp only [expr_interp] at HΦ

    obtain ⟨Φ₁_interp, Φ₂_interp, h1, h2, eq⟩ : ∃ Φ₁_interp Φ₂_interp,
        expr_interp Γ Φ₁ TYPE.prop = Part.some Φ₁_interp ∧
        expr_interp Γ Φ₂ TYPE.prop = Part.some Φ₂_interp ∧
        Φ_interp = interp_and Φ₁_interp Φ₂_interp := by
      simp only [show (do let e1' ← expr_interp Γ Φ₁ TYPE.prop
                          let e2' ← expr_interp Γ Φ₂ TYPE.prop
                          pure (interp_and e1' e2'))
                    = (expr_interp Γ Φ₁ TYPE.prop).bind (fun e1' =>
                        (expr_interp Γ Φ₂ TYPE.prop).bind (fun e2' =>
                          Part.some (interp_and e1' e2'))) by rfl,
                 Part.Dom.bind (expr_interp_correct (PROVES.typed H1)),
                 Part.Dom.bind (expr_interp_correct (PROVES.typed H2))] at HΦ
      simp at HΦ
      exact ⟨_, _, by simp, by simp, HΦ.symm⟩

    rw [eq]
    simp only [interp_and]
    apply conj_intro
    · exact IH1 Ψ_interp Φ₁_interp HΨ h1
    · exact IH2 Ψ_interp Φ₂_interp HΨ h2

  lemma soundness_and_elim_l {Γ : CTX.{i}} {Ψ : PCTX.{i}} {Φ₁ Φ₂ : PROPOSITION.{i}}
    (H : PROVES Γ Ψ (.and Φ₁ Φ₂))
    (IH : ∀ (Ψ_interp : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ),
      interp_pctx Ψ = pure Ψ_interp → expr_interp Γ (.and Φ₁ Φ₂) TYPE.prop = pure Φ_interp → pctx Ψ_interp ⊢ᵢ Φ_interp)
    (Ψ_interp : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
    (HΨ : interp_pctx Ψ = pure Ψ_interp)
    (HΦ : expr_interp Γ Φ₁ TYPE.prop = pure Φ_interp)
    : pctx Ψ_interp ⊢ᵢ Φ_interp := by

    obtain ⟨_, h1_typed, h2_typed⟩ := (PROVES.typed H).and_inversion

    have h1_dom := expr_interp_correct h1_typed
    have h2_dom := expr_interp_correct h2_typed

    obtain ⟨Φ₁_interp, Φ₂_interp, h1, h2⟩ : ∃ Φ₁_interp Φ₂_interp,
        expr_interp Γ Φ₁ TYPE.prop = Part.some Φ₁_interp ∧
        expr_interp Γ Φ₂ TYPE.prop = Part.some Φ₂_interp := by
        use (expr_interp Γ Φ₁ TYPE.prop).get h1_dom, (expr_interp Γ Φ₂ TYPE.prop).get h2_dom
        simp

    have h_and_interp : expr_interp Γ (.and Φ₁ Φ₂) TYPE.prop = Part.some (interp_and Φ₁_interp Φ₂_interp) := by
        simp [expr_interp, h1, h2]

    have ih_result := IH Ψ_interp (interp_and Φ₁_interp Φ₂_interp) HΨ h_and_interp

    rw [show Φ_interp = Φ₁_interp from Part.some_injective (HΦ.symm.trans h1)]
    simp only [interp_and] at ih_result
    apply conj_elim_l'
    exact ih_result

  lemma soundness_and_elim_r {Γ : CTX.{i}} {Ψ : PCTX.{i}} {Φ₁ Φ₂ : PROPOSITION.{i}}
    (H : PROVES Γ Ψ (.and Φ₁ Φ₂))
    (IH : ∀ (Ψ_interp : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ),
      interp_pctx Ψ = pure Ψ_interp → expr_interp Γ (.and Φ₁ Φ₂) TYPE.prop = pure Φ_interp → pctx Ψ_interp ⊢ᵢ Φ_interp)
    (Ψ_interp : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
    (HΨ : interp_pctx Ψ = pure Ψ_interp)
    (HΦ : expr_interp Γ Φ₂ TYPE.prop = pure Φ_interp)
    : pctx Ψ_interp ⊢ᵢ Φ_interp := by

    cases PROVES.typed H with
    | and h1_typed h2_typed =>

      obtain ⟨Φ₁_interp, Φ₂_interp, h1, h2⟩ : ∃ Φ₁_interp Φ₂_interp,
          expr_interp Γ Φ₁ TYPE.prop = Part.some Φ₁_interp ∧
          expr_interp Γ Φ₂ TYPE.prop = Part.some Φ₂_interp := by
        use (expr_interp Γ Φ₁ TYPE.prop).get (expr_interp_correct h1_typed),
            (expr_interp Γ Φ₂ TYPE.prop).get (expr_interp_correct h2_typed)
        simp

      have ih_result := IH Ψ_interp (interp_and Φ₁_interp Φ₂_interp) HΨ (by simp [expr_interp, h1, h2])

      rw [show Φ_interp = Φ₂_interp from Part.some_injective (HΦ.symm.trans h2)]
      simp only [interp_and] at ih_result
      apply conj_elim_r'
      exact ih_result

  lemma soundness_or_intro_l {Γ : CTX.{i}} {Ψ : PCTX.{i}} {Φ₁ Φ₂ : PROPOSITION.{i}}
    (HΦ2 : TYPED Γ Φ₂ TYPE.prop) (H : PROVES Γ Ψ Φ₁)
    (IH : ∀ (Ψ_interp : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ),
      interp_pctx Ψ = pure Ψ_interp → expr_interp Γ Φ₁ TYPE.prop = pure Φ_interp → pctx Ψ_interp ⊢ᵢ Φ_interp)
    (Ψ_interp : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
    (HΨ : interp_pctx Ψ = pure Ψ_interp)
    (HΦ : expr_interp Γ (.or Φ₁ Φ₂) TYPE.prop = pure Φ_interp)
    : pctx Ψ_interp ⊢ᵢ Φ_interp := by

    simp only [expr_interp] at HΦ

    obtain ⟨Φ₁_interp, Φ₂_interp, h1, h2, eq⟩ : ∃ Φ₁_interp Φ₂_interp,
        expr_interp Γ Φ₁ TYPE.prop = Part.some Φ₁_interp ∧
        expr_interp Γ Φ₂ TYPE.prop = Part.some Φ₂_interp ∧
        Φ_interp = interp_or Φ₁_interp Φ₂_interp := by
      simp only [show (do let e1' ← expr_interp Γ Φ₁ TYPE.prop
                          let e2' ← expr_interp Γ Φ₂ TYPE.prop
                          pure (interp_or e1' e2'))
                    = (expr_interp Γ Φ₁ TYPE.prop).bind (fun e1' =>
                        (expr_interp Γ Φ₂ TYPE.prop).bind (fun e2' =>
                          Part.some (interp_or e1' e2'))) by rfl,
                 Part.Dom.bind (expr_interp_correct (PROVES.typed H)),
                 Part.Dom.bind (expr_interp_correct HΦ2)] at HΦ
      simp at HΦ
      exact ⟨_, _, by simp, by simp, HΦ.symm⟩

    rw [eq]
    simp only [interp_or]
    apply disj_intro_l'
    exact IH Ψ_interp Φ₁_interp HΨ h1

  lemma soundness_or_intro_r {Γ : CTX.{i}} {Ψ : PCTX.{i}} {Φ₁ Φ₂ : PROPOSITION.{i}}
    (HΦ1 : TYPED Γ Φ₁ TYPE.prop) (H : PROVES Γ Ψ Φ₂)
    (IH : ∀ (Ψ_interp : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ),
      interp_pctx Ψ = pure Ψ_interp → expr_interp Γ Φ₂ TYPE.prop = pure Φ_interp → pctx Ψ_interp ⊢ᵢ Φ_interp)
    (Ψ_interp : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
    (HΨ : interp_pctx Ψ = pure Ψ_interp)
    (HΦ : expr_interp Γ (.or Φ₁ Φ₂) TYPE.prop = pure Φ_interp)
    : pctx Ψ_interp ⊢ᵢ Φ_interp := by

    simp only [expr_interp] at HΦ

    obtain ⟨Φ₁_interp, Φ₂_interp, h1, h2, eq⟩ : ∃ Φ₁_interp Φ₂_interp,
        expr_interp Γ Φ₁ TYPE.prop = Part.some Φ₁_interp ∧
        expr_interp Γ Φ₂ TYPE.prop = Part.some Φ₂_interp ∧
        Φ_interp = interp_or Φ₁_interp Φ₂_interp := by
      simp only [show (do let e1' ← expr_interp Γ Φ₁ TYPE.prop
                          let e2' ← expr_interp Γ Φ₂ TYPE.prop
                          pure (interp_or e1' e2'))
                    = (expr_interp Γ Φ₁ TYPE.prop).bind (fun e1' =>
                        (expr_interp Γ Φ₂ TYPE.prop).bind (fun e2' =>
                          Part.some (interp_or e1' e2'))) by rfl,
                 Part.Dom.bind (expr_interp_correct HΦ1),
                 Part.Dom.bind (expr_interp_correct (PROVES.typed H))] at HΦ
      simp at HΦ
      exact ⟨_, _, by simp, by simp, HΦ.symm⟩

    rw [eq]
    simp only [interp_or]
    apply disj_intro_r'
    exact IH Ψ_interp Φ₂_interp HΨ h2

  lemma soundness_impl_elim {Γ : CTX.{i}} {Ψ : PCTX.{i}} {Φ₁ Φ₂ : PROPOSITION.{i}}
    (H1 : PROVES Γ Ψ (.impl Φ₁ Φ₂)) (H2 : PROVES Γ Ψ Φ₁)
    (IH1 : ∀ (Ψ_interp : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ),
      interp_pctx Ψ = pure Ψ_interp → expr_interp Γ (.impl Φ₁ Φ₂) TYPE.prop = pure Φ_interp → pctx Ψ_interp ⊢ᵢ Φ_interp)
    (IH2 : ∀ (Ψ_interp : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ),
      interp_pctx Ψ = pure Ψ_interp → expr_interp Γ Φ₁ TYPE.prop = pure Φ_interp → pctx Ψ_interp ⊢ᵢ Φ_interp)
    (Ψ_interp : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
    (HΨ : interp_pctx Ψ = pure Ψ_interp)
    (HΦ : expr_interp Γ Φ₂ TYPE.prop = pure Φ_interp)
    : pctx Ψ_interp ⊢ᵢ Φ_interp := by

    cases PROVES.typed H1 with
    | impl h1_typed h2_typed =>
      obtain ⟨Φ₁_interp, Φ₂_interp, h_phi1, h_phi2⟩ : ∃ Φ₁_interp Φ₂_interp,
          expr_interp Γ Φ₁ TYPE.prop = Part.some Φ₁_interp ∧
          expr_interp Γ Φ₂ TYPE.prop = Part.some Φ₂_interp := by
        use (expr_interp Γ Φ₁ TYPE.prop).get (expr_interp_correct h1_typed),
            (expr_interp Γ Φ₂ TYPE.prop).get (expr_interp_correct h2_typed)
        simp

      have ih1_result := IH1 Ψ_interp (interp_impl Φ₁_interp Φ₂_interp) HΨ (by simp [expr_interp, h_phi1, h_phi2])

      have ih2_result := IH2 Ψ_interp Φ₁_interp HΨ h_phi1

      rw [show Φ_interp = Φ₂_interp from (Part.some_injective (h_phi2.symm.trans HΦ)).symm]
      apply elim_impl ih1_result ih2_result

  lemma later_eqI_entails {B : ℐ.{i}} :
      (later.map (eqI : (B ⊗ B) ⟶ Ω) ≫ lift_subobject_classifier)
        ⊢ᵢ (lift (later.map (fst B B)) (later.map (snd B B)) ≫ eqI) := by
    intro n γ m g hyp
    cases n with
    | zero =>
      obtain rfl : m = 0 := Nat.le_zero.mp (leOfHom g)
      show (later.obj B).map g.op _ = (later.obj B).map g.op _
      have : Subsingleton ((later.obj B).obj (op 0)) := by rw [later_obj_obj_zero]; infer_instance
      exact Subsingleton.elim _ _
    | succ n' =>
      show (later.obj B).map g.op _ = (later.obj B).map g.op _
      change (Sieve_succFunctor ((eqI.app (op n') _).down)).arrows g at hyp
      simp only [Sieve_succFunctor, Presieve_succFunctor] at hyp
      have hsub : Subsingleton ((later.obj B).obj (op 0)) := by rw [later_obj_obj_zero]; infer_instance
      rcases hyp with hleft | hm0
      · cases m with
        | zero => exact Subsingleton.elim _ _
        | succ m' => convert hleft using 2; rfl
      · cases m with
        | zero => exact Subsingleton.elim _ _
        | succ m' => exact absurd hm0 (Nat.succ_ne_zero m')

  lemma delay_eq_entails {Γ : CTX.{i}} {A : TYPE.{i}} (f g : ⟦[] :: Γ⟧ₛ ⟶ ⟦A⟧ₜ) :
      interp_lift (interp_delay (interp_eq f g))
        ⊢ᵢ interp_eq (interp_delay f) (interp_delay g) := by
    set p : ⟦Γ⟧ₛ ⟶ later.obj ⟦[] :: Γ⟧ₛ :=
      earlier_later_adj.unit.app ⟦Γ⟧ₛ ≫ later.map ((λ_ (earlier.obj ⟦Γ⟧ₛ)).inv) with hp
    have hdelay : ∀ {τ : TYPE.{i}} (h : ⟦[] :: Γ⟧ₛ ⟶ ⟦τ⟧ₜ),
        interp_delay h = p ≫ later.map h := by
      intro τ h
      rw [hp]; unfold interp_delay
      simp only [Equiv.toFun_as_coe, Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
    have hmapeq : later.map (interp_eq f g) = later.map (lift f g) ≫ later.map eqI :=
      Functor.map_comp later (lift f g) eqI
    have hlifteq : lift (later.map f) (later.map g)
        = later.map (lift f g) ≫ lift (later.map (fst _ _)) (later.map (snd _ _)) := by
      rw [comp_lift, ← Functor.map_comp, ← Functor.map_comp, lift_fst, lift_snd]
    have hL : interp_lift (interp_delay (interp_eq f g))
        = (p ≫ later.map (lift f g)) ≫ (later.map eqI ≫ lift_subobject_classifier) := by
      simp only [interp_lift, hdelay, hmapeq]; rfl
    have hR : interp_eq (interp_delay f) (interp_delay g)
        = (p ≫ later.map (lift f g)) ≫ (lift (later.map (fst _ _)) (later.map (snd _ _)) ≫ eqI) := by
      show lift (interp_delay f) (interp_delay g) ≫ eqI = _
      dsimp only [interp_ty]
      rw [hdelay f, hdelay g, ← comp_lift, hlifteq]; rfl
    rw [hL, hR]
    exact entails_subst _ _ _ later_eqI_entails

  lemma soundness_delay_eq {Γ : CTX.{i}} {Ψ : PCTX.{i}} {A : TYPE.{i}} {e1 e2 : EXPR.{i}}
      (_H : PROVES Γ Ψ (.lift (.delay (.eq A e1 e2))))
      (IH : ∀ (Ψ_i : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_i : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ),
        interp_pctx Ψ = pure Ψ_i →
        expr_interp Γ (.lift (.delay (.eq A e1 e2))) TYPE.prop = pure Φ_i → pctx Ψ_i ⊢ᵢ Φ_i)
      (Ψ_interp : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
      (HΨ : interp_pctx Ψ = pure Ψ_interp)
      (HΦ : expr_interp Γ (.eq (.later A) (.delay e1) (.delay e2)) TYPE.prop = pure Φ_interp)
      : pctx Ψ_interp ⊢ᵢ Φ_interp := by
    obtain ⟨_, hd⟩ := TYPED.lift_inversion (PROVES.typed _H)
    obtain ⟨_, _, heqd⟩ := TYPED.delay_inversion hd
    obtain ⟨_, he1, he2⟩ := TYPED.eq_inversion heqd
    set f := (expr_interp ([] :: Γ) e1 A).get (expr_interp_correct he1) with hf
    set g := (expr_interp ([] :: Γ) e2 A).get (expr_interp_correct he2) with hg
    have hfe : expr_interp ([] :: Γ) e1 A = Part.some f := (Part.some_get _).symm
    have hge : expr_interp ([] :: Γ) e2 A = Part.some g := (Part.some_get _).symm
    rw [show Φ_interp = interp_eq (interp_delay f) (interp_delay g) by
      rw [show expr_interp Γ (.eq (.later A) (.delay e1) (.delay e2)) TYPE.prop
          = Part.some (interp_eq (interp_delay f) (interp_delay g)) by
        simp only [expr_interp]; rw [hfe, hge]; simp [Part.bind_some]] at HΦ
      exact (Part.some_injective HΦ).symm]
    exact entails_trans _ _ _
      (IH Ψ_interp _ HΨ (by simp only [expr_interp]; rw [hfe, hge]; simp [Part.bind_some]))
      (delay_eq_entails f g)

  lemma soundness_eq_def {Γ : CTX.{i}} {Ψ : PCTX.{i}} {τ : TYPE.{i}} {e1 e2 : EXPR.{i}}
    (Heq : EQ Γ τ e1 e2)
    (Ψ_interp : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
    (_HΨ : interp_pctx Ψ = pure Ψ_interp)
    (HΦ : expr_interp Γ (.eq τ e1 e2) TYPE.prop = pure Φ_interp)
    : pctx Ψ_interp ⊢ᵢ Φ_interp := by

    obtain ⟨e1_interp, e2_interp, he1, he2⟩ : ∃ e1_interp e2_interp,
        expr_interp Γ e1 τ = Part.some e1_interp ∧
        expr_interp Γ e2 τ = Part.some e2_interp := by
      use (expr_interp Γ e1 τ).get (expr_interp_correct (EQ.typed Heq)),
          (expr_interp Γ e2 τ).get (expr_interp_correct (EQ.typed' Heq))
      simp

    rw [show Φ_interp = interp_eq e1_interp e2_interp from
      (Part.some_injective
        ((show expr_interp Γ (.eq τ e1 e2) TYPE.prop = Part.some (interp_eq e1_interp e2_interp) by
          simp [expr_interp, he1, he2]).symm.trans HΦ)).symm]
    apply intro_eq
    exact Part.some_injective (show Part.some e1_interp = Part.some e2_interp by
      rw [←he1, ←he2, eq_interp Γ e1 e2 τ Heq])

  lemma soundness_false_elim {Γ : CTX.{i}} {Ψ : PCTX.{i}} {P : PROPOSITION.{i}}
    (_HP : TYPED Γ P TYPE.prop) (_H : PROVES Γ Ψ EXPR.false)
    (IH : ∀ (Ψ_interp : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ),
      interp_pctx Ψ = pure Ψ_interp → expr_interp Γ EXPR.false TYPE.prop = pure Φ_interp → pctx Ψ_interp ⊢ᵢ Φ_interp)
    (Ψ_interp : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
    (HΨ : interp_pctx Ψ = pure Ψ_interp)
    (_HΦ : expr_interp Γ P TYPE.prop = pure Φ_interp)
    : pctx Ψ_interp ⊢ᵢ Φ_interp := by

    apply elim_false (IH Ψ_interp interp_false HΨ (by simp only [expr_interp, interp_false]))

  lemma soundness_pure_intro {Γ : CTX.{i}} {Ψ : PCTX.{i}} {P : Prop}
    (Hprop : P) (_Htyped : TYPED Γ (.pure (.embed Prop P)) TYPE.prop)
    (Ψ_interp : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
    (_HΨ : interp_pctx Ψ = pure Ψ_interp)
    (HΦ : expr_interp Γ (.pure (.embed Prop P)) TYPE.prop = pure Φ_interp)
    : pctx Ψ_interp ⊢ᵢ Φ_interp := by

    rw [show Φ_interp = interp_pure (interp_embed Prop P) from
      (Part.some_injective
        ((show expr_interp Γ (.pure (.embed Prop P)) TYPE.prop = Part.some (interp_pure (interp_embed Prop P)) by
          simp [expr_interp, Part.assert_pos]).symm.trans HΦ)).symm]
    apply intro_pure
    exact Hprop

  lemma soundness_eq_elim {Γ : OCTX.{i}} {Γs : CTX.{i}} {Ψ : PCTX.{i}} {τ : TYPE.{i}} {Φ e1 e2 : EXPR.{i}}
    (HΦ : TYPED ((τ :: Γ) :: Γs) Φ TYPE.prop)
    (H1 : PROVES (Γ :: Γs) Ψ (.eq τ e1 e2))
    (_H2 : PROVES (Γ :: Γs) Ψ (binds (single_subst (List.map List.length (Γ :: Γs)) e1) Φ))
    (IH1 : ∀ (Ψ_interp : List (List (⟦Γ :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ),
      interp_pctx Ψ = pure Ψ_interp →
      expr_interp (Γ :: Γs) (.eq τ e1 e2) TYPE.prop = pure Φ_interp → pctx Ψ_interp ⊢ᵢ Φ_interp)
    (IH2 : ∀ (Ψ_interp : List (List (⟦Γ :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ),
      interp_pctx Ψ = pure Ψ_interp →
      expr_interp (Γ :: Γs) (binds (single_subst (List.map List.length (Γ :: Γs)) e1) Φ) TYPE.prop = pure Φ_interp →
      pctx Ψ_interp ⊢ᵢ Φ_interp)
    (Ψ_interp : List (List (⟦Γ :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
    (HΨ : interp_pctx Ψ = pure Ψ_interp)
    (HΦ' : expr_interp (Γ :: Γs) (binds (single_subst (List.map List.length (Γ :: Γs)) e2) Φ) TYPE.prop = pure Φ_interp)
    : pctx Ψ_interp ⊢ᵢ Φ_interp := by

    obtain ⟨_, h1_typed, h2_typed⟩ := TYPED.eq_inversion (PROVES.typed H1)

    obtain ⟨e1_interp, e2_interp, Φ_body_interp, he1, he2, hΦ_body⟩ : ∃ e1_interp e2_interp Φ_body_interp,
        expr_interp (Γ :: Γs) e1 τ = Part.some e1_interp ∧
        expr_interp (Γ :: Γs) e2 τ = Part.some e2_interp ∧
        expr_interp ((τ :: Γ) :: Γs) Φ TYPE.prop = Part.some Φ_body_interp := by
      use (expr_interp (Γ :: Γs) e1 τ).get (expr_interp_correct h1_typed),
          (expr_interp (Γ :: Γs) e2 τ).get (expr_interp_correct h2_typed),
          (expr_interp ((τ :: Γ) :: Γs) Φ TYPE.prop).get (expr_interp_correct HΦ)
      simp

    have h_Φe1_interp : expr_interp (Γ :: Γs) (binds (single_subst (List.map List.length (Γ :: Γs)) e1) Φ) TYPE.prop
        = Part.some ((lift e1_interp (𝟙 _) ≫ (α_ _ _ _).inv) ≫ Φ_body_interp) := by

      let h_tssubst1 := TSSUBST.single_subst h1_typed

      have h_bind : expr_interp (Γ :: Γs) (binds (single_subst (List.map List.length (Γ :: Γs)) e1) Φ) TYPE.prop
          = (expr_interp ((τ :: Γ) :: Γs) Φ TYPE.prop).map (fun x => ⟦h_tssubst1⟧ₛₛ ≫ x) := by
        apply eq_bind
        exact HΦ

      rw [h_bind]
      rw [hΦ_body]
      simp [Part.map]

      have h_subst : ⟦h_tssubst1⟧ₛₛ = (lift e1_interp (𝟙 _) ≫ (α_ _ _ _).inv) := by
        rw [ssubst_single_interp]
        simp [he1]

      erw [h_subst]
      rfl

    have h_goal_eq : Φ_interp = (lift e2_interp (𝟙 _) ≫ (α_ _ _ _).inv) ≫ Φ_body_interp := by
      have h : Part.some ((lift e2_interp (𝟙 _) ≫ (α_ _ _ _).inv) ≫ Φ_body_interp) = Part.some Φ_interp := by

        let h_tssubst2 := TSSUBST.single_subst h2_typed

        have h_bind2 : expr_interp (Γ :: Γs) (binds (single_subst (List.map List.length (Γ :: Γs)) e2) Φ) TYPE.prop
            = (expr_interp ((τ :: Γ) :: Γs) Φ TYPE.prop).map (fun x => ⟦h_tssubst2⟧ₛₛ ≫ x) := by
          apply eq_bind
          exact HΦ

        rw [h_bind2] at HΦ'
        rw [hΦ_body] at HΦ'
        simp [Part.map] at HΦ'

        have h_subst2 : ⟦h_tssubst2⟧ₛₛ = (lift e2_interp (𝟙 _) ≫ (α_ _ _ _).inv) := by
          rw [ssubst_single_interp]
          simp [he2]

        erw [h_subst2] at HΦ'
        exact HΦ'
      simp at h
      exact h.symm

    rw [h_goal_eq]
    apply elim_eq _ _ Φ_body_interp
      (IH1 Ψ_interp (interp_eq e1_interp e2_interp) HΨ (by simp [expr_interp, he1, he2]))
      (IH2 Ψ_interp ((lift e1_interp (𝟙 _) ≫ (α_ _ _ _).inv) ≫ Φ_body_interp) HΨ h_Φe1_interp)

  lemma soundness_or_elim {Γ : CTX.{i}} {Ψ : POCTX.{i}} {Ψs : PCTX.{i}} {P Q Φ : PROPOSITION.{i}}
    (H1 : PROVES Γ ((P :: Ψ) :: Ψs) Φ)
    (H2 : PROVES Γ ((Q :: Ψ) :: Ψs) Φ)
    (H3 : PROVES Γ (Ψ :: Ψs) (.or P Q))
    (IH1 : ∀ (Ψ_interp : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ),
      interp_pctx ((P :: Ψ) :: Ψs) = pure Ψ_interp → expr_interp Γ Φ TYPE.prop = pure Φ_interp → pctx Ψ_interp ⊢ᵢ Φ_interp)
    (IH2 : ∀ (Ψ_interp : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ),
      interp_pctx ((Q :: Ψ) :: Ψs) = pure Ψ_interp → expr_interp Γ Φ TYPE.prop = pure Φ_interp → pctx Ψ_interp ⊢ᵢ Φ_interp)
    (IH3 : ∀ (Ψ_interp : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ),
      interp_pctx (Ψ :: Ψs) = pure Ψ_interp → expr_interp Γ (.or P Q) TYPE.prop = pure Φ_interp → pctx Ψ_interp ⊢ᵢ Φ_interp)
    (Ψ_interp : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
    (HΨ : interp_pctx (Ψ :: Ψs) = pure Ψ_interp)
    (HΦ : expr_interp Γ Φ TYPE.prop = pure Φ_interp)
    : pctx Ψ_interp ⊢ᵢ Φ_interp := by

    cases PROVES.typed H3 with
    | or hp_typed hq_typed =>
      obtain ⟨P_interp, Q_interp, hp, hq⟩ : ∃ P_interp Q_interp,
          expr_interp Γ P TYPE.prop = Part.some P_interp ∧
          expr_interp Γ Q TYPE.prop = Part.some Q_interp := by
        use (expr_interp Γ P TYPE.prop).get (expr_interp_correct hp_typed),
            (expr_interp Γ Q TYPE.prop).get (expr_interp_correct hq_typed)
        simp

      have ih3_result := IH3 Ψ_interp (interp_or P_interp Q_interp) HΨ (by simp [expr_interp, hp, hq])
      obtain ⟨Ψ', Ψs', he1, he2, he3⟩ := interp_pctx_cons_decomp HΨ
      rw [he3]
      apply elim_or (Φ₁ := P_interp) (Φ₂ := Q_interp)
      · rw [← he3]; exact ih3_result
      · exact IH1 ((P_interp :: Ψ') :: Ψs') Φ_interp
          (by simp [interp_pctx, interp_pctx_at, interp_poctx_at,
            weaken_global_shift_zero_id, hp, he1, he2]) HΦ
      · exact IH2 ((Q_interp :: Ψ') :: Ψs') Φ_interp
          (by simp [interp_pctx, interp_pctx_at, interp_poctx_at,
            weaken_global_shift_zero_id, hq, he1, he2]) HΦ

  lemma soundness_impl_intro {Γ : CTX.{i}} {Ψ : POCTX.{i}} {Ψs : PCTX.{i}} {Φ₁ Φ₂ : PROPOSITION.{i}}
    (HΦ1 : TYPED Γ Φ₁ TYPE.prop) (H : PROVES Γ ((Φ₁ :: Ψ) :: Ψs) Φ₂)
    (IH : ∀ (Ψ_interp : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ),
      interp_pctx ((Φ₁ :: Ψ) :: Ψs) = pure Ψ_interp → expr_interp Γ Φ₂ TYPE.prop = pure Φ_interp → pctx Ψ_interp ⊢ᵢ Φ_interp)
    (Ψ_interp : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
    (HΨ : interp_pctx (Ψ :: Ψs) = pure Ψ_interp)
    (HΦ : expr_interp Γ (.impl Φ₁ Φ₂) TYPE.prop = pure Φ_interp)
    : pctx Ψ_interp ⊢ᵢ Φ_interp := by
    obtain ⟨Ψ', Ψs', he1, he2, he3⟩ := interp_pctx_cons_decomp HΨ
    rw [he3]; simp only [pctx]

    obtain ⟨Φ₁_interp, Φ₂_interp, h_phi1, h_phi2⟩ : ∃ Φ₁_interp Φ₂_interp,
        expr_interp Γ Φ₁ TYPE.prop = Part.some Φ₁_interp ∧
        expr_interp Γ Φ₂ TYPE.prop = Part.some Φ₂_interp := by
      use (expr_interp Γ Φ₁ TYPE.prop).get (expr_interp_correct HΦ1),
          (expr_interp Γ Φ₂ TYPE.prop).get (expr_interp_correct (PROVES.typed H))
      simp

    rw [show Φ_interp = interp_impl Φ₁_interp Φ₂_interp from
      Part.some_injective (HΦ.symm.trans (by simp [expr_interp, h_phi1, h_phi2]))]
    simp only [interp_impl]
    apply intro_impl
    apply IH ((Φ₁_interp :: Ψ') :: Ψs') Φ₂_interp
    · simp [interp_pctx, interp_pctx_at, interp_poctx_at, weaken_global_shift_zero_id, h_phi1, he1, he2]
    · exact h_phi2

  lemma soundness_forall_elim' {Γ : CTX.{i}} {Ψ : PCTX.{i}} {τ : TYPE.{i}} {Φ : PROPOSITION.{i}} {e : EXPR.{i}}
    (He : TYPED Γ e τ) (H : PROVES Γ Ψ (.forall' τ Φ))
    (IH : ∀ (Ψ_interp : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ),
      interp_pctx Ψ = pure Ψ_interp → expr_interp Γ (.forall' τ Φ) TYPE.prop = pure Φ_interp → pctx Ψ_interp ⊢ᵢ Φ_interp)
    (Ψ_interp : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
    (HΨ : interp_pctx Ψ = pure Ψ_interp)
    (HΦ : expr_interp Γ (binds (single_subst (List.map List.length Γ) e) Φ) TYPE.prop = pure Φ_interp)
    : pctx Ψ_interp ⊢ᵢ Φ_interp := by
    cases Γ with
    | nil => simpa using typing_stack_len He
    | cons Γ' Γs =>
      set e_interp := (expr_interp (Γ' :: Γs) e τ).get (expr_interp_correct He)
      have h_e_eq : expr_interp (Γ' :: Γs) e τ = Part.some e_interp := by
        ext; simp [e_interp]

      obtain ⟨_, h_body_typed⟩ := TYPED.forall'_inversion (PROVES.typed H)

      set Φ_body := (expr_interp ((τ :: Γ') :: Γs) Φ TYPE.prop).get (expr_interp_correct h_body_typed)

      have h_body_eq : expr_interp ((τ :: Γ') :: Γs) Φ TYPE.prop = Part.some Φ_body := by
        ext; simp [Φ_body]

      have h_subst_interp : expr_interp (Γ' :: Γs) (binds (single_subst (List.map List.length (Γ' :: Γs)) e) Φ) TYPE.prop
          = Part.some ((lift e_interp (𝟙 _) ≫ (α_ _ _ _).inv) ≫ Φ_body) := by
        let h_tssubst := TSSUBST.single_subst He
        rw [show expr_interp (Γ' :: Γs) (binds (single_subst (List.map List.length (Γ' :: Γs)) e) Φ) TYPE.prop
            = (expr_interp ((τ :: Γ') :: Γs) Φ TYPE.prop).map (fun x => ⟦h_tssubst⟧ₛₛ ≫ x) by
          apply eq_bind; exact h_body_typed, h_body_eq]
        have h_subst : ⟦h_tssubst⟧ₛₛ = (lift e_interp (𝟙 _) ≫ (α_ _ _ _).inv) := by
          have := ssubst_single_interp He
          simp at this
          exact this
        exact (Part.map_some _ _).trans (congrArg Part.some (congrArg (· ≫ Φ_body) h_subst))

      rw [show Φ_interp = (lift e_interp (𝟙 _) ≫ (α_ _ _ _).inv) ≫ Φ_body from
        Part.some_injective (HΦ.symm.trans h_subst_interp)]
      exact elim_all Ψ_interp Φ_body
        (IH Ψ_interp (interp_forall Φ_body) HΨ (by simp [expr_interp, h_body_eq])) e_interp

  lemma soundness_exists_intro' {Γ' : OCTX.{i}} {Γs : CTX.{i}} {Ψ : PCTX.{i}} {τ : TYPE.{i}}
    {Φ : PROPOSITION.{i}} {e : EXPR.{i}}
    (He : TYPED (Γ' :: Γs) e τ) (h_body_typed : TYPED ((τ :: Γ') :: Γs) Φ TYPE.prop)
    (IH : ∀ (Ψ_interp : List (List (⟦Γ' :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ' :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ),
      interp_pctx Ψ = pure Ψ_interp →
      expr_interp (Γ' :: Γs) (binds (single_subst (List.map List.length (Γ' :: Γs)) e) Φ) TYPE.prop = pure Φ_interp →
      pctx Ψ_interp ⊢ᵢ Φ_interp)
    (Ψ_interp : List (List (⟦Γ' :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ' :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
    (HΨ : interp_pctx Ψ = pure Ψ_interp)
    (HΦ : expr_interp (Γ' :: Γs) (.exists' τ Φ) TYPE.prop = pure Φ_interp)
    : pctx Ψ_interp ⊢ᵢ Φ_interp := by
      set e_interp := (expr_interp (Γ' :: Γs) e τ).get (expr_interp_correct He)
      have h_e_eq : expr_interp (Γ' :: Γs) e τ = Part.some e_interp := by
        ext; simp [e_interp]
      set Φ_body := (expr_interp ((τ :: Γ') :: Γs) Φ TYPE.prop).get (expr_interp_correct h_body_typed)
      have h_body_eq : expr_interp ((τ :: Γ') :: Γs) Φ TYPE.prop = Part.some Φ_body := by
        ext; simp [Φ_body]
      have h_subst_interp : expr_interp (Γ' :: Γs) (binds (single_subst (List.map List.length (Γ' :: Γs)) e) Φ) TYPE.prop
          = Part.some ((lift e_interp (𝟙 _) ≫ (α_ _ _ _).inv) ≫ Φ_body) := by
        let h_tssubst := TSSUBST.single_subst He
        rw [show expr_interp (Γ' :: Γs) (binds (single_subst (List.map List.length (Γ' :: Γs)) e) Φ) TYPE.prop
            = (expr_interp ((τ :: Γ') :: Γs) Φ TYPE.prop).map (fun x => ⟦h_tssubst⟧ₛₛ ≫ x) by
          apply eq_bind; exact h_body_typed, h_body_eq]
        have h_subst : ⟦h_tssubst⟧ₛₛ = (lift e_interp (𝟙 _) ≫ (α_ _ _ _).inv) := by
          have := ssubst_single_interp He
          simp at this
          exact this
        exact (Part.map_some _ _).trans (congrArg Part.some (congrArg (· ≫ Φ_body) h_subst))
      rw [show Φ_interp = interp_exists Φ_body from
        Part.some_injective (HΦ.symm.trans (by simp [expr_interp, h_body_eq]))]
      exact intro_ex Ψ_interp Φ_body e_interp (IH Ψ_interp _ HΨ h_subst_interp)

  lemma soundness_forall_intro_points {Γ' : OCTX.{i}} {Γs : CTX.{i}} {Ψ : PCTX.{i}}
    {A : Type (imax i 0)} {Φ : PROPOSITION.{i}}
    (h_body_typed : TYPED ((TYPE.embed A :: Γ') :: Γs) Φ TYPE.prop)
    (IH : ∀ a : A, ∀ (Ψ_interp : List (List (⟦Γ' :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)))
        (Φ_interp : ⟦Γ' :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ),
      interp_pctx Ψ = pure Ψ_interp →
      expr_interp (Γ' :: Γs)
        (binds (single_subst (List.map List.length (Γ' :: Γs)) (EXPR.embed A a)) Φ) TYPE.prop
        = pure Φ_interp →
      pctx Ψ_interp ⊢ᵢ Φ_interp)
    (Ψ_interp : List (List (⟦Γ' :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)))
    (Φ_interp : ⟦Γ' :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
    (HΨ : interp_pctx Ψ = pure Ψ_interp)
    (HΦ : expr_interp (Γ' :: Γs) (.forall' (TYPE.embed A) Φ) TYPE.prop = pure Φ_interp)
    : pctx Ψ_interp ⊢ᵢ Φ_interp := by
      set Φ_body := (expr_interp ((TYPE.embed A :: Γ') :: Γs) Φ TYPE.prop).get
        (expr_interp_correct h_body_typed)
      have h_body_eq : expr_interp ((TYPE.embed A :: Γ') :: Γs) Φ TYPE.prop = Part.some Φ_body := by
        ext; simp [Φ_body]
      rw [show Φ_interp = interp_forall Φ_body from
        Part.some_injective (HΦ.symm.trans (by simp [expr_interp, h_body_eq]))]
      refine intro_all_points Ψ_interp Φ_body (fun a => ?_)
      have He : TYPED (Γ' :: Γs) (EXPR.embed A a) (TYPE.embed A) := TYPED.embed (by simp)
      have h_e_eq : expr_interp (Γ' :: Γs) (EXPR.embed A a) (TYPE.embed A)
          = Part.some (interp_embed A a) := by
        simp [expr_interp, Part.assert_pos]
      have h_subst_interp : expr_interp (Γ' :: Γs)
          (binds (single_subst (List.map List.length (Γ' :: Γs)) (EXPR.embed A a)) Φ) TYPE.prop
          = Part.some ((lift (interp_embed A a) (𝟙 _) ≫ (α_ _ _ _).inv) ≫ Φ_body) := by
        let h_tssubst := TSSUBST.single_subst He
        rw [show expr_interp (Γ' :: Γs)
            (binds (single_subst (List.map List.length (Γ' :: Γs)) (EXPR.embed A a)) Φ) TYPE.prop
            = (expr_interp ((TYPE.embed A :: Γ') :: Γs) Φ TYPE.prop).map
                (fun x => ⟦h_tssubst⟧ₛₛ ≫ x) by
          apply eq_bind; exact h_body_typed, h_body_eq]
        have h_subst : ⟦h_tssubst⟧ₛₛ
            = (lift (interp_embed A a) (𝟙 _) ≫ (α_ _ _ _).inv) := by
          have := ssubst_single_interp He
          simp at this
          exact this

        exact (Part.map_some _ _).trans (congrArg Part.some (congrArg (· ≫ Φ_body) h_subst))
      exact IH a Ψ_interp _ HΨ h_subst_interp

  lemma poctx_natural {Δ Γ : CTX.{i}} (Ψ : List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)) (δ : ⟦Δ⟧ₛ ⟶ ⟦Γ⟧ₛ)
      : δ ≫ poctx Ψ
        = poctx (List.map (fun Φ => δ ≫ Φ) Ψ) := by
    induction Ψ with
    | nil => rfl
    | cons y ys IH =>
      simp [poctx]
      erw [show δ ≫ y ∧ᵢ poctx ys
        = (δ ≫ y) ∧ᵢ (δ ≫ poctx ys) by rfl]
      erw [IH]

  lemma pctx_natural {Δ Γ : CTX.{i}} (Ψ : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (δ : ⟦Δ⟧ₛ ⟶ ⟦Γ⟧ₛ)
      : δ ≫ pctx Ψ
        = pctx (List.map (fun Ψ' => List.map (fun Φ => δ ≫ Φ) Ψ') Ψ) := by
    induction Ψ with
    | nil => rfl
    | cons x xs IH =>
      simp [pctx]
      erw [show δ ≫ poctx x ∧ᵢ pctx xs
        = (δ ≫ poctx x) ∧ᵢ (δ ≫ pctx xs) by rfl]
      erw [IH, poctx_natural]

  lemma interp_poctx_at_cons_decomp {Γ : CTX.{i}} {d : Nat} {Φ : EXPR.{i}} {Ψs : POCTX.{i}}
      {Ψ_interp : List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)}
      (H : interp_poctx_at d (Φ :: Ψs) = Pure.pure Ψ_interp)
      : ∃ (Φ' : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ) (Ψs' : List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)),
        expr_interp Γ (weaken Φ (REN.global_shift d REN.id)) TYPE.prop = Pure.pure Φ' ∧
        interp_poctx_at d Ψs = Pure.pure Ψs' ∧
        Ψ_interp = Φ' :: Ψs' := by
    simp only [interp_poctx_at] at H
    obtain ⟨Φ', hΦ', Ψs', hΨs', heq⟩ : ∃ Φ' Ψs',
        expr_interp Γ (weaken Φ (REN.global_shift d REN.id)) TYPE.prop = Part.some Φ' ∧
        interp_poctx_at d Ψs = Part.some Ψs' ∧
        Ψ_interp = Φ' :: Ψs' := by
      rw [show (do let Φ' ← expr_interp Γ (weaken Φ (REN.global_shift d REN.id)) TYPE.prop
                   let Ψs' ← interp_poctx_at d Ψs; pure (Φ' :: Ψs'))
               = (expr_interp Γ (weaken Φ (REN.global_shift d REN.id)) TYPE.prop).bind
                   (fun Φ' => (interp_poctx_at d Ψs).bind (fun Ψs' => Part.some (Φ' :: Ψs'))) by rfl] at H
      simp only [Part.bind_some_eq_map, Part.pure_eq_some] at H
      revert H
      cases (expr_interp Γ (weaken Φ (REN.global_shift d REN.id)) TYPE.prop) using Part.induction_on with
      | hnone => simp
      | hsome a =>
        simp only [Part.bind_some, Part.some_inj, exists_and_left, exists_eq_left']
        cases (interp_poctx_at d Ψs) using Part.induction_on with
        | hnone => simp
        | hsome as =>
          simp only [Part.map_some, Part.some_inj, exists_eq_left']; intro H; symm; exact H
    exact ⟨Φ', hΦ', Ψs', hΨs', heq⟩

  lemma id_comp_equiv (σ : REN) : REN.equiv (REN.comp REN.id σ) σ := by
    refine ⟨fun n m => ?_, fun n => ?_⟩
    · simp only [weaken_var']
    · cases n with
      | zero => simp [offset_ren]
      | succ n => simp only [offset_ren]

  lemma comp_global_shift_succ_octx_wk_equiv (d : Nat) :
      REN.equiv (REN.comp (REN.global_shift (d + 1) REN.id) octx_wk)
                (REN.global_shift (d + 1) REN.id) := by
    have h1 := asm_nat (d + 1) octx_wk
    simp only [octx_wk] at h1

    rw [show cut_ren (REN.local_weaken REN.id) (d + 1) = REN.id by simp [cut_ren],
      show offset_ren (REN.local_weaken REN.id) (d + 1) = d + 1 by simp [offset_ren]] at h1
    exact REN.equiv.trans h1 (id_comp_equiv _)

  lemma expr_octx_wk_tail {Γ : OCTX.{i}} {Γs : CTX.{i}} {τ : TYPE.{i}} (d : Nat) {Φ : EXPR.{i}}
      (Hσ : TYPED_REN octx_wk ((τ :: Γ) :: Γs) (Γ :: Γs))
      (HΦ : TYPED ((Γ :: Γs).drop (d + 1)) Φ TYPE.prop) :
      expr_interp ((τ :: Γ) :: Γs) (weaken Φ (REN.global_shift (d + 1) REN.id)) TYPE.prop
      = (expr_interp (Γ :: Γs) (weaken Φ (REN.global_shift (d + 1) REN.id)) TYPE.prop).map
          (fun b => ⟦Hσ⟧ᵣ ≫ b) := by
    have key := eq_weak (Γ :: Γs) (weaken Φ (REN.global_shift (d + 1) REN.id)) TYPE.prop Hσ
      (weaken_typing HΦ (global_shift_id_typing (Γ :: Γs) (d + 1)
        (by have h := typing_stack_len HΦ; rw [List.length_drop] at h; omega)))
    rw [weaken_comp, weaken_congr Φ (comp_global_shift_succ_octx_wk_equiv d)] at key
    exact key

  lemma interp_poctx_at_octx_wk_tail {Γ : OCTX.{i}} {Γs : CTX.{i}} {τ : TYPE.{i}} (d : Nat)
      (Hσ : TYPED_REN octx_wk ((τ :: Γ) :: Γs) (Γ :: Γs))
      (Ψf : POCTX.{i}) (v : List (⟦Γ :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))
      (Hwt : ∀ (m : Nat) (Φ : EXPR.{i}), Ψf[m]? = some Φ → TYPED ((Γ :: Γs).drop (d + 1)) Φ TYPE.prop)
      (Hv : interp_poctx_at (d + 1) Ψf = pure v) :
      interp_poctx_at (d + 1) Ψf (Γ := (τ :: Γ) :: Γs)
        = pure (v.map (fun b => ⟦Hσ⟧ᵣ ≫ b)) := by
    induction Ψf generalizing v with
    | nil =>
      obtain rfl : v = [] := by simpa [interp_poctx_at] using Hv.symm
      simp [interp_poctx_at]
    | cons Φ rest IH =>
      obtain ⟨Φ', rest', hΦ', hrest, heq⟩ := interp_poctx_at_cons_decomp Hv
      have hΦadv : expr_interp ((τ :: Γ) :: Γs) (weaken Φ (REN.global_shift (d + 1) REN.id)) TYPE.prop
          = pure (⟦Hσ⟧ᵣ ≫ Φ') := by
        rw [expr_octx_wk_tail d Hσ (Hwt 0 Φ (by simp)), hΦ']; rfl
      have hrestadv := IH rest' (fun m Φ'' h => Hwt (m + 1) Φ'' (by simpa using h)) hrest
      rw [heq]
      simp only [interp_poctx_at, hΦadv, hrestadv, List.map_cons, pure_bind]

  lemma interp_poctx_at_octx_wk_zero {Γ : OCTX.{i}} {Γs : CTX.{i}} {τ : TYPE.{i}}
      (Hσ : TYPED_REN octx_wk ((τ :: Γ) :: Γs) (Γ :: Γs))
      (Ψf : POCTX.{i}) (v : List (⟦Γ :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))
      (Hwt : ∀ (m : Nat) (Φ : EXPR.{i}), Ψf[m]? = some Φ → TYPED (Γ :: Γs) Φ TYPE.prop)
      (Hv : interp_poctx_at 0 Ψf = pure v) :
      interp_poctx_at 0 (Ψf.map (fun Φ => weaken Φ octx_wk)) (Γ := (τ :: Γ) :: Γs)
        = pure (v.map (fun b => ⟦Hσ⟧ᵣ ≫ b)) := by
    induction Ψf generalizing v with
    | nil =>
      obtain rfl : v = [] := by simpa [interp_poctx_at] using Hv.symm
      simp [interp_poctx_at]
    | cons Φ rest IH =>
      obtain ⟨Φ', rest', hΦ', hrest, heq⟩ := interp_poctx_at_cons_decomp Hv
      have hΦadv : expr_interp ((τ :: Γ) :: Γs)
          (weaken (weaken Φ octx_wk) (REN.global_shift 0 REN.id)) TYPE.prop
          = pure (⟦Hσ⟧ᵣ ≫ Φ') := by
        rw [weaken_global_shift_zero_id]
        rw [eq_weak (Γ :: Γs) Φ TYPE.prop Hσ (Hwt 0 Φ (by simp))]
        rw [show expr_interp (Γ :: Γs) (weaken Φ (REN.global_shift 0 REN.id)) TYPE.prop
              = expr_interp (Γ :: Γs) Φ TYPE.prop by rw [weaken_global_shift_zero_id]] at hΦ'
        rw [hΦ']; rfl
      have hrestadv := IH rest' (fun m Φ'' h => Hwt (m + 1) Φ'' (by simpa using h)) hrest
      rw [heq]
      simp only [List.map_cons, interp_poctx_at, hΦadv, hrestadv, pure_bind]

  lemma interp_pctx_intro_wrap {Γ : OCTX.{i}} {Γs : CTX.{i}} {τ : TYPE.{i}} (Ψ : PCTX.{i})
      (Hσ : TYPED_REN octx_wk ((τ :: Γ) :: Γs) (Γ :: Γs))
      (V : List (List (⟦Γ :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)))
      (Hwt : ctx_typed (Γ :: Γs) Ψ)
      (HV : interp_pctx Ψ = pure V) :
      interp_pctx (intro_wrap Ψ) (Γ := (τ :: Γ) :: Γs)
        = pure (V.map (fun frame => frame.map (fun b => ⟦Hσ⟧ᵣ ≫ b))) := by
    cases Ψ with
    | nil =>
      obtain rfl : V = [] := by simpa [interp_pctx, interp_pctx_at] using HV.symm
      simp [intro_wrap, interp_pctx, interp_pctx_at]
    | cons Ψf Ψrest =>
      obtain ⟨f', rest', hf', hrest, heq⟩ := interp_pctx_cons_decomp HV
      have hf0 : interp_poctx_at 0 (Ψf.map (fun Φ => weaken Φ octx_wk)) (Γ := (τ :: Γ) :: Γs)
          = pure (f'.map (fun b => ⟦Hσ⟧ᵣ ≫ b)) :=
        interp_poctx_at_octx_wk_zero Hσ Ψf f'
          (fun m Φ h => by
            have := Hwt 0 m Ψf Φ (by simp) h
            simpa using this) hf'
      have hrestadv : interp_pctx_at 1 Ψrest (Γ := (τ :: Γ) :: Γs)
          = pure (rest'.map (fun frame => frame.map (fun b => ⟦Hσ⟧ᵣ ≫ b))) := by
        clear heq hf' hf0
        suffices H : ∀ (d : Nat) (Ψtail : PCTX.{i}) (W : List (List (⟦Γ :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))),
            (∀ (n m : Nat) (Ψ' : POCTX.{i}) (Φ : EXPR.{i}),
              Ψtail[n]? = some Ψ' → Ψ'[m]? = some Φ → TYPED ((Γ :: Γs).drop (d + 1 + n)) Φ TYPE.prop) →
            interp_pctx_at (d + 1) Ψtail = pure W →
            interp_pctx_at (d + 1) Ψtail (Γ := (τ :: Γ) :: Γs)
              = pure (W.map (fun frame => frame.map (fun b => ⟦Hσ⟧ᵣ ≫ b))) by
          exact H 0 Ψrest rest'
            (fun n m Ψ' Φ hn hm => by
              have := Hwt (n + 1) m Ψ' Φ (by simpa using hn) hm
              simpa [Nat.add_comm, Nat.add_left_comm] using this)
            hrest
        intro d Ψtail
        induction Ψtail generalizing d with
        | nil =>
          intro W _ HW
          obtain rfl : W = [] := by simpa [interp_pctx_at] using HW.symm
          simp [interp_pctx_at]
        | cons Ψg Ψgs IH =>
          intro W Hwt' HW
          obtain ⟨g', gs', hg', hgs, geq⟩ := interp_pctx_at_cons_decomp HW
          have hgadv : interp_poctx_at (d + 1) Ψg (Γ := (τ :: Γ) :: Γs)
              = pure (g'.map (fun b => ⟦Hσ⟧ᵣ ≫ b)) :=
            interp_poctx_at_octx_wk_tail d Hσ Ψg g'
              (fun m Φ h => by
                have := Hwt' 0 m Ψg Φ (by simp) h
                simpa using this) hg'
          have hgsadv := IH (d + 1) gs'
            (fun n m Ψ' Φ hn hm => by
              have := Hwt' (n + 1) m Ψ' Φ (by simpa using hn) hm
              have he : d + 1 + (n + 1) = d + 1 + 1 + n := by omega
              rwa [he] at this)
            hgs
          rw [geq]
          simp only [interp_pctx_at, hgadv, hgsadv, List.map_cons, pure_bind]
      rw [heq]
      simp only [intro_wrap, intro_wrap', interp_pctx, interp_pctx_at, hf0, hrestadv,
        List.map_cons, pure_bind]

  lemma ctx_typed_intro_wrap {Γ : OCTX.{i}} {Γs : CTX.{i}} {τ : TYPE.{i}} {Ψ : PCTX.{i}}
      (Hσ : TYPED_REN octx_wk ((τ :: Γ) :: Γs) (Γ :: Γs))
      (Hwf : ctx_typed (Γ :: Γs) Ψ) :
      ctx_typed ((τ :: Γ) :: Γs) (intro_wrap Ψ) := by
    cases Ψ with
    | nil => intro n m Ψ' Φ Hn _; cases n <;> simp at Hn
    | cons Ψf Ψrest =>
      intro n m Ψ' Φ Hn Hm
      cases n with
      | zero =>
        simp only [intro_wrap, intro_wrap', List.getElem?_cons_zero, Option.some.injEq] at Hn
        subst Hn
        rw [List.getElem?_map] at Hm
        obtain ⟨Φ0, hΦ0, rfl⟩ : ∃ Φ0, Ψf[m]? = some Φ0 ∧ weaken Φ0 octx_wk = Φ := by
          rcases h : Ψf[m]? with _ | Φ0
          · simp [h] at Hm
          · exact ⟨Φ0, rfl, by simpa [h] using Hm⟩
        simpa using weaken_typing (Hwf 0 m Ψf Φ0 (by simp) hΦ0) Hσ
      | succ n' =>
        simp only [intro_wrap, intro_wrap', List.getElem?_cons_succ] at Hn
        simpa [List.drop_succ_cons] using Hwf (n' + 1) m Ψ' Φ (by simpa using Hn) Hm

  lemma soundness_forall_intro' {Γ : OCTX.{i}} {Γs : CTX.{i}} {Ψ : PCTX.{i}} {τ : TYPE.{i}} {Φ : PROPOSITION.{i}}
    (H : PROVES ((τ :: Γ) :: Γs) (intro_wrap Ψ) Φ)
    (Hwf : ctx_typed (Γ :: Γs) Ψ)
    (IH : ctx_typed ((τ :: Γ) :: Γs) (intro_wrap Ψ) →
      ∀ (Ψ_interp : List (List (⟦(τ :: Γ) :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦(τ :: Γ) :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ),
      interp_pctx (intro_wrap Ψ) = pure Ψ_interp →
      expr_interp ((τ :: Γ) :: Γs) Φ TYPE.prop = pure Φ_interp → pctx Ψ_interp ⊢ᵢ Φ_interp)
    (Ψ_interp : List (List (⟦Γ :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
    (HΨ : interp_pctx Ψ = pure Ψ_interp)
    (HΦ : expr_interp (Γ :: Γs) (.forall' τ Φ) TYPE.prop = pure Φ_interp)
    : pctx Ψ_interp ⊢ᵢ Φ_interp := by

    set Φ_body := (expr_interp ((τ :: Γ) :: Γs) Φ TYPE.prop).get (expr_interp_correct (PROVES.typed H))

    have h_body_eq : expr_interp ((τ :: Γ) :: Γs) Φ TYPE.prop = Part.some Φ_body := by
      ext; simp [Φ_body]

    rw [show Φ_interp = interp_forall Φ_body from
      Part.some_injective (HΦ.symm.trans (by simp [expr_interp, h_body_eq]))]
    apply intro_all
    set Hσ : TYPED_REN octx_wk ((τ :: Γ) :: Γs) (Γ :: Γs) :=
      TYPED_REN.local_weaken τ (TYPED_REN.id (by simp : 0 < (Γ :: Γs).length)) with hHσ_def
    have h_ren_eq : ⟦Hσ⟧ᵣ = interp_ren_local_weaken (τ := τ) interp_ren_id := by
      simp only [hHσ_def, interp_typed_ren, interp_ren_id]
    apply entails_trans; swap
    . apply IH (ctx_typed_intro_wrap Hσ Hwf)
        (Ψ_interp.map (fun Ψ' => Ψ'.map (fun Φ => ⟦Hσ⟧ᵣ ≫ Φ))) Φ_body _ h_body_eq
      exact interp_pctx_intro_wrap Ψ Hσ Ψ_interp Hwf HΨ
    . erw [h_ren_eq, pctx_natural]
      apply entails_refl

  lemma weaken_global_shift_succ (Φ : EXPR.{i}) (m : Nat) :
      weaken Φ (REN.global_shift (m + 1) REN.id)
      = weaken (weaken Φ (REN.global_shift m REN.id)) (REN.global_shift 1 REN.id) := by
    rw [weaken_comp, weaken_congr Φ (global_shift_comp_equiv m 1), Nat.add_comm 1 m]

  lemma global_shift_split_eq {C C' : CTX.{i}} {p p' : Nat} (hC : C = C') (hp : p = p')
      (h1 : ⟦C'⟧ₛ = ⟦C⟧ₛ)
      (h2 : ⟦C.drop p⟧ₛ = ⟦C'.drop p'⟧ₛ) :
      eqToHom h1 ≫ (interp_ctx_split C (i := p)).hom
          ≫ fst ((earlier.iter p).obj ⟦C.drop p⟧ₛ) ⟦C.take p⟧ₛ
          ≫ (n_force (i := p)).app ⟦C.drop p⟧ₛ ≫ eqToHom h2
        = (interp_ctx_split C' (i := p')).hom
          ≫ fst ((earlier.iter p').obj ⟦C'.drop p'⟧ₛ) ⟦C'.take p'⟧ₛ
          ≫ (n_force (i := p')).app ⟦C'.drop p'⟧ₛ := by
    subst hC; subst hp; simp

  lemma global_shift_id_interp (Γ : CTX.{i}) (n : Nat) (Hlt : n < Γ.length) :
      ⟦global_shift_id_typing Γ n Hlt⟧ᵣ = (interp_ctx_split Γ (i := n)).hom
        ≫ fst ((earlier.iter n).obj ⟦Γ.drop n⟧ₛ) ⟦Γ.take n⟧ₛ
        ≫ (n_force (i := n)).app ⟦Γ.drop n⟧ₛ := by
    have hlen' : n = (Γ.take n).length := by rw [List.length_take]; omega
    have hpos : 0 < (Γ.drop n).length := by rw [List.length_drop]; omega
    have heq : global_shift_id_typing Γ n Hlt
        = ren_transport_left (List.take_append_drop n Γ)
            (TYPED_REN.global_shift n hlen' (TYPED_REN.id hpos)) := rfl
    rw [heq, ren_transport_left_sem]
    simp only [interp_typed_ren, interp_ren_global_shift, interp_ren_id, Category.comp_id]
    exact global_shift_split_eq (List.take_append_drop n Γ) hlen'.symm _ _

  lemma global_shift_one_id_interp (Γ : CTX.{i}) (ha : (1:Nat) < ([] :: Γ).length) :
      ⟦global_shift_id_typing ([] :: Γ) 1 ha⟧ᵣ =
        (λ_ (earlier.obj ⟦Γ⟧ₛ)).hom ≫ force.app ⟦Γ⟧ₛ := by
    rw [global_shift_id_interp]
    simp [interp_ctx_split, n_force]
    change
      (((𝟙_ ℐ) ◁ earlier.map (ρ_ ⟦Γ⟧ₛ).inv ≫
              (𝟙_ ℐ) ◁ earlier_prod.hom.app (⟦Γ⟧ₛ, 𝟙_ ℐ))
            ≫ (α_ (𝟙_ ℐ) (earlier.obj ⟦Γ⟧ₛ) (earlier.obj (𝟙_ ℐ))).inv
            ≫ (β_ (𝟙_ ℐ) (earlier.obj ⟦Γ⟧ₛ)).hom ▷ earlier.obj (𝟙_ ℐ)
            ≫ (α_ (earlier.obj ⟦Γ⟧ₛ) (𝟙_ ℐ) (earlier.obj (𝟙_ ℐ))).hom
            ≫ fst (earlier.obj ⟦Γ⟧ₛ) ((𝟙_ ℐ) ⊗ earlier.obj (𝟙_ ℐ))
            ≫ force.app ⟦Γ⟧ₛ)
        = (λ_ (earlier.obj ⟦Γ⟧ₛ)).hom ≫ force.app ⟦Γ⟧ₛ
    have h := snd_force_chase (X := (𝟙_ ℐ)) (ρ_ ⟦Γ⟧ₛ).inv (𝟙 ⟦Γ⟧ₛ)
    rw [← leftUnitor_hom] at h
    simpa using h

  lemma expr_advance {Γ : CTX.{i}} {d : Nat} (Hd : d < Γ.length) {Φ : EXPR.{i}}
      (HΦ : TYPED (Γ.drop d) Φ TYPE.prop) :
      expr_interp ([] :: Γ) (weaken Φ (REN.global_shift (d + 1) REN.id)) TYPE.prop
      = (expr_interp Γ (weaken Φ (REN.global_shift d REN.id)) TYPE.prop).map
          (fun b => ((λ_ (earlier.obj ⟦Γ⟧ₛ)).hom ≫ force.app ⟦Γ⟧ₛ) ≫ b) := by
    have ha1 : (1 : Nat) < ([] :: Γ).length := by simp only [List.length_cons]; omega
    have key := eq_weak Γ (weaken Φ (REN.global_shift d REN.id)) TYPE.prop
        (global_shift_id_typing ([] :: Γ) 1 ha1) (weaken_typing HΦ (global_shift_id_typing Γ d Hd))
    erw [global_shift_one_id_interp Γ ha1] at key
    rw [weaken_global_shift_succ Φ d]
    exact key

  lemma interp_poctx_at_advance {Γ : CTX.{i}} (d : Nat) (Hd : d < Γ.length)
      (Ψf : POCTX.{i}) (v : List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))
      (Hwt : ∀ (m : Nat) (Φ : EXPR.{i}), Ψf[m]? = some Φ → TYPED (Γ.drop d) Φ TYPE.prop)
      (Hv : interp_poctx_at d Ψf = pure v) :
      interp_poctx_at (d + 1) Ψf (Γ := [] :: Γ)
        = pure (v.map (fun b => ((λ_ (earlier.obj ⟦Γ⟧ₛ)).hom ≫ force.app ⟦Γ⟧ₛ) ≫ b)) := by
    induction Ψf generalizing v with
    | nil =>
      obtain rfl : v = [] := by simpa [interp_poctx_at] using Hv.symm
      simp [interp_poctx_at]
    | cons Φ rest IH =>
      obtain ⟨Φ', rest', hΦ', hrest, heq⟩ := interp_poctx_at_cons_decomp Hv
      have hΦadv : expr_interp ([] :: Γ) (weaken Φ (REN.global_shift (d + 1) REN.id)) TYPE.prop
          = pure (((λ_ (earlier.obj ⟦Γ⟧ₛ)).hom ≫ force.app ⟦Γ⟧ₛ) ≫ Φ') := by
        rw [expr_advance Hd (Hwt 0 Φ (by simp)), hΦ']; rfl
      have hrestadv := IH rest' (fun m Φ'' h => Hwt (m + 1) Φ'' (by simpa using h)) hrest
      rw [heq]
      simp only [interp_poctx_at, hΦadv, hrestadv]
      exact (Part.bind_some _ _).trans (Part.bind_some _ _)

  lemma interp_pctx_at_advance {Γ : CTX.{i}} (d : Nat)
      (Ψ : PCTX.{i}) (V : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)))
      (Hlen : d + Ψ.length ≤ Γ.length)
      (Hwt : ∀ (n m : Nat) (Ψ' : POCTX.{i}) (Φ : EXPR.{i}),
        Ψ[n]? = some Ψ' → Ψ'[m]? = some Φ → TYPED (Γ.drop (d + n)) Φ TYPE.prop)
      (HV : interp_pctx_at d Ψ = pure V) :
      interp_pctx_at (d + 1) Ψ (Γ := [] :: Γ)
        = pure (V.map (fun frame =>
            frame.map (fun b => ((λ_ (earlier.obj ⟦Γ⟧ₛ)).hom ≫ force.app ⟦Γ⟧ₛ) ≫ b))) := by
    induction Ψ generalizing d V with
    | nil =>
      obtain rfl : V = [] := by simpa [interp_pctx_at] using HV.symm
      simp [interp_pctx_at]
    | cons Ψf Ψrest IH =>
      obtain ⟨f', rest', hf', hrest, heq⟩ := interp_pctx_at_cons_decomp HV
      have hfadv : interp_poctx_at (d + 1) Ψf (Γ := [] :: Γ)
          = pure (f'.map (fun b => ((λ_ (earlier.obj ⟦Γ⟧ₛ)).hom ≫ force.app ⟦Γ⟧ₛ) ≫ b)) :=
        interp_poctx_at_advance d (by simp only [List.length_cons] at Hlen; omega) Ψf f'
          (fun m Φ h => by simpa using Hwt 0 m Ψf Φ (by simp) h) hf'
      have hrestadv := IH (d + 1) rest'
        (by simp only [List.length_cons] at Hlen; omega)
        (fun n m Ψ' Φ hn hm => by
          have h := Hwt (n + 1) m Ψ' Φ (by simpa using hn) hm
          have he : d + (n + 1) = (d + 1) + n := by omega
          rwa [he] at h)
        hrest
      rw [heq]
      simp only [interp_pctx_at, hfadv, hrestadv, List.map_cons]
      exact (Part.bind_some _ _).trans (Part.bind_some _ _)

  lemma poctx_map_postcomp {Γ : CTX.{i}} {Δ : CTX.{i}} (g : ⟦Δ⟧ₛ ⟶ ⟦Γ⟧ₛ)
      (Ψ : List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)) :
      poctx (Ψ.map (fun b => g ≫ b)) = g ≫ poctx Ψ := by
    induction Ψ with
    | nil =>
      simp only [List.map_nil, poctx, Logic.true]
      erw [← Category.assoc]; congr 1
    | cons a as IH =>
      simp only [List.map_cons, poctx, IH, Logic.conj]
      rfl

  lemma pctx_map_postcomp {Γ : CTX.{i}} {Δ : CTX.{i}} (g : ⟦Δ⟧ₛ ⟶ ⟦Γ⟧ₛ)
      (Ψ : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) :
      pctx (Ψ.map (fun a => a.map (fun b => g ≫ b))) = g ≫ pctx Ψ := by
    induction Ψ with
    | nil =>
      simp only [List.map_nil, pctx, Logic.true]
      erw [← Category.assoc]; congr 1
    | cons a as IH =>
      simp only [List.map_cons, pctx, poctx_map_postcomp, IH, Logic.conj]
      rfl

  lemma soundness_lift_intro {Γ : CTX.{i}} {Ψ : PCTX.{i}} {Φ : PROPOSITION.{i}}
    (_Hlen : 0 < Γ.length) (H : PROVES ([] :: Γ) ([] :: Ψ) Φ)
    (IH : ctx_typed ([] :: Γ) ([] :: Ψ) →
      ∀ (Ψ_interp : List (List (⟦[] :: Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦[] :: Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ),
      interp_pctx ([] :: Ψ) = pure Ψ_interp → expr_interp ([] :: Γ) Φ TYPE.prop = pure Φ_interp → pctx Ψ_interp ⊢ᵢ Φ_interp)
    (Hwf : ctx_typed Γ Ψ)
    (Ψ_interp : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
    (HΨ : interp_pctx Ψ = pure Ψ_interp)
    (HΦ : expr_interp Γ (.lift (.delay Φ)) TYPE.prop = pure Φ_interp)
    : pctx Ψ_interp ⊢ᵢ Φ_interp := by

    set Φ_ext := (expr_interp ([] :: Γ) Φ TYPE.prop).get (expr_interp_correct (PROVES.typed H))

    rw [show Φ_interp = interp_lift (interp_delay Φ_ext) by
      have h_ext_eq : expr_interp ([] :: Γ) Φ TYPE.prop = Part.some Φ_ext := by
        ext; simp [Φ_ext]
      simp [expr_interp, h_ext_eq] at HΦ
      exact HΦ.symm]
    refine entails_trans _ _ _ (later_intro (pctx Ψ_interp)) (later_mono ?_)
    rw [← Category.assoc]
    have key := interp_pctx_at_advance 0 Ψ Ψ_interp
      (by have := PROVES.len H; simp only [List.length_cons] at this; omega)
      (fun n m Ψ' Φ' hn hm => by simpa using Hwf n m Ψ' Φ' hn hm) HΨ
    simp only [Nat.zero_add] at key
    have hadv : interp_pctx ([] :: Ψ) (Γ := [] :: Γ)
        = pure ([] :: Ψ_interp.map (fun frame =>
            frame.map (fun b => ((λ_ (earlier.obj ⟦Γ⟧ₛ)).hom ≫ force.app ⟦Γ⟧ₛ) ≫ b))) := by
      simp only [interp_pctx, interp_pctx_at, interp_poctx_at, key, pure_bind]
    have hih := IH (ctx_typed_lift Hwf) _ Φ_ext hadv (by ext; simp [Φ_ext])
    simp only [pctx, poctx] at hih
    erw [← pctx_map_postcomp (Γ := Γ) (Δ := [] :: Γ)
        ((λ_ (earlier.obj ⟦Γ⟧ₛ)).hom ≫ force.app ⟦Γ⟧ₛ) Ψ_interp]
    exact entails_trans _ _ _ (conj_intro true_intro (entails_refl _)) hih

  lemma expr_drop_shift {Γ : CTX.{i}} {n j : Nat} (hn' : n < Γ.length)
      (Hd : n + j < Γ.length) {Φ : EXPR.{i}}
      (HΦ : TYPED (Γ.drop (n + j)) Φ TYPE.prop) :
      expr_interp Γ (weaken Φ (REN.global_shift (n + j) REN.id)) TYPE.prop
      = (expr_interp (Γ.drop n) (weaken Φ (REN.global_shift j REN.id)) TYPE.prop).map
          (fun b => ⟦global_shift_id_typing Γ n hn'⟧ᵣ ≫ b) := by
    have HΦin : TYPED (Γ.drop n) (weaken Φ (REN.global_shift j REN.id)) TYPE.prop := by
      apply weaken_typing _ (global_shift_id_typing (Γ.drop n) j (by rw [List.length_drop]; omega))
      rw [show (Γ.drop n).drop j = Γ.drop (n + j) by rw [List.drop_drop, Nat.add_comm]]; exact HΦ
    have key := eq_weak (Γ.drop n) (weaken Φ (REN.global_shift j REN.id)) TYPE.prop
        (global_shift_id_typing Γ n hn') HΦin
    rw [weaken_comp, weaken_congr Φ (global_shift_comp_equiv j n)] at key
    exact key

  lemma interp_poctx_at_drop_shift {Γ : CTX.{i}} (n j : Nat) (hn' : n < Γ.length)
      (Ψf : POCTX.{i}) (v : List (⟦Γ.drop n⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))
      (Hwt : ∀ (m : Nat) (Φ : EXPR.{i}), Ψf[m]? = some Φ → TYPED ((Γ.drop n).drop j) Φ TYPE.prop)
      (Hdj : n + j < Γ.length)
      (Hv : interp_poctx_at j Ψf (Γ := Γ.drop n) = pure v) :
      interp_poctx_at (n + j) Ψf (Γ := Γ)
        = pure (v.map (fun b => ⟦global_shift_id_typing Γ n hn'⟧ᵣ ≫ b)) := by
    induction Ψf generalizing v with
    | nil =>
      obtain rfl : v = [] := by simpa [interp_poctx_at] using Hv.symm
      simp [interp_poctx_at]
    | cons Φ rest IH =>
      obtain ⟨Φ', rest', hΦ', hrest, heq⟩ := interp_poctx_at_cons_decomp Hv
      have hΦty : TYPED (Γ.drop (n + j)) Φ TYPE.prop := by
        have := Hwt 0 Φ (by simp)
        rw [List.drop_drop] at this; exact this
      have hΦadv : expr_interp Γ (weaken Φ (REN.global_shift (n + j) REN.id)) TYPE.prop
          = pure (⟦global_shift_id_typing Γ n hn'⟧ᵣ ≫ Φ') := by
        rw [expr_drop_shift hn' Hdj hΦty, hΦ']; rfl
      have hrestadv := IH rest' (fun m Φ'' h => Hwt (m + 1) Φ'' (by simpa using h)) hrest
      rw [heq]
      simp only [interp_poctx_at, hΦadv, hrestadv, List.map_cons, pure_bind]

  lemma interp_pctx_at_drop_shift {Γ : CTX.{i}} (n : Nat) (hn' : n < Γ.length)
      (Ψ : PCTX.{i}) (V : List (List (⟦Γ.drop n⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)))
      (Hlen : n + Ψ.length ≤ Γ.length)
      (Hwt : ctx_typed (Γ.drop n) Ψ)
      (HV : interp_pctx_at 0 Ψ (Γ := Γ.drop n) = pure V) :
      interp_pctx_at n Ψ (Γ := Γ)
        = pure (V.map (fun frame =>
            frame.map (fun b => ⟦global_shift_id_typing Γ n hn'⟧ᵣ ≫ b))) := by
    suffices H : ∀ (d : Nat) (Ψtail : PCTX.{i}) (W : List (List (⟦Γ.drop n⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))),
        n + d + Ψtail.length ≤ Γ.length →
        (∀ (k m : Nat) (Ψ' : POCTX.{i}) (Φ : EXPR.{i}),
          Ψtail[k]? = some Ψ' → Ψ'[m]? = some Φ →
            TYPED ((Γ.drop n).drop (d + k)) Φ TYPE.prop) →
        interp_pctx_at d Ψtail (Γ := Γ.drop n) = pure W →
        interp_pctx_at (n + d) Ψtail (Γ := Γ)
          = pure (W.map (fun frame =>
              frame.map (fun b => ⟦global_shift_id_typing Γ n hn'⟧ᵣ ≫ b))) by
      have := H 0 Ψ V (by simpa using Hlen)
        (fun k m Ψ' Φ hk hm => by simpa using Hwt k m Ψ' Φ hk hm) HV
      simpa using this
    intro d Ψtail
    induction Ψtail generalizing d with
    | nil =>
      intro W _ _ HW
      obtain rfl : W = [] := by simpa [interp_pctx_at] using HW.symm
      simp [interp_pctx_at]
    | cons Ψf Ψrest IH =>
      intro W Hlen' Hwt' HW
      obtain ⟨f', rest', hf', hrest, heq⟩ := interp_pctx_at_cons_decomp HW
      have hfadv : interp_poctx_at (n + d) Ψf (Γ := Γ)
          = pure (f'.map (fun b => ⟦global_shift_id_typing Γ n hn'⟧ᵣ ≫ b)) := by
        by_cases hf0 : Ψf = []
        · subst hf0
          obtain rfl : f' = [] := by simpa [interp_poctx_at] using hf'.symm
          simp [interp_poctx_at]
        · exact interp_poctx_at_drop_shift n d hn' Ψf f'
            (fun m Φ h => by
              have := Hwt' 0 m (Ψf) Φ (by simp) h
              rwa [Nat.add_zero] at this)
            (by simp only [List.length_cons] at Hlen'
                have : 0 < Ψf.length := List.length_pos_of_ne_nil hf0
                omega) hf'
      have hrestadv := IH (d + 1) rest'
        (by simp only [List.length_cons] at Hlen'; omega)
        (fun k m Ψ' Φ hk hm => by
          have := Hwt' (k + 1) m Ψ' Φ hk hm
          have he : d + (k + 1) = d + 1 + k := by omega
          rwa [he] at this)
        hrest
      rw [show n + (d + 1) = (n + d) + 1 from by omega] at hrestadv
      rw [heq]
      simp only [interp_pctx_at, hfadv, hrestadv, List.map_cons, pure_bind]

  lemma interp_pctx_at_drop_gen {Γ : CTX.{i}} (b n : Nat) (Ψ : PCTX.{i})
      (V : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)))
      (HV : interp_pctx_at b Ψ (Γ := Γ) = pure V) :
      interp_pctx_at (b + n) (Ψ.drop n) (Γ := Γ) = pure (V.drop n) := by
    induction n generalizing b Ψ V with
    | zero => simpa using HV
    | succ n' IH =>
      cases Ψ with
      | nil =>
        obtain rfl : V = [] := by simpa [interp_pctx_at] using HV.symm
        simp [interp_pctx_at]
      | cons Ψf Ψrest =>
        obtain ⟨f', rest', hf', hrest, heq⟩ := interp_pctx_at_cons_decomp HV
        subst heq
        simp only [List.drop]
        have h := IH (b + 1) Ψrest rest' hrest
        rwa [show b + (n' + 1) = (b + 1) + n' from by omega]

  lemma interp_pctx_at_drop {Γ : CTX.{i}} (n : Nat) (Ψ : PCTX.{i})
      (V : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)))
      (HV : interp_pctx_at 0 Ψ (Γ := Γ) = pure V) :
      interp_pctx_at n (Ψ.drop n) (Γ := Γ) = pure (V.drop n) := by
    have := interp_pctx_at_drop_gen 0 n Ψ V HV
    simpa using this

  lemma interp_poctx_at_dom {Γ : CTX.{i}} (d : Nat) (Ψf : POCTX.{i})
      (Hlen : d < Γ.length)
      (Hwt : ∀ (m : Nat) (Φ : EXPR.{i}), Ψf[m]? = some Φ → TYPED (Γ.drop d) Φ TYPE.prop) :
      (interp_poctx_at d Ψf (Γ := Γ)).Dom := by
    induction Ψf with
    | nil => simp [interp_poctx_at]
    | cons Φ rest IH =>
      have hΦw : (expr_interp Γ (weaken Φ (REN.global_shift d REN.id)) TYPE.prop).Dom :=
        expr_interp_correct (weaken_typing (Hwt 0 Φ (by simp)) (global_shift_id_typing Γ d Hlen))
      have hrest := IH (fun m Φ' h => Hwt (m + 1) Φ' (by simpa using h))
      rw [show interp_poctx_at d (Φ :: rest) (Γ := Γ)
            = (expr_interp Γ (weaken Φ (REN.global_shift d REN.id)) TYPE.prop).bind
                (fun Φ' => (interp_poctx_at d rest).bind (fun rest' => pure (Φ' :: rest'))) from rfl,
          Part.Dom.bind hΦw, Part.Dom.bind hrest]
      trivial

  lemma interp_pctx_at_dom {Γ : CTX.{i}} (d : Nat) (Ψ : PCTX.{i})
      (Hlen : d + Ψ.length ≤ Γ.length)
      (Hwt : ∀ (k m : Nat) (Ψ' : POCTX.{i}) (Φ : EXPR.{i}),
        Ψ[k]? = some Ψ' → Ψ'[m]? = some Φ → TYPED (Γ.drop (d + k)) Φ TYPE.prop) :
      (interp_pctx_at d Ψ (Γ := Γ)).Dom := by
    induction Ψ generalizing d with
    | nil => simp [interp_pctx_at]
    | cons Ψf Ψrest IH =>
      have hfdom : (interp_poctx_at d Ψf (Γ := Γ)).Dom := by
        by_cases hf0 : Ψf = []
        · subst hf0; simp [interp_poctx_at]
        · exact interp_poctx_at_dom d Ψf
            (by simp only [List.length_cons] at Hlen
                have : 0 < Ψf.length := List.length_pos_of_ne_nil hf0
                omega)
            (fun m Φ h => by simpa using Hwt 0 m Ψf Φ (by simp) h)
      have hrestdom := IH (d + 1) (by simp only [List.length_cons] at Hlen; omega)
          (fun k m Ψ' Φ hk hm => by
            have := Hwt (k + 1) m Ψ' Φ hk hm
            have he : d + (k + 1) = d + 1 + k := by omega
            rwa [he] at this)
      rw [show interp_pctx_at d (Ψf :: Ψrest) (Γ := Γ)
            = (interp_poctx_at d Ψf).bind
                (fun Ψf' => (interp_pctx_at (d + 1) Ψrest).bind (fun rest' => pure (Ψf' :: rest')))
            from rfl,
          Part.Dom.bind hfdom, Part.Dom.bind hrestdom]
      trivial

  lemma n_force_succ_eq_cut_force (m : Nat) (Hn : 0 < m + 1) :
      n_force (i := m + 1) = n_force_cut Hn ≫ force := by
    rw [n_force_cut_nm_force_cut Hn, nm_force_cut_decomp (show (1 : Nat) ≤ m + 1 by omega)]
    congr 1

  lemma lift_delay_prop_typed {Γ : CTX.{i}} {P : PROPOSITION.{i}}
      (h : TYPED Γ (.lift (.delay P)) TYPE.prop) : TYPED ([] :: Γ) P TYPE.prop := by
    obtain ⟨_, hl⟩ := h.lift_inversion
    obtain ⟨τ', heq, hb⟩ := hl.delay_inversion
    obtain rfl : τ' = TYPE.prop := by injection heq.symm
    exact hb

  lemma soundness_loeb_ind {Γ : CTX.{i}} {Ψs : POCTX.{i}} {Φs : PCTX.{i}} {Φ : PROPOSITION.{i}}
    (H : PROVES Γ ((.lift (.delay (weaken Φ (REN.global_shift 1 REN.id))) :: Ψs) :: Φs) Φ)
    (IH : ctx_typed Γ ((.lift (.delay (weaken Φ (REN.global_shift 1 REN.id))) :: Ψs) :: Φs) →
      ∀ (Ψ_interp : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ),
      interp_pctx ((.lift (.delay (weaken Φ (REN.global_shift 1 REN.id))) :: Ψs) :: Φs) = pure Ψ_interp →
      expr_interp Γ Φ TYPE.prop = pure Φ_interp → pctx Ψ_interp ⊢ᵢ Φ_interp)
    (Hwf : ctx_typed Γ (Ψs :: Φs))
    (Ψ_interp : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
    (HΨ : interp_pctx (Ψs :: Φs) = pure Ψ_interp)
    (HΦ : expr_interp Γ Φ TYPE.prop = pure Φ_interp)
    : pctx Ψ_interp ⊢ᵢ Φ_interp := by

    obtain ⟨Ψs', Φs', he1, he2, he3⟩ := interp_pctx_cons_decomp HΨ
    rw [he3]; simp only [pctx]

    apply loeb_ind

    have hlen : 0 < Γ.length := by rw [PROVES.len H]; simp
    have h_typed := PROVES.typed H
    have h_adv := expr_advance (Γ := Γ) (d := 0) hlen (Φ := Φ) h_typed
    rw [weaken_global_shift_zero_id, HΦ] at h_adv
    have h_lift_eq : expr_interp Γ (.lift (.delay (weaken Φ (REN.global_shift 1 REN.id)))) TYPE.prop
        = pure (interp_lift (interp_delay
            (((λ_ (earlier.obj ⟦Γ⟧ₛ)).hom ≫ force.app ⟦Γ⟧ₛ) ≫ Φ_interp))) := by
      simp [expr_interp, h_adv]
    have hpctx_eq : interp_pctx
          (((.lift (.delay (weaken Φ (REN.global_shift 1 REN.id)))) :: Ψs) :: Φs)
        = pure (((interp_lift (interp_delay
            (((λ_ (earlier.obj ⟦Γ⟧ₛ)).hom ≫ force.app ⟦Γ⟧ₛ) ≫ Φ_interp))) :: Ψs') :: Φs') := by
      simp only [interp_pctx, interp_pctx_at, interp_poctx_at, weaken_global_shift_zero_id, h_lift_eq,
        he1, he2, pure_bind]
    rw [← Category.assoc]
    exact IH (ctx_typed_cons0 Hwf (by
      apply TYPED.lift; apply TYPED.delay hlen
      exact weaken_typing h_typed
        (global_shift_id_typing ([] :: Γ) 1 (by simp only [List.length_cons]; omega))))
      _ Φ_interp hpctx_eq HΦ

  lemma pctx_entails_getElem {Γ : CTX.{i}} {n : Nat} :
      ∀ {Ψ_interp : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))} {Ψn_interp},
      Ψ_interp[n]? = some Ψn_interp → pctx Ψ_interp ⊢ᵢ poctx Ψn_interp := by
    induction n with
    | zero =>
      intro Ψ_interp Ψn_interp H
      cases Ψ_interp with
      | nil => simp at H
      | cons a as =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at H; subst H
        simp only [pctx]; exact conj_elim_l
    | succ n' IH =>
      intro Ψ_interp Ψn_interp H
      cases Ψ_interp with
      | nil => simp at H
      | cons a as =>
        simp only [List.getElem?_cons_succ] at H
        simp only [pctx]; exact entails_trans _ _ _ conj_elim_r (IH H)

  lemma poctx_entails_getElem {Γ : CTX.{i}} {m : Nat} :
      ∀ {Ψn_interp : List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)} {P},
      Ψn_interp[m]? = some P → poctx Ψn_interp ⊢ᵢ P := by
    induction m with
    | zero =>
      intro Ψn_interp P H
      cases Ψn_interp with
      | nil => simp at H
      | cons a as =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at H; subst H
        simp only [poctx]; exact conj_elim_l
    | succ m' IH =>
      intro Ψn_interp P H
      cases Ψn_interp with
      | nil => simp at H
      | cons a as =>
        simp only [List.getElem?_cons_succ] at H
        simp only [poctx]; exact entails_trans _ _ _ conj_elim_r (IH H)

  lemma interp_pctx_at_getElem {Γ : CTX.{i}} {d n : Nat} :
      ∀ {Ψ : PCTX.{i}} {Ψ_interp : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))} {Ψn : POCTX.{i}},
      interp_pctx_at d Ψ = pure Ψ_interp → Ψ[n]? = some Ψn →
      ∃ Ψn_interp, Ψ_interp[n]? = some Ψn_interp ∧ interp_poctx_at (d + n) Ψn = pure Ψn_interp := by
    induction n generalizing d with
    | zero =>
      intro Ψ Ψ_interp Ψn HΨ Hn
      cases Ψ with
      | nil => simp at Hn
      | cons Ψ0 Ψs =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at Hn; subst Hn
        obtain ⟨Ψ0', Ψs', h0, hs, heq⟩ := interp_pctx_at_cons_decomp HΨ
        exact ⟨Ψ0', by rw [heq]; simp, by simpa using h0⟩
    | succ n' IH =>
      intro Ψ Ψ_interp Ψn HΨ Hn
      cases Ψ with
      | nil => simp at Hn
      | cons Ψ0 Ψs =>
        simp only [List.getElem?_cons_succ] at Hn
        obtain ⟨Ψ0', Ψs', h0, hs, heq⟩ := interp_pctx_at_cons_decomp HΨ
        obtain ⟨Ψn_interp, hget, hint⟩ := IH hs Hn
        refine ⟨Ψn_interp, ?_, ?_⟩
        · rw [heq]; simpa using hget
        · rw [show d + (n' + 1) = (d + 1) + n' by omega]; exact hint

  lemma interp_poctx_at_getElem {Γ : CTX.{i}} {d m : Nat} :
      ∀ {Ψn : POCTX.{i}} {Ψn_interp : List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)} {Φ : EXPR.{i}},
      interp_poctx_at d Ψn = pure Ψn_interp → Ψn[m]? = some Φ →
      ∃ P, Ψn_interp[m]? = some P ∧
        expr_interp Γ (weaken Φ (REN.global_shift d REN.id)) TYPE.prop = pure P := by
    induction m with
    | zero =>
      intro Ψn Ψn_interp Φ HΨ Hm
      cases Ψn with
      | nil => simp at Hm
      | cons Φ0 rest =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at Hm; subst Hm
        obtain ⟨Φ', rest', hΦ', hrest, heq⟩ := interp_poctx_at_cons_decomp HΨ
        exact ⟨Φ', by rw [heq]; simp, hΦ'⟩
    | succ m' IH =>
      intro Ψn Ψn_interp Φ HΨ Hm
      cases Ψn with
      | nil => simp at Hm
      | cons Φ0 rest =>
        simp only [List.getElem?_cons_succ] at Hm
        obtain ⟨Φ', rest', hΦ', hrest, heq⟩ := interp_poctx_at_cons_decomp HΨ
        obtain ⟨P, hget, hexpr⟩ := IH hrest Hm
        exact ⟨P, by rw [heq]; simpa using hget, hexpr⟩

  lemma soundness_asm {Γ : CTX.{i}} {Ψ : PCTX.{i}} {Φ : PROPOSITION.{i}}
    {n m : Nat} {Ψ' : POCTX.{i}}
    (Hn : Ψ[n]? = some Ψ') (Hm : Ψ'[m]? = some Φ)
    (_Htyped : TYPED Γ (weaken Φ (REN.global_shift n REN.id)) TYPE.prop)
    (Ψ_interp : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
    (HΨ : interp_pctx Ψ = pure Ψ_interp)
    (HΦ : expr_interp Γ (weaken Φ (REN.global_shift n REN.id)) TYPE.prop = pure Φ_interp)
    : pctx Ψ_interp ⊢ᵢ Φ_interp := by
    obtain ⟨Ψn_interp, hgetn, hintn⟩ := interp_pctx_at_getElem HΨ Hn
    simp only [Nat.zero_add] at hintn
    obtain ⟨P, hgetm, hexprm⟩ := interp_poctx_at_getElem hintn Hm
    rw [show Φ_interp = P from Part.some_injective
      (show (pure Φ_interp : Part (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)) = pure P by rw [← HΦ]; exact hexprm)]
    exact entails_trans _ _ _ (pctx_entails_getElem hgetn) (poctx_entails_getElem hgetm)

  lemma soundness_later_mono {Γ : CTX.{i}} {Ψ : PCTX.{i}} {P Q : PROPOSITION.{i}}
    (_Hlen : 0 < Γ.length)
    (H1 : PROVES Γ Ψ (.lift (.delay P)))
    (H2 : PROVES ([] :: Γ) ([P] :: Ψ) Q)
    (IH1 : ctx_typed Γ Ψ →
      ∀ (Ψi : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φi : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ),
      interp_pctx Ψ = pure Ψi → expr_interp Γ (.lift (.delay P)) TYPE.prop = pure Φi → pctx Ψi ⊢ᵢ Φi)
    (IH2 : ctx_typed ([] :: Γ) ([P] :: Ψ) →
      ∀ (Ψi : List (List (⟦[] :: Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φi : ⟦[] :: Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ),
      interp_pctx ([P] :: Ψ) = pure Ψi → expr_interp ([] :: Γ) Q TYPE.prop = pure Φi → pctx Ψi ⊢ᵢ Φi)
    (Hwf : ctx_typed Γ Ψ)
    (Ψ_interp : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
    (HΨ : interp_pctx Ψ = pure Ψ_interp)
    (HΦ : expr_interp Γ (.lift (.delay Q)) TYPE.prop = pure Φ_interp)
    : pctx Ψ_interp ⊢ᵢ Φ_interp := by
    have hPty : TYPED ([] :: Γ) P TYPE.prop := lift_delay_prop_typed (PROVES.typed H1)
    set Q_ext := (expr_interp ([] :: Γ) Q TYPE.prop).get (expr_interp_correct (PROVES.typed H2)) with hQ_def
    have hQ_eq : expr_interp ([] :: Γ) Q TYPE.prop = pure Q_ext := by ext; simp [hQ_def]
    set P_ext := (expr_interp ([] :: Γ) P TYPE.prop).get (expr_interp_correct hPty) with hP_def
    have hP_eq : expr_interp ([] :: Γ) P TYPE.prop = pure P_ext := by ext; simp [hP_def]
    rw [show Φ_interp = interp_lift (interp_delay Q_ext) by
      simp only [expr_interp, hQ_eq, pure_bind] at HΦ
      exact (Part.some_injective HΦ).symm]
    have key := interp_pctx_at_advance 0 Ψ Ψ_interp
      (by have := PROVES.len H1; omega)
      (fun n m Ψ' Φ' hn hm => by simpa using Hwf n m Ψ' Φ' hn hm) HΨ
    simp only [Nat.zero_add] at key
    have hadv : interp_pctx ([P] :: Ψ) (Γ := [] :: Γ)
        = pure ([P_ext] :: Ψ_interp.map (fun frame =>
            frame.map (fun b => ((λ_ (earlier.obj ⟦Γ⟧ₛ)).hom ≫ force.app ⟦Γ⟧ₛ) ≫ b))) := by
      simp only [interp_pctx, interp_pctx_at, interp_poctx_at,
        weaken_global_shift_zero_id, Nat.zero_add, hP_eq, key, pure_bind]
    have hih2 := IH2 (ctx_typed_cons0 (ctx_typed_lift Hwf) (by simpa using hPty)) _ Q_ext hadv hQ_eq
    simp only [pctx, poctx] at hih2
    have hpm : (((λ_ (earlier.obj ⟦Γ⟧ₛ)).hom ≫ force.app ⟦Γ⟧ₛ) ≫ pctx Ψ_interp)
        = pctx (Γ := [] :: Γ) (Ψ_interp.map (fun frame =>
            frame.map (fun b => ((λ_ (earlier.obj ⟦Γ⟧ₛ)).hom ≫ force.app ⟦Γ⟧ₛ) ≫ b))) :=
      (pctx_map_postcomp (Δ := [] :: Γ)
        ((λ_ (earlier.obj ⟦Γ⟧ₛ)).hom ≫ force.app ⟦Γ⟧ₛ) Ψ_interp).symm
    rw [← hpm] at hih2
    have hmid : pctx Ψ_interp ⊢ᵢ
        interp_lift (interp_delay (P_ext ∧ᵢ
          (((λ_ (earlier.obj ⟦Γ⟧ₛ)).hom ≫ force.app ⟦Γ⟧ₛ) ≫ pctx Ψ_interp))) := by
      refine entails_trans _ _ _
        (conj_intro (IH1 Hwf Ψ_interp (interp_lift (interp_delay P_ext)) HΨ (by simp [expr_interp, hP_eq]))
          (later_intro (pctx Ψ_interp))) ?_
      rw [← Category.assoc]
      exact later_conj P_ext (((λ_ (earlier.obj ⟦Γ⟧ₛ)).hom ≫ force.app ⟦Γ⟧ₛ) ≫ pctx Ψ_interp)
    exact entails_trans _ _ _ hmid (later_mono
      (entails_trans _ _ _ (conj_intro (conj_intro conj_elim_l true_intro) conj_elim_r) hih2))

  lemma soundness_later_and {Γ : CTX.{i}} {Ψ : PCTX.{i}} {P Q : PROPOSITION.{i}}
    (H1 : PROVES Γ Ψ (.lift (.delay P)))
    (H2 : PROVES Γ Ψ (.lift (.delay Q)))
    (IH1 : ∀ (Ψi : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φi : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ),
      interp_pctx Ψ = pure Ψi → expr_interp Γ (.lift (.delay P)) TYPE.prop = pure Φi → pctx Ψi ⊢ᵢ Φi)
    (IH2 : ∀ (Ψi : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φi : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ),
      interp_pctx Ψ = pure Ψi → expr_interp Γ (.lift (.delay Q)) TYPE.prop = pure Φi → pctx Ψi ⊢ᵢ Φi)
    (Ψ_interp : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
    (HΨ : interp_pctx Ψ = pure Ψ_interp)
    (HΦ : expr_interp Γ (.lift (.delay (.and P Q))) TYPE.prop = pure Φ_interp)
    : pctx Ψ_interp ⊢ᵢ Φ_interp := by
    set P_ext := (expr_interp ([] :: Γ) P TYPE.prop).get
      (expr_interp_correct (lift_delay_prop_typed (PROVES.typed H1))) with hP_def
    have hP_eq : expr_interp ([] :: Γ) P TYPE.prop = pure P_ext := by ext; simp [hP_def]
    set Q_ext := (expr_interp ([] :: Γ) Q TYPE.prop).get
      (expr_interp_correct (lift_delay_prop_typed (PROVES.typed H2))) with hQ_def
    have hQ_eq : expr_interp ([] :: Γ) Q TYPE.prop = pure Q_ext := by ext; simp [hQ_def]
    rw [show Φ_interp = interp_lift (interp_delay (interp_and P_ext Q_ext)) by
      rw [show expr_interp Γ (.lift (.delay (.and P Q))) TYPE.prop
            = pure (interp_lift (interp_delay (interp_and P_ext Q_ext))) by
          simp [expr_interp, hP_eq, hQ_eq]] at HΦ
      exact (Part.some_injective HΦ).symm]
    exact entails_trans _ _ _
      (conj_intro (IH1 Ψ_interp _ HΨ (by simp [expr_interp, hP_eq]))
        (IH2 Ψ_interp _ HΨ (by simp [expr_interp, hQ_eq])))
      (later_conj P_ext Q_ext)

  lemma soundness_later_or {Γ : CTX.{i}} {Ψ : PCTX.{i}} {P Q : PROPOSITION.{i}}
    (H : PROVES Γ Ψ (.lift (.delay (.or P Q))))
    (IH : ∀ (Ψi : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φi : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ),
      interp_pctx Ψ = pure Ψi →
      expr_interp Γ (.lift (.delay (.or P Q))) TYPE.prop = pure Φi → pctx Ψi ⊢ᵢ Φi)
    (Ψ_interp : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
    (HΨ : interp_pctx Ψ = pure Ψ_interp)
    (HΦ : expr_interp Γ (.or (.lift (.delay P)) (.lift (.delay Q))) TYPE.prop = pure Φ_interp)
    : pctx Ψ_interp ⊢ᵢ Φ_interp := by
    obtain ⟨_, hPty, hQty⟩ := (lift_delay_prop_typed (PROVES.typed H)).or_inversion
    set P_ext := (expr_interp ([] :: Γ) P TYPE.prop).get (expr_interp_correct hPty) with hP_def
    have hP_eq : expr_interp ([] :: Γ) P TYPE.prop = pure P_ext := by ext; simp [hP_def]
    set Q_ext := (expr_interp ([] :: Γ) Q TYPE.prop).get (expr_interp_correct hQty) with hQ_def
    have hQ_eq : expr_interp ([] :: Γ) Q TYPE.prop = pure Q_ext := by ext; simp [hQ_def]
    rw [show Φ_interp = interp_or (interp_lift (interp_delay P_ext))
        (interp_lift (interp_delay Q_ext)) by
      rw [show expr_interp Γ (.or (.lift (.delay P)) (.lift (.delay Q))) TYPE.prop
            = pure (interp_or (interp_lift (interp_delay P_ext))
                (interp_lift (interp_delay Q_ext))) by simp [expr_interp, hP_eq, hQ_eq]] at HΦ
      exact (Part.some_injective HΦ).symm]
    exact entails_trans _ _ _
      (IH Ψ_interp (interp_lift (interp_delay (interp_or P_ext Q_ext))) HΨ
        (by simp [expr_interp, hP_eq, hQ_eq])) (later_disj P_ext Q_ext)

  lemma soundness_exists_elim' {Γ : OCTX.{i}} {Γs : CTX.{i}} {Ψ : POCTX.{i}} {Ψs : PCTX.{i}}
    {τ : TYPE.{i}} {Φ Q : PROPOSITION.{i}}
    (HQty : TYPED (Γ :: Γs) Q TYPE.prop)
    (Hex : PROVES (Γ :: Γs) (Ψ :: Ψs) (.exists' τ Φ))
    (IH1 : ctx_typed (Γ :: Γs) (Ψ :: Ψs) →
      ∀ (Ψi : List (List (⟦Γ :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φi : ⟦Γ :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ),
      interp_pctx (Ψ :: Ψs) = pure Ψi →
      expr_interp (Γ :: Γs) (.exists' τ Φ) TYPE.prop = pure Φi → pctx Ψi ⊢ᵢ Φi)
    (IH2 : ctx_typed ((τ :: Γ) :: Γs) ((Φ :: intro_wrap' Ψ) :: Ψs) →
      ∀ (Ψi : List (List (⟦(τ :: Γ) :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φi : ⟦(τ :: Γ) :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ),
      interp_pctx ((Φ :: intro_wrap' Ψ) :: Ψs) = pure Ψi →
      expr_interp ((τ :: Γ) :: Γs) (weaken Q octx_wk) TYPE.prop = pure Φi → pctx Ψi ⊢ᵢ Φi)
    (Hwf : ctx_typed (Γ :: Γs) (Ψ :: Ψs))
    (Ψ_interp : List (List (⟦Γ :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
    (HΨ : interp_pctx (Ψ :: Ψs) = pure Ψ_interp)
    (HΦ : expr_interp (Γ :: Γs) Q TYPE.prop = pure Φ_interp)
    : pctx Ψ_interp ⊢ᵢ Φ_interp := by
    obtain ⟨_, h_body_typed⟩ := TYPED.exists'_inversion (PROVES.typed Hex)
    set Φb := (expr_interp ((τ :: Γ) :: Γs) Φ TYPE.prop).get (expr_interp_correct h_body_typed) with hΦb_def
    have h_body_eq : expr_interp ((τ :: Γ) :: Γs) Φ TYPE.prop = pure Φb := by
      ext; simp [hΦb_def]
    have hex_sem := IH1 Hwf Ψ_interp (interp_exists Φb) HΨ (by simp [expr_interp, h_body_eq])
    have hposlen : 0 < (Γ :: Γs).length := by simp
    set Hσ : TYPED_REN octx_wk ((τ :: Γ) :: Γs) (Γ :: Γs) :=
      TYPED_REN.local_weaken τ (TYPED_REN.id hposlen) with hHσ
    have hR_eq : ⟦Hσ⟧ᵣ = interp_ren_local_weaken (τ := τ) interp_ren_id := by
      simp only [hHσ, interp_typed_ren, interp_ren_id]
    obtain ⟨WiH, WiT, hWiH, hWiT, hWiEq⟩ := interp_pctx_cons_decomp
      (show interp_pctx (intro_wrap' Ψ :: Ψs)
          = pure (Ψ_interp.map (fun fr => fr.map (fun b => ⟦Hσ⟧ᵣ ≫ b))) by
        simpa only [intro_wrap] using interp_pctx_intro_wrap (Ψ :: Ψs) Hσ Ψ_interp Hwf HΨ)
    have hbranchI : interp_pctx ((Φ :: intro_wrap' Ψ) :: Ψs)
        = pure ((Φb :: WiH) :: WiT) := by
      simp only [interp_pctx, interp_pctx_at, interp_poctx_at, weaken_global_shift_zero_id, h_body_eq]
      rw [show interp_poctx_at 0 (intro_wrap' Ψ) = pure WiH from hWiH,
        show interp_pctx_at 1 Ψs = pure WiT from hWiT]
      simp [Part.bind_some]
    have hbranchP : expr_interp ((τ :: Γ) :: Γs) (weaken Q octx_wk) TYPE.prop
        = pure (⟦Hσ⟧ᵣ ≫ Φ_interp) := by
      rw [eq_weak (Γ :: Γs) Q TYPE.prop Hσ HQty, HΦ]; rfl
    have hwf_branch : ctx_typed ((τ :: Γ) :: Γs) ((Φ :: intro_wrap' Ψ) :: Ψs) := by
      have hiw : ctx_typed ((τ :: Γ) :: Γs) (intro_wrap' Ψ :: Ψs) := by
        simpa only [intro_wrap] using ctx_typed_intro_wrap Hσ Hwf
      exact ctx_typed_cons0 hiw h_body_typed
    have ih := IH2 hwf_branch _ _ hbranchI hbranchP
    have hpsi : ⟦Hσ⟧ᵣ ≫ pctx Ψ_interp = poctx WiH ∧ᵢ pctx WiT := by
      rw [← pctx_map_postcomp, hWiEq]; rfl
    have hbr0 : (Φb ∧ᵢ (poctx WiH ∧ᵢ pctx WiT)) ⊢ᵢ (⟦Hσ⟧ᵣ ≫ Φ_interp) := by
      refine entails_trans _ _ _ ?_ ih
      simp only [pctx, poctx]
      apply conj_intro
      · apply conj_intro
        · exact conj_elim_l
        · exact entails_trans _ _ _ conj_elim_r conj_elim_l
      · exact entails_trans _ _ _ conj_elim_r conj_elim_r
    have hbr1 : (Φb ∧ᵢ (⟦Hσ⟧ᵣ ≫ pctx Ψ_interp)) ⊢ᵢ (⟦Hσ⟧ᵣ ≫ Φ_interp) :=
      (congrArg (fun X => (((Φb ∧ᵢ X) ⊢ᵢ (⟦Hσ⟧ᵣ ≫ Φ_interp)) : Prop)) hpsi).mpr hbr0
    exact elim_ex Ψ_interp Φb Φ_interp hex_sem (hR_eq ▸ hbr1)

  lemma soundness_sum_elim {Γ : OCTX.{i}} {Γs : CTX.{i}} {Ψ : POCTX.{i}} {Ψs : PCTX.{i}}
    {A B : TYPE.{i}} {Φ : PROPOSITION.{i}} (e : EXPR.{i})
    (HΦty : TYPED (Γ :: Γs) Φ TYPE.prop)
    (He : TYPED (Γ :: Γs) e (TYPE.sum A B))
    (IHinl : ctx_typed ((A :: Γ) :: Γs)
        ((EXPR.eq (TYPE.sum A B) (weaken e octx_wk) (.inl B (.var' 0 0)) :: intro_wrap' Ψ) :: Ψs) →
      ∀ (Ψi : List (List (⟦(A :: Γ) :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φi : ⟦(A :: Γ) :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ),
        interp_pctx
            ((EXPR.eq (TYPE.sum A B) (weaken e octx_wk) (.inl B (.var' 0 0)) :: intro_wrap' Ψ) :: Ψs)
          = pure Ψi →
        expr_interp ((A :: Γ) :: Γs) (weaken Φ octx_wk) TYPE.prop = pure Φi → pctx Ψi ⊢ᵢ Φi)
    (IHinr : ctx_typed ((B :: Γ) :: Γs)
        ((EXPR.eq (TYPE.sum A B) (weaken e octx_wk) (.inr A (.var' 0 0)) :: intro_wrap' Ψ) :: Ψs) →
      ∀ (Ψi : List (List (⟦(B :: Γ) :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φi : ⟦(B :: Γ) :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ),
        interp_pctx
            ((EXPR.eq (TYPE.sum A B) (weaken e octx_wk) (.inr A (.var' 0 0)) :: intro_wrap' Ψ) :: Ψs)
          = pure Ψi →
        expr_interp ((B :: Γ) :: Γs) (weaken Φ octx_wk) TYPE.prop = pure Φi → pctx Ψi ⊢ᵢ Φi)
    (Hwf : ctx_typed (Γ :: Γs) (Ψ :: Ψs))
    (Ψ_interp : List (List (⟦Γ :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
    (HΨ : interp_pctx (Ψ :: Ψs) = pure Ψ_interp)
    (HΦ : expr_interp (Γ :: Γs) Φ TYPE.prop = pure Φ_interp)
    : pctx Ψ_interp ⊢ᵢ Φ_interp := by
    set e_interp := (expr_interp (Γ :: Γs) e (TYPE.sum A B)).get (expr_interp_correct He) with he_def
    have h_e_eq : expr_interp (Γ :: Γs) e (TYPE.sum A B) = Part.some e_interp := by
      ext; simp [e_interp]
    have hposlen : 0 < (Γ :: Γs).length := by simp
    set HσA : TYPED_REN octx_wk ((A :: Γ) :: Γs) (Γ :: Γs) :=
      TYPED_REN.local_weaken A (TYPED_REN.id hposlen) with hHσA
    set HσB : TYPED_REN octx_wk ((B :: Γ) :: Γs) (Γ :: Γs) :=
      TYPED_REN.local_weaken B (TYPED_REN.id hposlen) with hHσB
    set vA : ⟦(A :: Γ) :: Γs⟧ₛ ⟶ ⟦A⟧ₜ := interp_var 0 0 (rfl) (rfl) with hvAdef
    set vB : ⟦(B :: Γ) :: Γs⟧ₛ ⟶ ⟦B⟧ₜ := interp_var 0 0 (rfl) (rfl) with hvBdef
    have hRA_eq : ⟦HσA⟧ᵣ = interp_ren_local_weaken (τ := A) interp_ren_id := by
      simp only [hHσA, interp_typed_ren, interp_ren_id]
    have hRB_eq : ⟦HσB⟧ᵣ = interp_ren_local_weaken (τ := B) interp_ren_id := by
      simp only [hHσB, interp_typed_ren, interp_ren_id]
    have hvA_fst : vA = (α_ ⟦A⟧ₜ ⟦Γ⟧ₒ (earlier.obj ⟦Γs⟧ₛ)).hom ≫ fst _ _ := by
      simp only [hvAdef, interp_var, ctx_proj, octx_proj, interp_octx, interp_ctx, eqToHom_refl,
        Category.comp_id]
      rw [← CategoryTheory.CartesianMonoidalCategory.associator_hom_fst]
    have hvB_fst : vB = (α_ ⟦B⟧ₜ ⟦Γ⟧ₒ (earlier.obj ⟦Γs⟧ₛ)).hom ≫ fst _ _ := by
      simp only [hvBdef, interp_var, ctx_proj, octx_proj, interp_octx, interp_ctx, eqToHom_refl,
        Category.comp_id]
      rw [← CategoryTheory.CartesianMonoidalCategory.associator_hom_fst]
    have surjA : ∀ (n : ℕ) (γ : (⟦Γ :: Γs⟧ₛ).obj (op n)) (a : (⟦A⟧ₜ).obj (op n)),
        ∃ x : (⟦(A :: Γ) :: Γs⟧ₛ).obj (op n),
          (⟦HσA⟧ᵣ).app (op n) x = γ ∧ vA.app (op n) x = a := by
      intro n γ a
      refine ⟨(α_ ⟦A⟧ₜ ⟦Γ⟧ₒ (earlier.obj ⟦Γs⟧ₛ)).inv.app (op n) (a, γ), ?_, ?_⟩
      · rw [hRA_eq]; exact snd_lw_inv_app n a γ
      · rw [hvA_fst]; exact fst_assoc_inv_app n a γ
    have surjB : ∀ (n : ℕ) (γ : (⟦Γ :: Γs⟧ₛ).obj (op n)) (b : (⟦B⟧ₜ).obj (op n)),
        ∃ x : (⟦(B :: Γ) :: Γs⟧ₛ).obj (op n),
          (⟦HσB⟧ᵣ).app (op n) x = γ ∧ vB.app (op n) x = b := by
      intro n γ b
      refine ⟨(α_ ⟦B⟧ₜ ⟦Γ⟧ₒ (earlier.obj ⟦Γs⟧ₛ)).inv.app (op n) (b, γ), ?_, ?_⟩
      · rw [hRB_eq]; exact snd_lw_inv_app n b γ
      · rw [hvB_fst]; exact fst_assoc_inv_app n b γ
    have hbranch : ∀ {τ : TYPE.{i}} (Hσ : TYPED_REN octx_wk ((τ :: Γ) :: Γs) (Γ :: Γs))
        (inj : EXPR.{i}) (inj_interp : ⟦(τ :: Γ) :: Γs⟧ₛ ⟶ ⟦TYPE.sum A B⟧ₜ),
        expr_interp ((τ :: Γ) :: Γs) inj (TYPE.sum A B) = pure inj_interp →
        (ctx_typed ((τ :: Γ) :: Γs)
          ((EXPR.eq (TYPE.sum A B) (weaken e octx_wk) inj :: intro_wrap' Ψ) :: Ψs) →
          ∀ (Ψi : List (List (⟦(τ :: Γ) :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)))
            (Φi : ⟦(τ :: Γ) :: Γs⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ),
            interp_pctx
                ((EXPR.eq (TYPE.sum A B) (weaken e octx_wk) inj :: intro_wrap' Ψ) :: Ψs) = pure Ψi →
            expr_interp ((τ :: Γ) :: Γs) (weaken Φ octx_wk) TYPE.prop = pure Φi → pctx Ψi ⊢ᵢ Φi) →
        TYPED ((τ :: Γ) :: Γs) inj (TYPE.sum A B) →
        (((⟦Hσ⟧ᵣ ≫ e_interp) ≡ᵢ inj_interp) ∧ᵢ (⟦Hσ⟧ᵣ ≫ pctx Ψ_interp)) ⊢ᵢ (⟦Hσ⟧ᵣ ≫ Φ_interp) := by
      intro τ Hσ inj inj_interp hinj IH hinj_typed
      obtain ⟨WiH, WiT, hWiH, hWiT, hWiEq⟩ := interp_pctx_cons_decomp
        (show interp_pctx (intro_wrap' Ψ :: Ψs)
            = pure (Ψ_interp.map (fun fr => fr.map (fun b => ⟦Hσ⟧ᵣ ≫ b))) by
          simpa only [intro_wrap] using interp_pctx_intro_wrap (Ψ :: Ψs) Hσ Ψ_interp Hwf HΨ)
      have h_wke : expr_interp ((τ :: Γ) :: Γs) (weaken e octx_wk) (TYPE.sum A B)
          = pure (⟦Hσ⟧ᵣ ≫ e_interp) := by
        rw [eq_weak (Γ :: Γs) e (TYPE.sum A B) Hσ He, h_e_eq, Part.map_some]; rfl
      have heqA_i : expr_interp ((τ :: Γ) :: Γs)
          (EXPR.eq (TYPE.sum A B) (weaken e octx_wk) inj) TYPE.prop
          = pure (interp_eq (⟦Hσ⟧ᵣ ≫ e_interp) inj_interp) := by
        simp only [expr_interp]
        rw [h_wke, hinj]; simp [Part.bind_some]
      have hbranchI : interp_pctx
          ((EXPR.eq (TYPE.sum A B) (weaken e octx_wk) inj :: intro_wrap' Ψ) :: Ψs)
          = pure ((interp_eq (⟦Hσ⟧ᵣ ≫ e_interp) inj_interp :: WiH) :: WiT) := by
        simp only [interp_pctx, interp_pctx_at, interp_poctx_at, weaken_global_shift_zero_id, heqA_i]
        rw [show interp_poctx_at 0 (intro_wrap' Ψ) = pure WiH from hWiH,
          show interp_pctx_at 1 Ψs = pure WiT from hWiT]
        simp [Part.bind_some]
      have hbranchP : expr_interp ((τ :: Γ) :: Γs) (weaken Φ octx_wk) TYPE.prop
          = pure (⟦Hσ⟧ᵣ ≫ Φ_interp) := by
        rw [eq_weak (Γ :: Γs) Φ TYPE.prop Hσ HΦty, HΦ]; rfl
      have hwf_branch : ctx_typed ((τ :: Γ) :: Γs)
          ((EXPR.eq (TYPE.sum A B) (weaken e octx_wk) inj :: intro_wrap' Ψ) :: Ψs) := by
        have hiw : ctx_typed ((τ :: Γ) :: Γs) (intro_wrap' Ψ :: Ψs) := by
          simpa only [intro_wrap] using ctx_typed_intro_wrap Hσ Hwf
        exact ctx_typed_cons0 hiw
          (TYPED.eq (weaken_typing He Hσ) hinj_typed)
      have ih := IH hwf_branch _ _ hbranchI hbranchP
      have hpsi : ⟦Hσ⟧ᵣ ≫ pctx Ψ_interp = poctx WiH ∧ᵢ pctx WiT := by
        rw [← pctx_map_postcomp, hWiEq]; rfl
      refine entails_trans _ _ _ ?_ ih
      erw [hpsi]
      simp only [pctx, poctx]
      apply conj_intro
      · apply conj_intro
        · exact conj_elim_l
        · exact entails_trans _ _ _ conj_elim_r conj_elim_l
      · exact entails_trans _ _ _ conj_elim_r conj_elim_r
    have h_varA : expr_interp ((A :: Γ) :: Γs) (EXPR.var' 0 0) A = pure vA := by
      rw [hvAdef]; simp only [expr_interp]
      rw [Part.assert_pos (show (0:Nat) < ((A :: Γ) :: Γs).length by simp),
          Part.assert_pos (show ((A :: Γ) :: Γs)[0][0]? = some A by rfl)]
    have h_varB : expr_interp ((B :: Γ) :: Γs) (EXPR.var' 0 0) B = pure vB := by
      rw [hvBdef]; simp only [expr_interp]
      rw [Part.assert_pos (show (0:Nat) < ((B :: Γ) :: Γs).length by simp),
          Part.assert_pos (show ((B :: Γ) :: Γs)[0][0]? = some B by rfl)]
    have h_inlA : expr_interp ((A :: Γ) :: Γs) (EXPR.inl B (.var' 0 0)) (TYPE.sum A B)
        = pure (interp_inl vA) := by
      show (Part.assert (B = B) fun _ =>
        (expr_interp ((A :: Γ) :: Γs) (EXPR.var' 0 0) A).bind
          (fun e' => pure (interp_inl (B := B) e'))) = pure (interp_inl vA)
      rw [Part.assert_pos rfl, h_varA]; simp
    have h_inrB : expr_interp ((B :: Γ) :: Γs) (EXPR.inr A (.var' 0 0)) (TYPE.sum A B)
        = pure (interp_inr vB) := by
      show (Part.assert (A = A) fun _ =>
        (expr_interp ((B :: Γ) :: Γs) (EXPR.var' 0 0) B).bind
          (fun e' => pure (interp_inr (A := A) e'))) = pure (interp_inr vB)
      rw [Part.assert_pos rfl, h_varB]; simp
    have HinlE := hbranch HσA (EXPR.inl B (.var' 0 0)) (interp_inl vA) h_inlA IHinl
      (TYPED.inl (TYPED.var' 0 0 rfl rfl))
    have HinrE := hbranch HσB (EXPR.inr A (.var' 0 0)) (interp_inr vB) h_inrB IHinr
      (TYPED.inr (TYPED.var' 0 0 rfl rfl))
    exact elim_sum e_interp (⟦HσA⟧ᵣ) vA (⟦HσB⟧ᵣ) vB Φ_interp (pctx Ψ_interp)
      surjA surjB HinlE HinrE

  lemma inl_inj_entails {Γ : CTX.{i}} {A B : TYPE.{i}} (a a' : ⟦Γ⟧ₛ ⟶ ⟦A⟧ₜ) :
      interp_eq (interp_inl (A := A) (B := B) a) (interp_inl (A := A) (B := B) a')
        ⊢ᵢ interp_eq a a' := by
    intro n γ m f He
    change Sum.inl (⟦A⟧ₜ.map f.op (a.app (op n) γ)) = Sum.inl (⟦A⟧ₜ.map f.op (a'.app (op n) γ)) at He
    show ⟦A⟧ₜ.map f.op (a.app (op n) γ) = ⟦A⟧ₜ.map f.op (a'.app (op n) γ)
    exact Sum.inl.inj He

  lemma inr_inj_entails {Γ : CTX.{i}} {A B : TYPE.{i}} (b b' : ⟦Γ⟧ₛ ⟶ ⟦B⟧ₜ) :
      interp_eq (interp_inr (A := A) (B := B) b) (interp_inr (A := A) (B := B) b')
        ⊢ᵢ interp_eq b b' := by
    intro n γ m f He
    change Sum.inr (⟦B⟧ₜ.map f.op (b.app (op n) γ)) = Sum.inr (⟦B⟧ₜ.map f.op (b'.app (op n) γ)) at He
    show ⟦B⟧ₜ.map f.op (b.app (op n) γ) = ⟦B⟧ₜ.map f.op (b'.app (op n) γ)
    exact Sum.inr.inj He

  lemma inl_inr_disj_entails {Γ : CTX.{i}} {A B : TYPE.{i}}
      (a : ⟦Γ⟧ₛ ⟶ ⟦A⟧ₜ) (b : ⟦Γ⟧ₛ ⟶ ⟦B⟧ₜ) :
      interp_eq (interp_inl (A := A) (B := B) a) (interp_inr (A := A) (B := B) b)
        ⊢ᵢ interp_false := by
    intro n γ m f He
    change Sum.inl (⟦A⟧ₜ.map f.op (a.app (op n) γ)) = Sum.inr (⟦B⟧ₜ.map f.op (b.app (op n) γ)) at He
    exact absurd He (by simp)

  lemma soundness_inl_inj {Γ : CTX.{i}} {Ψ : PCTX.{i}} {A B : TYPE.{i}} {a a' : EXPR.{i}}
      (_H : PROVES Γ Ψ (.eq (TYPE.sum A B) (.inl B a) (.inl B a')))
      (IH : ∀ (Ψ_i : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_i : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ),
        interp_pctx Ψ = pure Ψ_i →
        expr_interp Γ (.eq (TYPE.sum A B) (.inl B a) (.inl B a')) TYPE.prop = pure Φ_i →
        pctx Ψ_i ⊢ᵢ Φ_i)
      (Ψ_interp : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
      (HΨ : interp_pctx Ψ = pure Ψ_interp)
      (HΦ : expr_interp Γ (.eq A a a') TYPE.prop = pure Φ_interp)
      : pctx Ψ_interp ⊢ᵢ Φ_interp := by
    obtain ⟨_, h1, h2⟩ := TYPED.eq_inversion (PROVES.typed _H)
    rcases TYPED.inl_inversion h1 with ⟨A1, hτ1, ha⟩
    rcases TYPED.inl_inversion h2 with ⟨A2, hτ2, ha'⟩
    injection hτ1 with e11 _; injection hτ2 with e21 _
    set ai := (expr_interp Γ a A).get (expr_interp_correct (show TYPED Γ a A from e11 ▸ ha))
    set a'i := (expr_interp Γ a' A).get (expr_interp_correct (show TYPED Γ a' A from e21 ▸ ha'))
    have hae : expr_interp Γ a A = Part.some ai := (Part.some_get _).symm
    have ha'e : expr_interp Γ a' A = Part.some a'i := (Part.some_get _).symm
    have hinlA : expr_interp Γ (.inl B a) (TYPE.sum A B) = pure (interp_inl (B := B) ai) := by
      show (Part.assert (B = B) fun _ =>
        (expr_interp Γ a A).bind (fun e' => pure (interp_inl (B := B) e'))) = _
      rw [Part.assert_pos rfl, hae]; simp
    have hinlA' : expr_interp Γ (.inl B a') (TYPE.sum A B) = pure (interp_inl (B := B) a'i) := by
      show (Part.assert (B = B) fun _ =>
        (expr_interp Γ a' A).bind (fun e' => pure (interp_inl (B := B) e'))) = _
      rw [Part.assert_pos rfl, ha'e]; simp
    have hprem : expr_interp Γ (.eq (TYPE.sum A B) (.inl B a) (.inl B a')) TYPE.prop
        = pure (interp_eq (interp_inl (B := B) ai) (interp_inl (B := B) a'i)) := by
      show (expr_interp Γ (.inl B a) (TYPE.sum A B)).bind (fun e1' =>
        (expr_interp Γ (.inl B a') (TYPE.sum A B)).bind (fun e2' => pure (interp_eq e1' e2'))) = _
      rw [hinlA, hinlA']; simp [Part.bind_some]
    rw [show Φ_interp = interp_eq ai a'i by
      rw [show expr_interp Γ (.eq A a a') TYPE.prop = Part.some (interp_eq ai a'i) by
        simp only [expr_interp]; rw [hae, ha'e]; simp [Part.bind_some]] at HΦ
      exact (Part.some_injective HΦ).symm]
    exact entails_trans _ _ _ (IH Ψ_interp _ HΨ hprem) (inl_inj_entails ai a'i)

  lemma soundness_inr_inj {Γ : CTX.{i}} {Ψ : PCTX.{i}} {A B : TYPE.{i}} {b b' : EXPR.{i}}
      (_H : PROVES Γ Ψ (.eq (TYPE.sum A B) (.inr A b) (.inr A b')))
      (IH : ∀ (Ψ_i : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_i : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ),
        interp_pctx Ψ = pure Ψ_i →
        expr_interp Γ (.eq (TYPE.sum A B) (.inr A b) (.inr A b')) TYPE.prop = pure Φ_i →
        pctx Ψ_i ⊢ᵢ Φ_i)
      (Ψ_interp : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
      (HΨ : interp_pctx Ψ = pure Ψ_interp)
      (HΦ : expr_interp Γ (.eq B b b') TYPE.prop = pure Φ_interp)
      : pctx Ψ_interp ⊢ᵢ Φ_interp := by
    obtain ⟨_, h1, h2⟩ := TYPED.eq_inversion (PROVES.typed _H)
    rcases TYPED.inr_inversion h1 with ⟨B1, hτ1, hb⟩
    rcases TYPED.inr_inversion h2 with ⟨B2, hτ2, hb'⟩
    injection hτ1 with _ e12; injection hτ2 with _ e22
    set bi := (expr_interp Γ b B).get (expr_interp_correct (show TYPED Γ b B from e12 ▸ hb))
    set b'i := (expr_interp Γ b' B).get (expr_interp_correct (show TYPED Γ b' B from e22 ▸ hb'))
    have hbe : expr_interp Γ b B = Part.some bi := (Part.some_get _).symm
    have hb'e : expr_interp Γ b' B = Part.some b'i := (Part.some_get _).symm
    have hinrB : expr_interp Γ (.inr A b) (TYPE.sum A B) = pure (interp_inr (A := A) bi) := by
      show (Part.assert (A = A) fun _ =>
        (expr_interp Γ b B).bind (fun e' => pure (interp_inr (A := A) e'))) = _
      rw [Part.assert_pos rfl, hbe]; simp
    have hinrB' : expr_interp Γ (.inr A b') (TYPE.sum A B) = pure (interp_inr (A := A) b'i) := by
      show (Part.assert (A = A) fun _ =>
        (expr_interp Γ b' B).bind (fun e' => pure (interp_inr (A := A) e'))) = _
      rw [Part.assert_pos rfl, hb'e]; simp
    have hprem : expr_interp Γ (.eq (TYPE.sum A B) (.inr A b) (.inr A b')) TYPE.prop
        = pure (interp_eq (interp_inr (A := A) bi) (interp_inr (A := A) b'i)) := by
      show (expr_interp Γ (.inr A b) (TYPE.sum A B)).bind (fun e1' =>
        (expr_interp Γ (.inr A b') (TYPE.sum A B)).bind (fun e2' => pure (interp_eq e1' e2'))) = _
      rw [hinrB, hinrB']; simp [Part.bind_some]
    rw [show Φ_interp = interp_eq bi b'i by
      rw [show expr_interp Γ (.eq B b b') TYPE.prop = Part.some (interp_eq bi b'i) by
        simp only [expr_interp]; rw [hbe, hb'e]; simp [Part.bind_some]] at HΦ
      exact (Part.some_injective HΦ).symm]
    exact entails_trans _ _ _ (IH Ψ_interp _ HΨ hprem) (inr_inj_entails bi b'i)

  lemma soundness_inl_inr_disj {Γ : CTX.{i}} {Ψ : PCTX.{i}} {A B : TYPE.{i}} {a b : EXPR.{i}}
      (_H : PROVES Γ Ψ (.eq (TYPE.sum A B) (.inl B a) (.inr A b)))
      (IH : ∀ (Ψ_i : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_i : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ),
        interp_pctx Ψ = pure Ψ_i →
        expr_interp Γ (.eq (TYPE.sum A B) (.inl B a) (.inr A b)) TYPE.prop = pure Φ_i →
        pctx Ψ_i ⊢ᵢ Φ_i)
      (Ψ_interp : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
      (HΨ : interp_pctx Ψ = pure Ψ_interp)
      (HΦ : expr_interp Γ EXPR.false TYPE.prop = pure Φ_interp)
      : pctx Ψ_interp ⊢ᵢ Φ_interp := by
    obtain ⟨_, h1, h2⟩ := TYPED.eq_inversion (PROVES.typed _H)
    rcases TYPED.inl_inversion h1 with ⟨A1, hτ1, ha⟩
    rcases TYPED.inr_inversion h2 with ⟨B2, hτ2, hb⟩
    injection hτ1 with e11 _; injection hτ2 with _ e22
    set ai := (expr_interp Γ a A).get (expr_interp_correct (show TYPED Γ a A from e11 ▸ ha))
    set bi := (expr_interp Γ b B).get (expr_interp_correct (show TYPED Γ b B from e22 ▸ hb))
    have hae : expr_interp Γ a A = Part.some ai := (Part.some_get _).symm
    have hbe : expr_interp Γ b B = Part.some bi := (Part.some_get _).symm
    have hinlA : expr_interp Γ (.inl B a) (TYPE.sum A B) = pure (interp_inl (B := B) ai) := by
      show (Part.assert (B = B) fun _ =>
        (expr_interp Γ a A).bind (fun e' => pure (interp_inl (B := B) e'))) = _
      rw [Part.assert_pos rfl, hae]; simp
    have hinrB : expr_interp Γ (.inr A b) (TYPE.sum A B) = pure (interp_inr (A := A) bi) := by
      show (Part.assert (A = A) fun _ =>
        (expr_interp Γ b B).bind (fun e' => pure (interp_inr (A := A) e'))) = _
      rw [Part.assert_pos rfl, hbe]; simp
    have hprem : expr_interp Γ (.eq (TYPE.sum A B) (.inl B a) (.inr A b)) TYPE.prop
        = pure (interp_eq (interp_inl (B := B) ai) (interp_inr (A := A) bi)) := by
      show (expr_interp Γ (.inl B a) (TYPE.sum A B)).bind (fun e1' =>
        (expr_interp Γ (.inr A b) (TYPE.sum A B)).bind (fun e2' => pure (interp_eq e1' e2'))) = _
      rw [hinlA, hinrB]; simp [Part.bind_some]
    rw [show Φ_interp = interp_false by
      rw [show expr_interp Γ EXPR.false TYPE.prop = Part.some interp_false by
        simp only [expr_interp, interp_false]; rfl] at HΦ
      exact (Part.some_injective HΦ).symm]
    exact entails_trans _ _ _ (IH Ψ_interp _ HΨ hprem) (inl_inr_disj_entails ai bi)

  theorem soundness {Γ : CTX.{i}} {Ψ : PCTX.{i}} {Φ : PROPOSITION.{i}}
    (H : PROVES Γ Ψ Φ) (Hwf : ctx_typed Γ Ψ)
    : ∀ (Ψ_interp : List (List (⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ))) (Φ_interp : ⟦Γ⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ),
      interp_pctx Ψ = pure Ψ_interp →
      expr_interp Γ Φ TYPE.prop = pure Φ_interp →
      pctx Ψ_interp ⊢ᵢ Φ_interp := by
    intro Ψ_interp Φ_interp HΨ HΦ
    induction H with
    | asm n m Hn Hm Htyped Hlen =>
      exact soundness_asm Hn Hm Htyped Ψ_interp Φ_interp HΨ HΦ
    | true_intro Hlen Hlen' =>
      exact soundness_true_intro Hlen Ψ_interp Φ_interp HΨ HΦ
    | and_intro H1 H2 IH1 IH2 =>
      exact soundness_and_intro H1 H2 (IH1 Hwf) (IH2 Hwf) Ψ_interp Φ_interp HΨ HΦ
    | and_elim_l H IH =>
      exact soundness_and_elim_l H (IH Hwf) Ψ_interp Φ_interp HΨ HΦ
    | and_elim_r H IH =>
      exact soundness_and_elim_r H (IH Hwf) Ψ_interp Φ_interp HΨ HΦ
    | or_intro_l HΦ2 H IH =>
      exact soundness_or_intro_l HΦ2 H (IH Hwf) Ψ_interp Φ_interp HΨ HΦ
    | or_intro_r HΦ1 H IH =>
      exact soundness_or_intro_r HΦ1 H (IH Hwf) Ψ_interp Φ_interp HΨ HΦ
    | or_elim H1 H2 H3 IH1 IH2 IH3 =>
      cases PROVES.typed H3 with
      | or hP hQ =>
        exact soundness_or_elim H1 H2 H3 (IH1 (ctx_typed_cons0 Hwf hP))
          (IH2 (ctx_typed_cons0 Hwf hQ)) (IH3 Hwf) Ψ_interp Φ_interp HΨ HΦ
    | impl_intro HΦ1 H IH =>
      exact soundness_impl_intro HΦ1 H (IH (ctx_typed_cons0 Hwf HΦ1)) Ψ_interp Φ_interp HΨ HΦ
    | impl_elim H1 H2 IH1 IH2 =>
      exact soundness_impl_elim H1 H2 (IH1 Hwf) (IH2 Hwf) Ψ_interp Φ_interp HΨ HΦ
    | forall_intro' H IH =>
      exact soundness_forall_intro' H Hwf IH Ψ_interp Φ_interp HΨ HΦ
    | forall_elim' τ Φ e HΦty Hforall He IH =>
      exact soundness_forall_elim' He Hforall (IH Hwf) Ψ_interp Φ_interp HΨ HΦ
    | exists_intro' τ Φ e HΦty He H IH =>
      exact soundness_exists_intro' He HΦty (IH Hwf) Ψ_interp Φ_interp HΨ HΦ
    | forall_intro_points A Φ HΦty Hlen Hfam IH =>
      exact soundness_forall_intro_points HΦty (fun a => IH a Hwf) Ψ_interp Φ_interp HΨ HΦ
    | exists_elim' HQty Hex Hbr IH1 IH2 =>
      exact soundness_exists_elim' HQty Hex IH1 IH2 Hwf Ψ_interp Φ_interp HΨ HΦ
    | lift_intro Hlen H IH =>
      exact soundness_lift_intro Hlen H IH Hwf Ψ_interp Φ_interp HΨ HΦ
    | later_mono Hpos H1 H2 IH1 IH2 =>
      exact soundness_later_mono Hpos H1 H2 IH1 IH2 Hwf Ψ_interp Φ_interp HΨ HΦ
    | later_and H1 H2 IH1 IH2 =>
      exact soundness_later_and H1 H2 (IH1 Hwf) (IH2 Hwf) Ψ_interp Φ_interp HΨ HΦ
    | later_or H IH =>
      exact soundness_later_or H (IH Hwf) Ψ_interp Φ_interp HΨ HΦ
    | loeb_ind H IH =>
      exact soundness_loeb_ind H IH Hwf Ψ_interp Φ_interp HΨ HΦ
    | eq_def Heq Hlen =>
      exact soundness_eq_def Heq Ψ_interp Φ_interp HΨ HΦ
    | eq_elim HΦtyped He1 He2 Heq Hbinds1 IH1 IH2 =>
      exact soundness_eq_elim HΦtyped Heq Hbinds1 (IH1 Hwf) (IH2 Hwf) Ψ_interp Φ_interp HΨ HΦ
    | false_elim P HP H IH =>
      exact soundness_false_elim HP H (IH Hwf) Ψ_interp Φ_interp HΨ HΦ
    | pure_intro Hprop Htyped Hlen =>
      exact soundness_pure_intro Hprop Htyped Ψ_interp Φ_interp HΨ HΦ
    | delay_eq H IH =>
      exact soundness_delay_eq H (IH Hwf) Ψ_interp Φ_interp HΨ HΦ
    | sum_elim e HΦty He Hinl Hinr IHinl IHinr =>
      exact soundness_sum_elim e HΦty He IHinl IHinr Hwf Ψ_interp Φ_interp HΨ HΦ
    | inl_inj H IH =>
      exact soundness_inl_inj H (fun Ψ_i Φ_i => IH Hwf Ψ_i Φ_i) Ψ_interp Φ_interp HΨ HΦ
    | inr_inj H IH =>
      exact soundness_inr_inj H (fun Ψ_i Φ_i => IH Hwf Ψ_i Φ_i) Ψ_interp Φ_interp HΨ HΦ
    | inl_inr_disj H IH =>
      exact soundness_inl_inr_disj H (fun Ψ_i Φ_i => IH Hwf Ψ_i Φ_i) Ψ_interp Φ_interp HΨ HΦ

  theorem consistency (H : PROVES ([[]] : CTX.{i}) [[]] EXPR.false) : False := by
    have hent : (pctx (Γ := ([[]] : CTX.{i})) [[]] : ⟦([[]] : CTX.{i})⟧ₛ ⟶ ⟦TYPE.prop⟧ₜ)
        ⊢ᵢ interp_false :=
      soundness H
        (by intro k l Ψ' Φ Hk Hl; rcases k with _ | k <;> simp_all)
        [[]] _
        (by simp only [interp_pctx, interp_pctx_at, interp_poctx_at]
            exact (Part.bind_some _ _).trans (Part.bind_some _ _))
        (by simp only [expr_interp, interp_false])
    have hmem := hent 0 ⟨PUnit.unit, PUnit.unit⟩ 0 (𝟙 0) (by trivial)
    change False at hmem
    exact hmem

end soundness

end Soundness

end prf
