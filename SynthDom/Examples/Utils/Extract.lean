module

public import SynthDom
@[expose] public section

open CategoryTheory Logic MonoidalCategory CartesianMonoidalCategory

noncomputable section
namespace Extract

universe i

abbrev Point : ℐ.{i} := ⟦([[]] : CTX.{i})⟧ₛ

abbrev top : Point ⟶ ⟦TYPE.prop⟧ₜ := pctx [[]]

def Valid (P : EXPR.{i}) : Prop :=
  ∃ Φ : Point ⟶ ⟦TYPE.prop⟧ₜ, Φ ∈ expr_interp [[]] P TYPE.prop ∧ top ⊢ᵢ Φ

private lemma ctx_typed_nil : Soundness.ctx_typed ([[]] : CTX.{i}) [[]] := by
  intro k l Ψ Φ hk hl
  rcases k with _ | k <;> simp_all

private lemma interp_pctx_nil :
    Soundness.interp_pctx ([[]] : PCTX.{i}) = Part.some ([[]] : List (List (Point ⟶ ⟦TYPE.prop⟧ₜ))) := by
  simp only [Soundness.interp_pctx, Soundness.interp_pctx_at, Soundness.interp_poctx_at]
  exact (Part.bind_some _ _).trans (Part.bind_some _ _)

private lemma mem_expr_interp {P : EXPR.{i}} (HP : TYPED [[]] P TYPE.prop) :
    ∃ Φ, Φ ∈ expr_interp [[]] P TYPE.prop :=
  Part.dom_iff_mem.mp (expr_interp_correct HP)

theorem valid_of_goal {PΓ PΨ : ElabCtx} {P : EXPR.{i}} (H : GOAL PΓ PΨ [[]] [[]] P) :
    Valid P := by
  obtain ⟨Φ, hΦ⟩ := mem_expr_interp H.goal.typed
  exact ⟨Φ, hΦ, Soundness.soundness H.goal ctx_typed_nil _ _ interp_pctx_nil
    (Part.eq_some_iff.mpr hΦ)⟩

theorem valid_impl {P Q : EXPR.{i}} (HQ : TYPED [[]] Q TYPE.prop)
    (H : Valid (P.impl Q)) (HP : Valid P) : Valid Q := by
  obtain ⟨PQ', hPQ, hent⟩ := H
  obtain ⟨P', hP, hPv⟩ := HP
  obtain ⟨Q', hQ⟩ := mem_expr_interp HQ
  refine ⟨Q', hQ, ?_⟩
  simp only [expr_interp, Part.bind_eq_bind, Part.mem_bind_iff, Part.pure_eq_some,
    Part.mem_some_iff] at hPQ
  obtain ⟨p, hp, q, hq, hPQ⟩ := hPQ
  rw [Part.mem_unique hp hP, Part.mem_unique hq hQ] at hPQ
  exact elim_impl (hPQ ▸ hent) hPv

theorem valid_mp {PΓ PΨ : ElabCtx} {P Q : EXPR.{i}}
    (H : GOAL PΓ PΨ [[]] [[]] (P.impl Q)) (HP : Valid P) : Valid Q :=
  valid_impl (TYPED.impl_inversion H.goal.typed).2.2 (valid_of_goal H) HP

theorem valid_pure {φ : Prop} (H : Valid ⟪⌜δ(φ)⌝⟫) : φ := by
  obtain ⟨Φ, hΦ, hv⟩ := H
  simp only [expr_interp, Part.bind_eq_bind, Part.mem_bind_iff, Part.pure_eq_some,
    Part.mem_some_iff, Part.mem_assert_iff] at hΦ
  obtain ⟨a, ⟨_, ha⟩, rfl⟩ := hΦ
  obtain rfl : a = interp_embed Prop φ := by simpa using ha
  have hp := pure_sound (P := interp_embed Prop φ) 0 hv
  change φ at hp
  exact hp

private lemma interp_shift {P : EXPR.{i}} (HP : TYPED [[]] P TYPE.prop)
    {Φ : Point ⟶ ⟦TYPE.prop⟧ₜ} (hΦ : expr_interp [[]] P TYPE.prop = Part.some Φ) :
    expr_interp ([] :: [[]]) P TYPE.prop
      = Part.some (((λ_ (earlier.obj Point)).hom ≫ force.app Point) ≫ Φ) := by
  have h := Soundness.expr_advance (Γ := [[]]) (d := 0) (by simp) HP
  rw [weaken_closed HP, weaken_closed HP, hΦ] at h
  rw [h]
  rfl

private lemma later_elim {Φ : Point ⟶ ⟦TYPE.prop⟧ₜ}
    (H : top ⊢ᵢ interp_lift (interp_delay ((λ_ _).hom ≫ force.app _ ≫ Φ))) : top ⊢ᵢ Φ := by
  intro n γ m f _
  have hyp := H (n + 1) ⟨PUnit.unit, PUnit.unit⟩ (m + 1) (Nat.succ_le_succ (leOfHom f)).hom (by trivial)
  simp only [interp_lift, interp_delay] at hyp
  erw [ConcreteCategory.comp_apply, ConcreteCategory.hom_ofHom, TypeCat.Fun.mk_apply] at hyp
  replace hyp : (Sieve_succFunctor ((ConcreteCategory.hom (Φ.app (Opposite.op n)))
      ((ConcreteCategory.hom (Point.map (Opposite.op (homOfLE (Nat.le_succ n)))))
        ⟨PUnit.unit, PUnit.unit⟩)).down).arrows (Nat.succ_le_succ (leOfHom f)).hom := hyp
  simp only [Sieve_succFunctor, Presieve_succFunctor] at hyp
  obtain h | h := hyp
  · obtain ⟨_, _⟩ := γ
    exact h
  · exact absurd h (Nat.succ_ne_zero m)

theorem valid_later {P : EXPR.{i}} (HP : TYPED [[]] P TYPE.prop)
    (H : Valid P.delay.lift) : Valid P := by
  obtain ⟨L, hL, hent⟩ := H
  obtain ⟨Φ, hΦ⟩ := mem_expr_interp HP
  refine ⟨Φ, hΦ, ?_⟩
  simp only [expr_interp, Part.bind_eq_bind, Part.mem_bind_iff, Part.pure_eq_some,
    Part.mem_some_iff] at hL
  obtain ⟨_, ⟨b, hb, rfl⟩, rfl⟩ := hL
  rw [Part.mem_unique hb (Part.eq_some_iff.mp (interp_shift HP (Part.eq_some_iff.mpr hΦ)))] at hent
  exact later_elim hent

end Extract
end

end
