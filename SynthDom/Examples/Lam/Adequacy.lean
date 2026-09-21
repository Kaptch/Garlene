module

public import SynthDom
public import SynthDom.Examples.Lam.Model
public import SynthDom.Examples.Lam.Language
public import SynthDom.Examples.Lam.Soundness
public import SynthDom.Examples.Utils.Embed
public import SynthDom.Examples.Utils.Extract
@[expose] public section

namespace Lam

gtheorem Dom.proj_thunk : ∀ w : ▸ Dom.
    (([Dom.PROJ]ₛ ([Dom.thunk]ₛ w))
      = (inr (inr (inl w)) : (Δ Nat ⊕ (Δ Unit ⊕ (▸ Dom ⊕ ▸ (Dom → Dom)))))) := by
  gintro w
  gunfold Dom.thunk
  gsimpl
  grewrite (Dom.PROJ_MK)
  grfl

gtheorem Dom.proj_lam : ∀ g : ▸ (Dom → Dom).
    (([Dom.PROJ]ₛ ([Dom.lam]ₛ g))
      = (inr (inr (inr g)) : (Δ Nat ⊕ (Δ Unit ⊕ (▸ Dom ⊕ ▸ (Dom → Dom)))))) := by
  gintro g
  gunfold Dom.lam
  gsimpl
  grewrite (Dom.PROJ_MK)
  grfl

section wp

gdef Dom.wp : Dom → (Dom → Ω) → Ω :=
  fix W. λ p. λ Φ.
    case ([Dom.PROJ]ₛ p)
      (λ n. Φ p)
      (λ r. case r
        (λ u. ⊥)
        (λ r2. case r2
          (λ w. lift (delay (((adv 1 W) (adv 1 w)) Φ)))
          (λ g. Φ p)))

gtheorem Dom.eq_of_proj :
    ∀ p : Dom. ∀ x : (Δ Nat ⊕ (Δ Unit ⊕ (▸ Dom ⊕ ▸ (Dom → Dom)))).
      ((([Dom.PROJ]ₛ p) = x) → (p = [Dom.MK]ₛ x)) := by
  gintro p x H
  gapply (eq_trans' Dom) p ([Dom.MK]ₛ ([Dom.PROJ]ₛ p)) ([Dom.MK]ₛ x)
  · gapply (eq_symm' Dom)
    gapply (Dom.MK_PROJ)
  · gapply (app_cong_arg _ _)
    gexact H

gtheorem Dom.thunk_mk : ∀ w : ▸ Dom.
    (([Dom.thunk]ₛ w) = [Dom.MK]ₛ (inr (inr (inl w)))) := by
  gintro w
  gunfold Dom.thunk
  gsimpl
  grfl

gtheorem Dom.wp_lam : ∀ g : ▸ (Dom → Dom). ∀ Φ : (Dom → Ω).
    ((([Dom.wp]ₛ ([Dom.lam]ₛ g)) Φ) = Φ ([Dom.lam]ₛ g)) := by
  gintro g Φ
  gunfold Dom.wp
  gfix
  grewrite (Dom.proj_lam) g
  gsimpl
  grfl

gtheorem Dom.wp_thunk : ∀ w : ▸ Dom. ∀ Φ : (Dom → Ω).
    ((([Dom.wp]ₛ ([Dom.thunk]ₛ w)) Φ)
      = lift (delay ((([Dom.wp]ₛ (adv 1 w)) Φ)))) := by
  gintro w Φ
  gunfold Dom.wp
  gfix
  grewrite (Dom.proj_thunk) w
  gsimpl
  grfl

gtheorem Dom.wp_mk_num : ∀ k : (Δ Nat). ∀ Φ : (Dom → Ω).
    ((([Dom.wp]ₛ ([Dom.MK]ₛ (inl k))) Φ) = Φ ([Dom.MK]ₛ (inl k))) := by
  gintro k Φ
  gunfold Dom.wp
  gfix
  grewrite (Dom.PROJ_MK) (inl k)
  gsimpl
  grfl

gtheorem Dom.wp_mk_error : ∀ u : (Δ Unit). ∀ Φ : (Dom → Ω).
    ((([Dom.wp]ₛ ([Dom.MK]ₛ (inr (inl u)))) Φ) = ⊥) := by
  gintro u Φ
  gunfold Dom.wp
  gfix
  grewrite (Dom.PROJ_MK) (inr (inl u))
  gsimpl
  grfl

gtheorem Dom.wp_mk_thunk : ∀ w : (▸ Dom). ∀ Φ : (Dom → Ω).
    ((([Dom.wp]ₛ ([Dom.MK]ₛ (inr (inr (inl w))))) Φ)
      = lift (delay ((([Dom.wp]ₛ (adv 1 w)) Φ)))) := by
  gintro w Φ
  gunfold Dom.wp
  gfix
  grewrite (Dom.PROJ_MK) (inr (inr (inl w)))
  gsimpl
  grfl

gtheorem Dom.wp_mk_lam : ∀ g : (▸ (Dom → Dom)). ∀ Φ : (Dom → Ω).
    ((([Dom.wp]ₛ ([Dom.MK]ₛ (inr (inr (inr g))))) Φ) = Φ ([Dom.MK]ₛ (inr (inr (inr g))))) := by
  gintro g Φ
  gunfold Dom.wp
  gfix
  grewrite (Dom.PROJ_MK) (inr (inr (inr g)))
  gsimpl
  grfl

gtheorem Dom.num_mk (k : Nat) :
    (([Dom.num k]ₛ) = [Dom.MK]ₛ (inl (δ(k : Nat)))) := by
  gunfold Dom.num
  grfl

gtheorem Dom.wp_num (k : Nat) : ∀ Φ : (Dom → Ω).
    ((([Dom.wp]ₛ ([Dom.num k]ₛ)) Φ) = Φ ([Dom.num k]ₛ)) := by
  gintro Φ
  grewrite (Dom.num_mk k)
  gapply (Dom.wp_mk_num)

gtheorem Dom.wp_value : ∀ g : ▸ (Dom → Dom). ∀ Φ : (Dom → Ω).
    ((Φ ([Dom.lam]ₛ g)) → (([Dom.wp]ₛ ([Dom.lam]ₛ g)) Φ)) := by
  gintro g Φ H
  grewrite (Dom.wp_lam) g Φ
  gexact H

gtheorem Dom.wp_step : ∀ w : ▸ Dom. ∀ Φ : (Dom → Ω).
    ((lift (delay ((([Dom.wp]ₛ (adv 1 w)) Φ)))) → (([Dom.wp]ₛ ([Dom.thunk]ₛ w)) Φ)) := by
  gintro w Φ H
  grewrite (Dom.wp_thunk) w Φ
  gexact H

gtheorem Dom.wp_mono : ∀ Φ : (Dom → Ω). ∀ Ψ : (Dom → Ω). ∀ p : Dom.
    ((∀ q : Dom. ((Φ q) → Ψ q))
      → ((([Dom.wp]ₛ p) Φ) → (([Dom.wp]ₛ p) Ψ))) := by
  glöb IH
  gintro Φ Ψ p Himp H
  gcases ([Dom.PROJ]ₛ p) with (⟨k, hk⟩ | ⟨r, hr⟩)
  · gassert hp of (p = [Dom.MK]ₛ (inl k))
    · gapply (Dom.eq_of_proj)
      gexact hk
    grewrite hp at H
    grewrite hp
    grewrite (Dom.wp_mk_num) k Ψ
    gapply Himp
    grewrite ← (Dom.wp_mk_num) k Φ
    gexact H
  · gassert hp of (p = [Dom.MK]ₛ (inr r))
    · gapply (Dom.eq_of_proj)
      gexact hr
    gcases (r) with (⟨u, hu⟩ | ⟨r2, hr2⟩)
    · grewrite hu at hp
      grewrite hp at H
      gexfalso
      grewrite ← (Dom.wp_mk_error) u Φ
      gexact H
    · grewrite hr2 at hp
      gcases (r2) with (⟨w, hw⟩ | ⟨g, hg⟩)
      · grewrite hw at hp
        grewrite hp at H
        grewrite hp
        grewrite (Dom.wp_mk_thunk) w Ψ
        gassert Hl of (lift (delay ((([Dom.wp]ₛ (adv 1 w)) Φ))))
        · grewrite ← (Dom.wp_mk_thunk) w Φ
          gexact H
        gmono Hl IH as H' IH'
        gapply IH' Φ Ψ (adv 1 w)
        · gexact Himp
        · gexact H'
      · grewrite hg at hp
        grewrite hp at H
        grewrite hp
        grewrite (Dom.wp_mk_lam) g Ψ
        gapply Himp
        grewrite ← (Dom.wp_mk_lam) g Φ
        gexact H

gtheorem Dom.wp_bind_apply : ∀ x : Dom. ∀ Φ : (Dom → Ω). ∀ Ψ : (Dom → Ω). ∀ p : Dom.
    ((∀ f : Dom. ((Φ f) → (([Dom.wp]ₛ (([Dom.apply]ₛ f) x)) Ψ)))
      → ((([Dom.wp]ₛ p) Φ) → (([Dom.wp]ₛ (([Dom.apply]ₛ p) x)) Ψ))) := by
  glöb IH
  gintro x Φ Ψ p Hcont H
  gcases ([Dom.PROJ]ₛ p) with (⟨k, hk⟩ | ⟨r, hr⟩)
  · gassert hp of (p = [Dom.MK]ₛ (inl k))
    · gapply (Dom.eq_of_proj)
      gexact hk
    grewrite hp
    gapply Hcont
    grewrite ← (Dom.wp_mk_num) k Φ
    grewrite ← hp
    gexact H
  · gassert hp of (p = [Dom.MK]ₛ (inr r))
    · gapply (Dom.eq_of_proj)
      gexact hr
    gcases (r) with (⟨u, hu⟩ | ⟨r2, hr2⟩)
    · grewrite hu at hp
      gexfalso
      grewrite ← (Dom.wp_mk_error) u Φ
      grewrite ← hp
      gexact H
    · grewrite hr2 at hp
      gcases (r2) with (⟨w, hw⟩ | ⟨g, hg⟩)
      · grewrite hw at hp
        gassert hpt of (p = [Dom.thunk]ₛ w)
        · gapply (eq_trans' Dom) p ([Dom.MK]ₛ (inr (inr (inl w)))) ([Dom.thunk]ₛ w)
          · gexact hp
          · gapply (eq_symm' Dom)
            gapply (Dom.thunk_mk)
        grewrite hpt
        grewrite (Dom.apply_thunk) w x
        grewrite (Dom.wp_thunk) (delay ((([Dom.apply]ₛ (adv 1 w)) x))) Ψ
        gassert Hl of (lift (delay ((([Dom.wp]ₛ (adv 1 w)) Φ))))
        · grewrite ← (Dom.wp_thunk) w Φ
          grewrite ← hpt
          gexact H
        gmono Hl IH as H' IH'
        gapply IH' x Φ Ψ (adv 1 w)
        · gexact Hcont
        · gexact H'
      · grewrite hg at hp
        grewrite hp
        gapply Hcont
        grewrite ← (Dom.wp_mk_lam) g Φ
        grewrite ← hp
        gexact H

end wp
gtheorem Dom.wp_cong : ∀ p : Dom. ∀ q : Dom. ∀ Φ : (Dom → Ω).
    ((p = q) → ((([Dom.wp]ₛ p) Φ) → (([Dom.wp]ₛ q) Φ))) := by
  gintro p q Φ h H
  grewrite ← h
  gexact H

def Ctx.tail {n : Nat} (Γ : Ctx (n + 1)) : Ctx n := fun i => Γ i.succ

@[simp] theorem Ctx.tail_cons {n : Nat} (a : Ty) (Γ : Ctx n) :
    Ctx.tail (Ctx.cons a Γ) = Γ := rfl

section step_relation

gdef Dom.Exp : (Δ (Lam 0) → Dom → Ω) → Δ (Lam 0) → Dom → Ω :=
  λ vr. λ e. λ p.
    ([Dom.wp]ₛ p) (λ v. ∃ w : (Δ (Lam 0)). ((⌜(δ(@Steps 0) ⊙ e) ⊙ w⌝) ∧ ((vr w) v)))

gdef Dom.ValArr : (Δ (Lam 0) → Dom → Ω) → (Δ (Lam 0) → Dom → Ω) → Δ (Lam 0) → Dom → Ω :=
  λ va. λ vb. λ w. λ p. ∃ g : ▸ (Dom → Dom).
    ((p = [Dom.lam]ₛ g)
      ∧ (∀ y : (Δ (Lam 0)). lift (delay (∀ q : Dom.
          (((([Dom.Exp]ₛ va) y) q)
            → (([Dom.Exp]ₛ vb) ((δ(@Lam.app 0) ⊙ w) ⊙ y)) ((adv 1 g) q))))))

def Dom.Val : Ty → SYNT ⦃Δ (Lam 0) → Dom → Ω⦄
  | .unit => box(λ w. λ p. ((⌜δ(fun x : Lam 0 => x = Lam.unit) ⊙ w⌝) ∧ (p = [Dom.num 0]ₛ)))
  | .arr a b => box(([Dom.ValArr]ₛ [Dom.Val a]ₛ) [Dom.Val b]ₛ)

theorem Dom.Val_unit_eq :
    Dom.Val Ty.unit = box(λ w. λ p.
      ((⌜δ(fun x : Lam 0 => x = Lam.unit) ⊙ w⌝) ∧ (p = [Dom.num 0]ₛ))) := rfl

theorem Dom.Val_arr_eq (a b : Ty) :
    Dom.Val (Ty.arr a b) = box(([Dom.ValArr]ₛ [Dom.Val a]ₛ) [Dom.Val b]ₛ) := rfl

gtheorem Dom.Exp_intro : ∀ vr : ((Δ (Lam 0)) → Dom → Ω). ∀ e : (Δ (Lam 0)). ∀ p : Dom.
    ((([Dom.wp]ₛ p) (λ v. ∃ w : (Δ (Lam 0)). ((⌜(δ(@Steps 0) ⊙ e) ⊙ w⌝) ∧ ((vr w) v))))
      → (([Dom.Exp]ₛ vr) e) p) := by
  gintro vr e p
  gunfold Dom.Exp
  gsimpl
  gintro H
  gexact H

gtheorem Dom.Exp_elim : ∀ vr : ((Δ (Lam 0)) → Dom → Ω). ∀ e : (Δ (Lam 0)). ∀ p : Dom.
    (((([Dom.Exp]ₛ vr) e) p)
      → ([Dom.wp]ₛ p)
          (λ v. ∃ w : (Δ (Lam 0)). ((⌜(δ(@Steps 0) ⊙ e) ⊙ w⌝) ∧ ((vr w) v)))) := by
  gintro vr e p
  gunfold Dom.Exp
  gsimpl
  gintro H
  gexact H

gtheorem Dom.ValArr_elim : ∀ va : ((Δ (Lam 0)) → Dom → Ω). ∀ vb : ((Δ (Lam 0)) → Dom → Ω).
    ∀ w : (Δ (Lam 0)). ∀ p : Dom.
    ((((([Dom.ValArr]ₛ va) vb) w) p)
      → ∃ g : ▸ (Dom → Dom).
          ((p = [Dom.lam]ₛ g)
            ∧ (∀ y : (Δ (Lam 0)). lift (delay (∀ q : Dom.
                (((([Dom.Exp]ₛ va) y) q)
                  → (([Dom.Exp]ₛ vb) ((δ(@Lam.app 0) ⊙ w) ⊙ y)) ((adv 1 g) q))))))) := by
  gintro va vb w p
  gunfold Dom.ValArr
  gsimpl
  gintro H
  gexact H

gtheorem Dom.ValArr_intro : ∀ va : ((Δ (Lam 0)) → Dom → Ω). ∀ vb : ((Δ (Lam 0)) → Dom → Ω).
    ∀ w : (Δ (Lam 0)). ∀ p : Dom.
    ((∃ g : ▸ (Dom → Dom).
        ((p = [Dom.lam]ₛ g)
          ∧ (∀ y : (Δ (Lam 0)). lift (delay (∀ q : Dom.
              (((([Dom.Exp]ₛ va) y) q)
                → (([Dom.Exp]ₛ vb) ((δ(@Lam.app 0) ⊙ w) ⊙ y)) ((adv 1 g) q)))))))
      → (((([Dom.ValArr]ₛ va) vb) w) p)) := by
  gintro va vb w p
  gunfold Dom.ValArr
  gsimpl
  gintro H
  gexact H

gtheorem Dom.Val_arr_elim (a b : Ty) : ∀ w : (Δ (Lam 0)). ∀ p : Dom.
    ((([Dom.Val (Ty.arr a b)]ₛ w) p)
      → ∃ g : ▸ (Dom → Dom).
          ((p = [Dom.lam]ₛ g)
            ∧ (∀ y : (Δ (Lam 0)). lift (delay (∀ q : Dom.
                (((([Dom.Exp]ₛ [Dom.Val a]ₛ) y) q)
                  → (([Dom.Exp]ₛ [Dom.Val b]ₛ) ((δ(@Lam.app 0) ⊙ w) ⊙ y)) ((adv 1 g) q))))))) := by
  rw [Dom.Val_arr_eq]
  gintro w p
  gsimpl
  gintro H
  gapply (Dom.ValArr_elim) [Dom.Val a]ₛ [Dom.Val b]ₛ w p
  gexact H

gtheorem Dom.Exp_steps_mono : ∀ vr : ((Δ (Lam 0)) → Dom → Ω). ∀ e1 : (Δ (Lam 0)).
    ∀ e2 : (Δ (Lam 0)). ∀ p : Dom.
    ((∀ w : (Δ (Lam 0)).
        ((⌜(δ(@Steps 0) ⊙ e2) ⊙ w⌝) → (⌜(δ(@Steps 0) ⊙ e1) ⊙ w⌝)))
      → ((((([Dom.Exp]ₛ vr) e2) p)) → (([Dom.Exp]ₛ vr) e1) p)) := by
  gintro vr e1 e2 p Himp H
  gapply (Dom.Exp_intro)
  gapply (Dom.wp_mono)
    (λ v. ∃ w : (Δ (Lam 0)). ((⌜(δ(@Steps 0) ⊙ e2) ⊙ w⌝) ∧ ((vr w) v)))
    (λ v. ∃ w : (Δ (Lam 0)). ((⌜(δ(@Steps 0) ⊙ e1) ⊙ w⌝) ∧ ((vr w) v)))
    p
  · gintro v HV
    gcases HV with ⟨w, ⟨Hs, Hv⟩⟩
    gexists w
    gsplit
    · gapply Himp
      gexact Hs
    · gexact Hv
  · gapply (Dom.Exp_elim) vr e2 p
    gexact H

gtheorem Exp_unit :
    (([Dom.Exp]ₛ [Dom.Val Ty.unit]ₛ) δ(Lam.unit : Lam 0)) [Dom.num 0]ₛ := by
  gapply (Dom.Exp_intro)
  grewrite (Dom.wp_num 0)
  gexists δ(Lam.unit : Lam 0)
  gsplit
  · gsimpl
    gembed
    exact Steps.refl _
  · gsplit
    · gsimpl
      gembed
      trivial
    · grfl

gtheorem Exp_thunk (a : Ty) (e : Lam 0) :
    ∀ w : (▸ Dom). ((lift (delay ((([Dom.Exp]ₛ [Dom.Val a]ₛ) δ(e)) (adv 1 w))))
      → (([Dom.Exp]ₛ [Dom.Val a]ₛ) δ(e)) ([Dom.thunk]ₛ w)) := by
  gintro w H
  gapply (Dom.Exp_intro)
  gapply (Dom.wp_step)
  gmono H as H'
  gapply (Dom.Exp_elim) [Dom.Val a]ₛ δ(e) (adv 1 w)
  gexact H'

def consSub {n : Nat} (y : Lam 0) (σ : Fin n → Lam 0) : Fin (n + 1) → Lam 0 := Fin.cases y σ

@[simp] theorem consSub_zero {n : Nat} (y : Lam 0) (σ : Fin n → Lam 0) :
    consSub y σ ⟨0, Nat.succ_pos n⟩ = y := rfl

@[simp] theorem consSub_succ {n : Nat} (y : Lam 0) (σ : Fin n → Lam 0) (i : Fin n) :
    consSub y σ i.succ = σ i := rfl

theorem consSub_tail {n : Nat} (y : Lam 0) (σ : Fin n → Lam 0) :
    (fun i => consSub y σ i.succ) = σ := rfl

def SubstOk : (n : Nat) → Ctx n → (Fin n → Lam 0) → SYNT ⦃[Env n] → Ω⦄
  | 0, _, _ => box(λ _ : [Env 0]. ⊤)
  | n + 1, Γ, σ =>
    box(λ p.
      (([SubstOk n (Ctx.tail Γ) (fun i => σ i.succ)]ₛ (π₁ p))
        ∧ ((([Dom.Exp]ₛ [Dom.Val (Γ ⟨0, Nat.succ_pos n⟩)]ₛ)
              δ(σ ⟨0, Nat.succ_pos n⟩)) (π₂ p))))

gtheorem SubstOk_fst (n : Nat) (Γ : Ctx (n + 1)) (σ : Fin (n + 1) → Lam 0) :
    ∀ p : [Env (n + 1)].
      (([SubstOk (n + 1) Γ σ]ₛ p)
        → ([SubstOk n (Ctx.tail Γ) (fun i => σ i.succ)]ₛ (π₁ p))) := by
  gintro p
  gsimpl
  gintro H
  gcases H with ⟨H1, H2⟩
  gexact H1

gtheorem SubstOk_snd (n : Nat) (Γ : Ctx (n + 1)) (σ : Fin (n + 1) → Lam 0) :
    ∀ p : [Env (n + 1)].
      (([SubstOk (n + 1) Γ σ]ₛ p)
        → (([Dom.Exp]ₛ [Dom.Val (Γ ⟨0, Nat.succ_pos n⟩)]ₛ)
              δ(σ ⟨0, Nat.succ_pos n⟩)) (π₂ p)) := by
  gintro p
  gsimpl
  gintro H
  gcases H with ⟨H1, H2⟩
  gexact H2

gtheorem SubstOk_cons (n : Nat) (Γ : Ctx n) (σ : Fin n → Lam 0) (a : Ty) (y : Lam 0) :
    ∀ ρ : [Env n]. ∀ q : Dom.
      (([SubstOk n Γ σ]ₛ ρ)
        → ((((([Dom.Exp]ₛ [Dom.Val a]ₛ) δ(y)) q))
          → ([SubstOk (n + 1) (Ctx.cons a Γ) (consSub y σ)]ₛ ⟨ρ, q⟩))) := by
  gintro ρ q H1 H2
  gsimpl
  simp only [Ctx.tail_cons, consSub_tail, consSub_zero, Ctx.cons_zero]
  gsplit
  · gexact H1
  · gexact H2

gtheorem SubstOk_lookup (n : Nat) (Γ : Ctx n) (σ : Fin n → Lam 0) (i : Fin n) :
    ∀ ρ : [Env n].
      (([SubstOk n Γ σ]ₛ ρ)
        → (([Dom.Exp]ₛ [Dom.Val (Γ i)]ₛ) δ(σ i)) ([lookup n i]ₛ ρ)) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ ?_ i
    · gintro ρ H
      gsimpl
      gapply (SubstOk_snd n Γ σ)
      gexact H
    · intro j
      gintro ρ H
      gsimpl
      gapply (ih (Ctx.tail Γ) (fun i => σ i.succ) j)
      gapply (SubstOk_fst n Γ σ)
      gexact H

gtheorem steps_app (n : Nat) (σ : Fin n → Lam 0) (t u : Lam n) :
    ∀ w : (Δ (Lam 0)). ∀ w' : (Δ (Lam 0)).
        ((⌜(δ(@Steps 0) ⊙ δ(sub σ t)) ⊙ w⌝)
          → ((⌜(δ(@Steps 0) ⊙ ((δ(@Lam.app 0) ⊙ w) ⊙ δ(sub σ u))) ⊙ w'⌝)
            → (⌜(δ(@Steps 0) ⊙ δ(sub σ (Lam.app t u))) ⊙ w'⌝))) := by
  gpoints w
  gpoints w'
  gpose (embed_sem.pure_imp2 (Steps (sub σ t) w) (Steps (Lam.app w (sub σ u)) w')
    (Steps (sub σ (Lam.app t u)) w')
    (fun h1 h2 => Steps.trans (Steps.appL (sub σ u) h1) h2)) as PI
  gexact PI

gtheorem steps_beta (n : Nat) (σ : Fin n → Lam 0) (t : Lam (n + 1)) (y : Lam 0)
    (el eb : Lam 0) (hl : el = sub σ (Lam.lam t)) (hb : eb = sub (consSub y σ) t) :
    ∀ w : (Δ (Lam 0)).
        ((⌜(δ(@Steps 0) ⊙ δ(eb)) ⊙ w⌝)
          → (⌜(δ(@Steps 0) ⊙ ((δ(@Lam.app 0) ⊙ δ(el)) ⊙ δ(y))) ⊙ w⌝)) := by
  gpoints w
  gpose (embed_sem.pure_imp1 (Steps eb w) (Steps (Lam.app el y) w)
    (fun h => by
      subst hl
      subst hb
      exact Steps.trans (Steps.beta (sub (liftSub σ) t) y) (by rw [subst0_sub]; exact h))) as PI
  gexact PI

gtheorem steps_unfold (n : Nat) (σ : Fin n → Lam 0) (t : Lam (n + 1))
    (ef eb : Lam 0) (hf : ef = sub σ (Lam.fix t))
    (hb : eb = sub (consSub (sub σ (Lam.fix t)) σ) t) :
    ∀ w : (Δ (Lam 0)).
        ((⌜(δ(@Steps 0) ⊙ δ(eb)) ⊙ w⌝) → (⌜(δ(@Steps 0) ⊙ δ(ef)) ⊙ w⌝)) := by
  gpoints w
  gpose (embed_sem.pure_imp1 (Steps eb w) (Steps ef w)
    (fun h => by
      subst hf
      subst hb
      exact Steps.trans (Steps.unfold (sub (liftSub σ) t)) (by rw [subst0_sub]; exact h))) as PI
  gexact PI

abbrev Rel (n : Nat) (Γ : Ctx n) (σ : Fin n → Lam 0) (e : Lam n) (a : Ty) : Prop :=
  ⊢ᵍ ⟪∀ ρ : [Env n].
      (([SubstOk n Γ σ]ₛ ρ) → (([Dom.Exp]ₛ [Dom.Val a]ₛ) δ(sub σ e)) ([interp n e]ₛ ρ))⟫

theorem fundamental_unit (n : Nat) (Γ : Ctx n) (σ : Fin n → Lam 0) :
    Rel n Γ σ Lam.unit Ty.unit := by
  gintro ρ H
  gsimpl
  gapply (Exp_unit)

theorem fundamental_var (n : Nat) (Γ : Ctx n) (σ : Fin n → Lam 0) (i : Fin n) :
    Rel n Γ σ (Lam.var i) (Γ i) := by
  gintro ρ H
  gapply (SubstOk_lookup n Γ σ i)
  gexact H

theorem fundamental_app (n : Nat) (Γ : Ctx n) (σ : Fin n → Lam 0) (t u : Lam n) (a b : Ty)
    (iht : ∀ σ' : Fin n → Lam 0, Rel n Γ σ' t (Ty.arr a b))
    (ihu : ∀ σ' : Fin n → Lam 0, Rel n Γ σ' u a) :
    Rel n Γ σ (Lam.app t u) b := by
  gintro ρ H
  gsimpl
  gapply (Dom.Exp_intro)
  gapply (Dom.wp_bind_apply) ([interp n u]ₛ ρ)
    (λ f. ∃ w : (Δ (Lam 0)).
      ((⌜(δ(@Steps 0) ⊙ δ(sub σ t)) ⊙ w⌝) ∧ (([Dom.Val (Ty.arr a b)]ₛ w) f)))
    (λ v. ∃ w : (Δ (Lam 0)).
      ((⌜(δ(@Steps 0) ⊙ δ(sub σ (Lam.app t u))) ⊙ w⌝) ∧ (([Dom.Val b]ₛ w) v)))
    ([interp n t]ₛ ρ)
  · gintro f Hf
    gcases Hf with ⟨w, ⟨Hs, Hv⟩⟩
    gassert HE of (∃ g : ▸ (Dom → Dom).
      ((f = [Dom.lam]ₛ g)
        ∧ (∀ y : (Δ (Lam 0)). lift (delay (∀ q : Dom.
            (((([Dom.Exp]ₛ [Dom.Val a]ₛ) y) q)
              → (([Dom.Exp]ₛ [Dom.Val b]ₛ) ((δ(@Lam.app 0) ⊙ w) ⊙ y)) ((adv 1 g) q)))))))
    · gapply (Dom.Val_arr_elim a b) w f
      gexact Hv
    gcases HE with ⟨g, ⟨heq, Hall⟩⟩
    gspecialize Hall δ(sub σ u) as Hlater
    gapply (Dom.wp_cong) ([Dom.thunk]ₛ (delay ((adv 1 g) ([interp n u]ₛ ρ))))
      (([Dom.apply]ₛ f) ([interp n u]ₛ ρ))
      (λ v. ∃ w : (Δ (Lam 0)).
        ((⌜(δ(@Steps 0) ⊙ δ(sub σ (Lam.app t u))) ⊙ w⌝) ∧ (([Dom.Val b]ₛ w) v)))
    · gapply (eq_symm' Dom)
      gapply (eq_trans' Dom) (([Dom.apply]ₛ f) ([interp n u]ₛ ρ))
        (([Dom.apply]ₛ ([Dom.lam]ₛ g)) ([interp n u]ₛ ρ))
        ([Dom.thunk]ₛ (delay ((adv 1 g) ([interp n u]ₛ ρ))))
      · gapply (Dom.apply_cong)
        · gexact heq
        · grfl
      · gapply (Dom.apply_lam) g ([interp n u]ₛ ρ)
    · gapply (Dom.wp_step)
      gmono Hlater as HL
      gapply (Dom.Exp_elim) [Dom.Val b]ₛ δ(sub σ (Lam.app t u)) ((adv 1 g) ([interp n u]ₛ ρ))
      gapply (Dom.Exp_steps_mono) [Dom.Val b]ₛ δ(sub σ (Lam.app t u))
        ((δ(@Lam.app 0) ⊙ w) ⊙ δ(sub σ u)) ((adv 1 g) ([interp n u]ₛ ρ))
      · gintro w' HS
        gapply (steps_app n σ t u) w w'
        · gexact Hs
        · gexact HS
      · gapply HL
        gapply (ihu σ) ρ
        gexact H
  · gapply (Dom.Exp_elim) [Dom.Val (Ty.arr a b)]ₛ δ(sub σ t) ([interp n t]ₛ ρ)
    gapply (iht σ)
    gexact H

theorem fundamental_lam (n : Nat) (Γ : Ctx n) (σ : Fin n → Lam 0) (t : Lam (n + 1)) (a b : Ty)
    (ih : ∀ σ' : Fin (n + 1) → Lam 0, Rel (n + 1) (Ctx.cons a Γ) σ' t b) :
    Rel n Γ σ (Lam.lam t) (Ty.arr a b) := by
  gintro ρ H
  generalize hgl : sub σ (Lam.lam t) = el
  gsimpl
  gapply (Dom.Exp_intro)
  gapply (Dom.wp_value)
  gexists δ(el)
  gsplit
  · gsimpl
    gembed
    exact Steps.refl _
  · rw [Dom.Val_arr_eq]
    gsimpl
    gapply (Dom.ValArr_intro)
    gexists (delay (λ v. [interp (n + 1) t]ₛ ⟨ρ, v⟩))
    gsplit
    · grfl
    · gpoints y
      gnext
      gintro q Hy
      gsimpl
      gpose (steps_beta n σ t y el (sub (consSub y σ) t) hgl.symm rfl) as BR
      gapply (Dom.Exp_steps_mono) [Dom.Val b]ₛ ((δ(@Lam.app 0) ⊙ δ(el)) ⊙ δ(y))
        δ(sub (consSub y σ) t) ([interp (n + 1) t]ₛ ⟨ρ, q⟩)
      · gexact BR
      · gapply (ih (consSub y σ)) ⟨ρ, q⟩
        gsimpl
        gapply (SubstOk_cons n Γ σ a y) ρ q
        · gexact H
        · gexact Hy

theorem fundamental_fix (n : Nat) (Γ : Ctx n) (σ : Fin n → Lam 0) (t : Lam (n + 1)) (a : Ty)
    (ih : ∀ σ' : Fin (n + 1) → Lam 0, Rel (n + 1) (Ctx.cons a Γ) σ' t a) :
    Rel n Γ σ (Lam.fix t) a := by
  glöb LIH
  gintro ρ H
  generalize hgf : sub σ (Lam.fix t) = ef
  gsimpl
  gfix
  gapply (Exp_thunk a ef)
  gmono LIH as LH
  gpose (steps_unfold n σ t ef (sub (consSub ef σ) t) hgf.symm (by rw [hgf])) as BR
  gapply (Dom.Exp_steps_mono) [Dom.Val a]ₛ δ(ef) δ(sub (consSub ef σ) t)
    ([interp (n + 1) t]ₛ ⟨ρ, fix y. [Dom.thunk]ₛ (delay ([interp (n + 1) t]ₛ ⟨ρ, adv 1 y⟩))⟩)
  · gexact BR
  · gapply (ih (consSub ef σ)) ⟨ρ, fix y. [Dom.thunk]ₛ (delay ([interp (n + 1) t]ₛ ⟨ρ, adv 1 y⟩))⟩
    gsimpl
    gapply (SubstOk_cons n Γ σ a ef) ρ
      (fix y. [Dom.thunk]ₛ (delay ([interp (n + 1) t]ₛ ⟨ρ, adv 1 y⟩)))
    · gexact H
    · gapply LH ρ
      gexact H

theorem fundamental {n : Nat} {Γ : Ctx n} {e : Lam n} {a : Ty} (h : Typing Γ e a) :
    ∀ σ : Fin n → Lam 0, Rel n Γ σ e a := by
  induction h with
  | unit => exact fun σ => fundamental_unit _ _ σ
  | var i => exact fun σ => fundamental_var _ _ σ i
  | app _ _ iht ihu => exact fun σ => fundamental_app _ _ σ _ _ _ _ iht ihu
  | lam _ ih => exact fun σ => fundamental_lam _ _ σ _ _ _ ih
  | @«fix» _ _ _ _ _ ih => exact fun σ => fundamental_fix _ _ σ _ _ ih

end step_relation

section adequacy

open CategoryTheory Logic Extract

theorem sub_closed (σ : Fin 0 → Lam 0) (e : Lam 0) : sub σ e = e := by
  obtain rfl : σ = fun i => Lam.var i := funext fun i => i.elim0
  exact sub_var e

gtheorem Dom.wp_step_inv : ∀ w : ▸ Dom. ∀ Φ : (Dom → Ω).
    ((([Dom.wp]ₛ ([Dom.thunk]ₛ w)) Φ) → (lift (delay ((([Dom.wp]ₛ (adv 1 w)) Φ))))) := by
  gintro w Φ H
  grewrite ← (Dom.wp_thunk) w Φ
  gexact H

gtheorem Dom.wp_num_inv (k : Nat) : ∀ Φ : (Dom → Ω).
    ((([Dom.wp]ₛ ([Dom.num k]ₛ)) Φ) → (Φ ([Dom.num k]ₛ))) := by
  gintro Φ H
  grewrite ← (Dom.wp_num k) Φ
  gexact H

gtheorem Dom.Exp_step_inv : ∀ vr : ((Δ (Lam 0)) → Dom → Ω). ∀ e : (Δ (Lam 0)). ∀ t : (▸ Dom).
    (((([Dom.Exp]ₛ vr) e) ([Dom.thunk]ₛ t))
      → (lift (delay ((([Dom.Exp]ₛ vr) e) (adv 1 t))))) := by
  gintro vr e t H
  gassert HW of (lift (delay ((([Dom.wp]ₛ (adv 1 t))
    (λ v. ∃ w : (Δ (Lam 0)). ((⌜(δ(@Steps 0) ⊙ e) ⊙ w⌝) ∧ ((vr w) v)))))))
  · gapply (Dom.wp_step_inv) t
      (λ v. ∃ w : (Δ (Lam 0)). ((⌜(δ(@Steps 0) ⊙ e) ⊙ w⌝) ∧ ((vr w) v)))
    gapply (Dom.Exp_elim) vr e ([Dom.thunk]ₛ t)
    gexact H
  gmono HW as HW'
  gapply (Dom.Exp_intro)
  gexact HW'

abbrev Dom.step (r : SYNT ⦃Dom⦄) : SYNT ⦃Dom⦄ := box([Dom.thunk]ₛ (delay [r]ₛ))

abbrev denote (e : Lam 0) : SYNT ⦃Dom⦄ := box([interp 0 e]ₛ δ(()))

abbrev EqG (p q : SYNT ⦃Dom⦄) : Prop := ⊢ᵍ ⟪([p]ₛ = [q]ₛ)⟫

abbrev ExpProp (a : Ty) (e : Lam 0) (r : SYNT ⦃Dom⦄) : EXPR :=
  ⟪(([Dom.Exp]ₛ [Dom.Val a]ₛ) δ(e)) [r]ₛ⟫

gtheorem Dom.Exp_cong : ∀ vr : (Δ (Lam 0) → Dom → Ω). ∀ e : (Δ (Lam 0)).
    ∀ p : Dom. ∀ q : Dom.
    ((p = q) → ((([Dom.Exp]ₛ vr) e) p) → ((([Dom.Exp]ₛ vr) e) q)) := by
  gintro vr e p q Heq H
  grewrite ← Heq
  gexact H

theorem Exp_cong (a : Ty) (e : Lam 0) (p q : SYNT ⦃Dom⦄) (h : EqG p q) :
    ⊢ᵍ ((ExpProp a e p).impl (ExpProp a e q)) := by
  unfold ExpProp
  gintro H
  gapply (Dom.Exp_cong) [Dom.Val a]ₛ δ(e) [p]ₛ [q]ₛ
  · gpose (h) as Heq
    gexact Heq
  · gexact H

theorem Exp_step (a : Ty) (e : Lam 0) (r : SYNT ⦃Dom⦄) :
    ⊢ᵍ ((ExpProp a e (Dom.step r)).impl (ExpProp a e r).delay.lift) := by
  unfold ExpProp
  gintro H
  gsimpl
  gapply (Dom.Exp_step_inv) [Dom.Val a]ₛ δ(e) (delay [r]ₛ)
  gexact H

theorem Exp_value (e : Lam 0) :
    ⊢ᵍ ((ExpProp Ty.unit e (Dom.num 0)).impl ⟪⌜δ(Steps e Lam.unit)⌝⟫) := by
  unfold ExpProp
  rw [Dom.Val_unit_eq]
  gintro H
  gassert HW of (∃ w : (Δ (Lam 0)).
    ((⌜(δ(@Steps 0) ⊙ δ(e)) ⊙ w⌝)
      ∧ ((⌜δ(fun x : Lam 0 => x = Lam.unit) ⊙ w⌝) ∧ ([Dom.num 0]ₛ = [Dom.num 0]ₛ))))
  · gapply (Dom.wp_num_inv 0) (λ v. ∃ w : (Δ (Lam 0)).
      ((⌜(δ(@Steps 0) ⊙ δ(e)) ⊙ w⌝)
        ∧ ((⌜δ(fun x : Lam 0 => x = Lam.unit) ⊙ w⌝) ∧ (v = [Dom.num 0]ₛ))))
    gapply (Dom.Exp_elim) (λ w. λ p.
      ((⌜δ(fun x : Lam 0 => x = Lam.unit) ⊙ w⌝) ∧ (p = [Dom.num 0]ₛ))) δ(e) [Dom.num 0]ₛ
    gexact H
  gcases HW with ⟨w, ⟨HS, HV⟩⟩
  gcases HV with ⟨HU, HN⟩
  gapply (embed_sem.pure_close₂_all (Lam 0) (fun x : Lam 0 => x = Lam.unit) (Steps e)
    (Steps e Lam.unit) (fun a hu hs => hu ▸ hs)) w
  · gexact HU
  · gexact HS

theorem Exp_typed (a : Ty) (e : Lam 0) (r : SYNT ⦃Dom⦄) :
    TYPED [[]] (ExpProp a e r) TYPE.prop := by
  have H : ⊢ᵍ ((ExpProp a e r).impl (ExpProp a e r)) := by
    gintro H
    gexact H
  exact (TYPED.impl_inversion H.goal.typed).2.1

def Runs : Nat → SYNT ⦃Dom⦄ → SYNT ⦃Dom⦄ → Prop
  | 0, p, q => EqG p q
  | k + 1, p, q => ∃ r, EqG p (Dom.step r) ∧ Runs k r q

theorem valid_of_runs (a : Ty) (e : Lam 0) : ∀ (k : Nat) (p q : SYNT ⦃Dom⦄), Runs k p q →
    Valid (ExpProp a e p) → Valid (ExpProp a e q) := by
  intro k
  induction k with
  | zero =>
    intro p q heq hv
    exact valid_mp (Exp_cong a e p q heq) hv
  | succ k ih =>
    rintro p q ⟨r, heq, hrun⟩ hv
    have hv' := valid_mp (Exp_cong a e p (Dom.step r) heq) hv
    exact ih r q hrun (valid_later (Exp_typed a e r) (valid_mp (Exp_step a e r) hv'))

theorem fundamental_closed (Γ : Ctx 0) (e : Lam 0) (a : Ty) (h : Typing Γ e a) :
    ⊢ᵍ (ExpProp a e (denote e)) := by
  unfold ExpProp
  have H := fundamental h Fin.elim0
  simp only [Rel, sub_closed] at H
  gsimpl
  gapply (H)
  gtrivial

theorem adequacy (Γ : Ctx 0) (e : Lam 0) (h : Typing Γ e Ty.unit) (k : Nat)
    (hrun : Runs k (denote e) (Dom.num 0)) : Steps e Lam.unit :=
  valid_pure (valid_mp (Exp_value e)
    (valid_of_runs Ty.unit e k _ _ hrun (valid_of_goal (fundamental_closed Γ e Ty.unit h))))

example (Γ : Ctx 0) : Steps (Lam.app (Lam.lam (Lam.var 0)) Lam.unit : Lam 0) Lam.unit := by
  apply adequacy Γ _ (Typing.app (Typing.lam (Typing.var 0)) Typing.unit) 1
  refine ⟨denote Lam.unit, ?_, ?_⟩
  · gsimpl
    gapply (Dom.apply_lam) (delay (λ v : Dom. v)) ([Dom.num 0]ₛ)
  · change EqG _ _
    gsimpl
    grfl

namespace Combinators

def K {n : Nat} : Lam n := .lam (.lam (.var 1))

def S {n : Nat} : Lam n :=
  .lam (.lam (.lam (.app (.app (.var 2) (.var 0)) (.app (.var 1) (.var 0)))))

def skkUnit : Lam 0 := .app (.app (.app S K) K) .unit

theorem K_typing {n : Nat} (Γ : Ctx n) (a b : Ty) :
    Typing Γ K (.arr a (.arr b a)) :=
  .lam (.lam (.var 1))

theorem S_typing {n : Nat} (Γ : Ctx n) (a b c : Ty) :
    Typing Γ S (.arr (.arr a (.arr b c)) (.arr (.arr a b) (.arr a c))) :=
  .lam (.lam (.lam (.app (.app (.var 2) (.var 0)) (.app (.var 1) (.var 0)))))

theorem skkUnit_typing (Γ : Ctx 0) : Typing Γ skkUnit .unit :=
  .app (.app (.app (S_typing Γ .unit (.arr .unit .unit) .unit)
    (K_typing Γ .unit (.arr .unit .unit))) (K_typing Γ .unit .unit)) .unit

def ticks : Nat → SYNT ⦃Dom⦄ → SYNT ⦃Dom⦄
  | 0, p => p
  | k + 1, p => Dom.step (ticks k p)

theorem runs_of_eq_ticks (k : Nat) (p q : SYNT ⦃Dom⦄) (h : EqG p (ticks k q)) :
    Runs k p q := by
  induction k generalizing p with
  | zero => exact h
  | succ k ih =>
    refine ⟨ticks k q, h, ih _ ?_⟩
    grfl

theorem skkUnit_eq : EqG (denote skkUnit) (ticks 5 (Dom.num 0)) := by
  simp only [ticks]
  gsimpl
  grewrite (Dom.apply_lam)
  grewrite (Dom.apply_thunk)
  grewrite (Dom.apply_thunk)
  gcong
  gnext
  grewrite (Dom.apply_lam)
  grewrite (Dom.apply_thunk)
  gcong
  gnext
  grewrite (Dom.apply_lam)
  gcong
  gnext
  grewrite (Dom.apply_lam)
  grewrite (Dom.apply_thunk)
  gcong
  gnext
  grewrite (Dom.apply_lam)
  grfl

theorem skkUnit_runs : Runs 5 (denote skkUnit) (Dom.num 0) :=
  runs_of_eq_ticks 5 _ _ skkUnit_eq

theorem skkUnit_adequacy (Γ : Ctx 0) : Steps skkUnit Lam.unit :=
  adequacy Γ skkUnit (skkUnit_typing Γ) 5 skkUnit_runs

end Combinators

end adequacy

end Lam

end
