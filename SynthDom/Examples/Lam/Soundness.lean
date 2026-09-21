module
public import SynthDom
public import SynthDom.Examples.Lam.Model
public import SynthDom.Examples.Lam.Language
@[expose] public section
namespace Lam

gtheorem eq_trans' (A : TYPE) :
    ∀ x : A. ∀ y : A. ∀ z : A. ((x = y) → ((y = z) → (x = z))) := by
  gintro x y z h1 h2
  grewrite h1
  gexact h2

gtheorem app_cong_arg (A B : TYPE) :
    ∀ f : (A → B). ∀ x : A. ∀ x' : A. ((x = x') → ((f x) = (f x'))) := by
  gintro f x x' h
  grewrite h
  grfl

gtheorem pair_cong_snd (A B : TYPE) : ∀ a : A. ∀ b : B. ∀ b' : B.
    ((b = b') → ((⟨a, b⟩ : (A × B)) = ⟨a, b'⟩)) := by
  gintro a b b' h
  gsimpl
  grewrite h
  grfl

gtheorem Env.lift_fst' (n m : Nat) (E : SYNT ⦃[Env m] → [Env n]⦄) :
    ∀ p : [Env (m + 1)]. (([E]ₛ (π₁ p)) = π₁ ([Env.lift n m E]ₛ p)) := by
  gintro p
  gunfold Env.lift
  gunfold Env.liftP
  gsimpl
  grfl

gtheorem Env.lift_snd (n m : Nat) (E : SYNT ⦃[Env m] → [Env n]⦄) :
    ∀ p : [Env (m + 1)]. ((π₂ p) = π₂ ([Env.lift n m E]ₛ p)) := by
  gintro p
  gunfold Env.lift
  gunfold Env.liftP
  gsimpl
  grfl

gtheorem Env.lift_pair (n m : Nat) (E : SYNT ⦃[Env m] → [Env n]⦄) :
    ∀ q : [Env m]. ∀ v : Dom. (([Env.lift n m E]ₛ ⟨q, v⟩) = ⟨[E]ₛ q, v⟩) := by
  gintro q v
  gunfold Env.lift
  gunfold Env.liftP
  gsimpl
  grfl

gdef Env.wk (m : Nat) : [Env (m + 1)] → [Env m] :=
  λ p. π₁ p

abbrev AgreeAlong (n m : Nat) (a : SYNT ⦃[Env m] → Dom⦄) (E : SYNT ⦃[Env m] → [Env n]⦄)
    (b : SYNT ⦃[Env n] → Dom⦄) : Prop :=
  ⊢ᵍ ⟪∀ ρ : [Env m]. (([a]ₛ ρ) = [b]ₛ ([E]ₛ ρ))⟫

theorem Env.lift_lookup (n m : Nat) (ξ : Fin n → Fin m) (E : SYNT ⦃[Env m] → [Env n]⦄)
    (hE : ∀ i : Fin n, AgreeAlong n m (lookup m (ξ i)) E (lookup n i)) :
    ∀ i : Fin (n + 1),
      AgreeAlong (n + 1) (m + 1) (lookup (m + 1) (liftRen ξ i)) (Env.lift n m E)
        (lookup (n + 1) i) := by
  intro i
  refine Fin.cases ?_ ?_ i
  · gintro ρ
    gsimpl
    gapply (Env.lift_snd n m E)
  · intro j
    gintro ρ
    gsimpl
    gapply (eq_trans' Dom) ([lookup m (ξ j)]ₛ (π₁ ρ))
      ([lookup n j]ₛ ([E]ₛ (π₁ ρ))) ([lookup n j]ₛ (π₁ ([Env.lift n m E]ₛ ρ)))
    · gapply (hE j)
    · gapply (app_cong_arg _ _)
      gapply (Env.lift_fst' n m E)
gtheorem Env.wk_apply (m : Nat) :
    ∀ p : [Env (m + 1)]. (([Env.wk m]ₛ p) = π₁ p) := by
  gintro p
  gunfold Env.wk
  gsimpl
  grfl

theorem Env.wk_lookup (m : Nat) :
    ∀ i : Fin m, AgreeAlong m (m + 1) (lookup (m + 1) (Fin.succ i)) (Env.wk m) (lookup m i) := by
  intro i
  gintro ρ
  gunfold Env.wk
  gsimpl
  grfl

gtheorem eq_symm' (A : TYPE) : ∀ x : A. ∀ y : A. ((x = y) → (y = x)) := by
  gintro x y h
  grewrite h
  grfl

gtheorem proj1_cong (A B : TYPE) :
    ∀ p : (A × B). ∀ q : (A × B). ((p = q) → ((π₁ p) = π₁ q)) := by
  gintro p q h
  grewrite h
  grfl

gtheorem proj2_cong (A B : TYPE) :
    ∀ p : (A × B). ∀ q : (A × B). ((p = q) → ((π₂ p) = π₂ q)) := by
  gintro p q h
  grewrite h
  grfl

gdef Env.extP (n : Nat) : ([Env n] → Dom) → [Env n] → [Env (n + 1)] :=
  λ u. λ ρ. ⟨ρ, u ρ⟩

gdef Env.ext (n : Nat) (U : SYNT ⦃[Env n] → Dom⦄) : [Env n] → [Env (n + 1)] :=
  [Env.extP n]ₛ [U]ₛ

gtheorem Env.ext_apply' (n : Nat) (U : SYNT ⦃[Env n] → Dom⦄) :
    ∀ ρ : [Env n]. ((⟨ρ, [U]ₛ ρ⟩ : ([Env n] × Dom)) = [Env.ext n U]ₛ ρ) := by
  gintro ρ
  gunfold Env.ext
  gunfold Env.extP
  gsimpl
  grfl

theorem Env.ext_lookup (n : Nat) (u : Lam n) :
    ∀ i : Fin (n + 1),
      AgreeAlong (n + 1) n (interp n (substHead u i)) (Env.ext n (interp n u))
        (lookup (n + 1) i) := by
  intro i
  refine Fin.cases ?_ ?_ i
  · gintro ρ
    gsimpl
    gapply (eq_trans' Dom) ([interp n u]ₛ ρ) (π₂ (⟨ρ, [interp n u]ₛ ρ⟩ : ([Env n] × Dom)))
      (π₂ ([Env.ext n (interp n u)]ₛ ρ))
    · grfl
    · gapply (proj2_cong (Env n) Dom) (⟨ρ, [interp n u]ₛ ρ⟩ : ([Env n] × Dom))
        ([Env.ext n (interp n u)]ₛ ρ)
      gapply (Env.ext_apply' n (interp n u))
  · intro j
    gintro ρ
    gsimpl
    gapply (app_cong_arg _ _)
    gapply (eq_trans' (Env n)) ρ (π₁ (⟨ρ, [interp n u]ₛ ρ⟩ : ([Env n] × Dom)))
      (π₁ ([Env.ext n (interp n u)]ₛ ρ))
    · grfl
    · gapply (proj1_cong (Env n) Dom) (⟨ρ, [interp n u]ₛ ρ⟩ : ([Env n] × Dom))
        ([Env.ext n (interp n u)]ₛ ρ)
      gapply (Env.ext_apply' n (interp n u))

gtheorem interp_snd_cong (n : Nat) (t : Lam (n + 1)) :
    ∀ ρ : [Env n]. ∀ x : Dom. ∀ y : Dom.
      ((x = y) → (([interp (n + 1) t]ₛ ⟨ρ, x⟩) = [interp (n + 1) t]ₛ ⟨ρ, y⟩)) := by
  gintro ρ x y h
  gapply (app_cong_arg _ _)
  gapply (pair_cong_snd (Env n) Dom)
  gexact h

theorem interp_fix_cong (n m : Nat) (t : Lam (n + 1)) (t' : Lam (m + 1))
    (E : SYNT ⦃[Env m] → [Env n]⦄)
    (h : ⊢ᵍ ⟪∀ ρ : [Env m]. ∀ x : Dom.
        (([interp (m + 1) t']ₛ ⟨ρ, x⟩) = [interp (n + 1) t]ₛ ⟨[E]ₛ ρ, x⟩)⟫) :
    AgreeAlong n m (interp m (Lam.fix t')) E (interp n (Lam.fix t)) := by
  glöb L
  gintro ρ
  gsimpl
  gapply (eq_trans' Dom) ([interp m (Lam.fix t')]ₛ ρ)
    ([Dom.thunk]ₛ (delay ([interp (m + 1) t']ₛ ⟨ρ, [interp m (Lam.fix t')]ₛ ρ⟩)))
    ([interp n (Lam.fix t)]ₛ ([E]ₛ ρ))
  · gapply (interp_fix_apply m t') ρ
  · gapply (eq_symm' Dom)
    gapply (eq_trans' Dom) ([interp n (Lam.fix t)]ₛ ([E]ₛ ρ))
      ([Dom.thunk]ₛ (delay ([interp (n + 1) t]ₛ
        ⟨[E]ₛ ρ, [interp n (Lam.fix t)]ₛ ([E]ₛ ρ)⟩)))
      ([Dom.thunk]ₛ (delay ([interp (m + 1) t']ₛ ⟨ρ, [interp m (Lam.fix t')]ₛ ρ⟩)))
    · gapply (interp_fix_apply n t) ([E]ₛ ρ)
    · gapply (Dom.thunk_delay_cong_tm_later)
        ([interp (n + 1) t]ₛ ⟨[E]ₛ ρ, [interp n (Lam.fix t)]ₛ ([E]ₛ ρ)⟩)
        ([interp (m + 1) t']ₛ ⟨ρ, [interp m (Lam.fix t')]ₛ ρ⟩)
      gmono L as L'
      gapply (eq_trans' Dom)
        ([interp (n + 1) t]ₛ ⟨[E]ₛ ρ, [interp n (Lam.fix t)]ₛ ([E]ₛ ρ)⟩)
        ([interp (n + 1) t]ₛ ⟨[E]ₛ ρ, [interp m (Lam.fix t')]ₛ ρ⟩)
        ([interp (m + 1) t']ₛ ⟨ρ, [interp m (Lam.fix t')]ₛ ρ⟩)
      · gapply (interp_snd_cong n t) ([E]ₛ ρ)
          ([interp n (Lam.fix t)]ₛ ([E]ₛ ρ)) ([interp m (Lam.fix t')]ₛ ρ)
        gapply (eq_symm' Dom)
        gapply L' ρ
      · gapply (eq_symm' Dom)
        gapply (h) ρ ([interp m (Lam.fix t')]ₛ ρ)

theorem interp_ren : ∀ {n : Nat} (t : Lam n) {m : Nat} (ξ : Fin n → Fin m)
    (E : SYNT ⦃[Env m] → [Env n]⦄)
    (_hE : ∀ i : Fin n, AgreeAlong n m (lookup m (ξ i)) E (lookup n i)),
    AgreeAlong n m (interp m (ren ξ t)) E (interp n t) := by
  intro n t
  induction t with
  | @unit n =>
    intro m ξ E hE
    gintro ρ
    gsimpl
    grfl
  | @var n i =>
    intro m ξ E hE
    gintro ρ
    gapply (hE i)
  | @app n t u iht ihu =>
    intro m ξ E hE
    gintro ρ
    gsimpl
    gapply (Dom.apply_cong)
    · gapply (iht ξ E hE)
    · gapply (ihu ξ E hE)
  | @lam n t iht =>
    intro m ξ E hE
    have ih := iht (liftRen ξ) (Env.lift n m E) (Env.lift_lookup n m ξ E hE)
    gintro ρ
    gsimpl
    gassert Hfn of ((λ v. [interp (m + 1) (ren (liftRen ξ) t)]ₛ ⟨ρ, v⟩)
        = (λ v. [interp (n + 1) t]ₛ ⟨[E]ₛ ρ, v⟩))
    · gapply (gfunext _ _)
      gintro x
      gsimpl
      gapply (eq_trans' Dom) ([interp (m + 1) (ren (liftRen ξ) t)]ₛ ⟨ρ, x⟩)
        ([interp (n + 1) t]ₛ ([Env.lift n m E]ₛ ⟨ρ, x⟩))
        ([interp (n + 1) t]ₛ ⟨[E]ₛ ρ, x⟩)
      · gapply (ih) ⟨ρ, x⟩
      · gapply (app_cong_arg _ _)
        gapply (Env.lift_pair n m E) ρ x
    gapply (Dom.lam_delay_cong_fn)
      (λ v. [interp (m + 1) (ren (liftRen ξ) t)]ₛ ⟨ρ, v⟩)
      (λ v. [interp (n + 1) t]ₛ ⟨[E]ₛ ρ, v⟩)
    gexact Hfn
  | @«fix» n t iht =>
    intro m ξ E hE
    have ih := iht (liftRen ξ) (Env.lift n m E) (Env.lift_lookup n m ξ E hE)
    refine interp_fix_cong n m t (ren (liftRen ξ) t) E ?_
    gintro ρ x
    gapply (eq_trans' Dom) ([interp (m + 1) (ren (liftRen ξ) t)]ₛ ⟨ρ, x⟩)
      ([interp (n + 1) t]ₛ ([Env.lift n m E]ₛ ⟨ρ, x⟩))
      ([interp (n + 1) t]ₛ ⟨[E]ₛ ρ, x⟩)
    · gapply (ih) ⟨ρ, x⟩
    · gapply (app_cong_arg _ _)
      gapply (Env.lift_pair n m E) ρ x
theorem Env.liftS_lookup (n m : Nat) (σ : Fin n → Lam m) (E : SYNT ⦃[Env m] → [Env n]⦄)
    (hE : ∀ i : Fin n, AgreeAlong n m (interp m (σ i)) E (lookup n i)) :
    ∀ i : Fin (n + 1),
      AgreeAlong (n + 1) (m + 1) (interp (m + 1) (liftSub σ i)) (Env.lift n m E)
        (lookup (n + 1) i) := by
  intro i
  refine Fin.cases ?_ ?_ i
  · gintro ρ
    gsimpl
    gapply (Env.lift_snd n m E)
  · intro j
    gintro ρ
    gsimpl
    gapply (eq_trans' Dom) ([interp (m + 1) (ren Fin.succ (σ j))]ₛ ρ)
      ([interp m (σ j)]ₛ ([Env.wk m]ₛ ρ)) ([lookup n j]ₛ (π₁ ([Env.lift n m E]ₛ ρ)))
    · gapply (interp_ren (σ j) Fin.succ (Env.wk m) (Env.wk_lookup m)) ρ
    · gapply (eq_trans' Dom) ([interp m (σ j)]ₛ ([Env.wk m]ₛ ρ))
        ([lookup n j]ₛ ([E]ₛ ([Env.wk m]ₛ ρ))) ([lookup n j]ₛ (π₁ ([Env.lift n m E]ₛ ρ)))
      · gapply (hE j)
      · gapply (app_cong_arg _ _)
        gapply (eq_trans' (Env n)) ([E]ₛ ([Env.wk m]ₛ ρ)) ([E]ₛ (π₁ ρ))
          (π₁ ([Env.lift n m E]ₛ ρ))
        · gapply (app_cong_arg _ _)
          gapply (Env.wk_apply m)
        · gapply (Env.lift_fst' n m E)

theorem interp_sub : ∀ {n : Nat} (t : Lam n) {m : Nat} (σ : Fin n → Lam m)
    (E : SYNT ⦃[Env m] → [Env n]⦄)
    (_hE : ∀ i : Fin n, AgreeAlong n m (interp m (σ i)) E (lookup n i)),
    AgreeAlong n m (interp m (sub σ t)) E (interp n t) := by
  intro n t
  induction t with
  | @unit n =>
    intro m σ E hE
    gintro ρ
    gsimpl
    grfl
  | @var n i =>
    intro m σ E hE
    gintro ρ
    gapply (hE i)
  | @app n t u iht ihu =>
    intro m σ E hE
    gintro ρ
    gsimpl
    gapply (Dom.apply_cong)
    · gapply (iht σ E hE)
    · gapply (ihu σ E hE)
  | @lam n t iht =>
    intro m σ E hE
    have ih := iht (liftSub σ) (Env.lift n m E) (Env.liftS_lookup n m σ E hE)
    gintro ρ
    gsimpl
    gassert Hfn of ((λ v. [interp (m + 1) (sub (liftSub σ) t)]ₛ ⟨ρ, v⟩)
        = (λ v. [interp (n + 1) t]ₛ ⟨[E]ₛ ρ, v⟩))
    · gapply (gfunext _ _)
      gintro x
      gsimpl
      gapply (eq_trans' Dom) ([interp (m + 1) (sub (liftSub σ) t)]ₛ ⟨ρ, x⟩)
        ([interp (n + 1) t]ₛ ([Env.lift n m E]ₛ ⟨ρ, x⟩))
        ([interp (n + 1) t]ₛ ⟨[E]ₛ ρ, x⟩)
      · gapply (ih) ⟨ρ, x⟩
      · gapply (app_cong_arg _ _)
        gapply (Env.lift_pair n m E) ρ x
    gapply (Dom.lam_delay_cong_fn)
      (λ v. [interp (m + 1) (sub (liftSub σ) t)]ₛ ⟨ρ, v⟩)
      (λ v. [interp (n + 1) t]ₛ ⟨[E]ₛ ρ, v⟩)
    gexact Hfn
  | @«fix» n t iht =>
    intro m σ E hE
    have ih := iht (liftSub σ) (Env.lift n m E) (Env.liftS_lookup n m σ E hE)
    refine interp_fix_cong n m t (sub (liftSub σ) t) E ?_
    gintro ρ x
    gapply (eq_trans' Dom) ([interp (m + 1) (sub (liftSub σ) t)]ₛ ⟨ρ, x⟩)
      ([interp (n + 1) t]ₛ ([Env.lift n m E]ₛ ⟨ρ, x⟩))
      ([interp (n + 1) t]ₛ ⟨[E]ₛ ρ, x⟩)
    · gapply (ih) ⟨ρ, x⟩
    · gapply (app_cong_arg _ _)
      gapply (Env.lift_pair n m E) ρ x

abbrev EqUpToTick (n : Nat) (a b : SYNT ⦃[Env n] → Dom⦄) : Prop :=
  ⊢ᵍ ⟪∀ ρ : [Env n]. (([a]ₛ ρ) = [Dom.thunk]ₛ (delay ([b]ₛ ρ)))⟫

theorem interp_step : ∀ {n : Nat} {e e' : Lam n}, Step e e' →
    EqUpToTick n (interp n e) (interp n e') := by
  intro n e e' h
  induction h with
  | @beta t u =>
    gintro ρ
    gsimpl
    gapply (eq_trans' Dom) ([interp n (Lam.app (Lam.lam t) u)]ₛ ρ)
      ([Dom.thunk]ₛ (delay ([interp (n + 1) t]ₛ ⟨ρ, [interp n u]ₛ ρ⟩)))
      ([Dom.thunk]ₛ (delay ([interp n (subst0 t u)]ₛ ρ)))
    · gapply (Dom.apply_lam) (delay (λ v. [interp (n + 1) t]ₛ ⟨ρ, v⟩))
        ([interp n u]ₛ ρ)
    · gapply (Dom.thunk_delay_cong_tm) ([interp (n + 1) t]ₛ ⟨ρ, [interp n u]ₛ ρ⟩)
        ([interp n (subst0 t u)]ₛ ρ)
      gapply (eq_symm' Dom)
      gapply (eq_trans' Dom) ([interp n (subst0 t u)]ₛ ρ)
        ([interp (n + 1) t]ₛ ([Env.ext n (interp n u)]ₛ ρ))
        ([interp (n + 1) t]ₛ ⟨ρ, [interp n u]ₛ ρ⟩)
      · gapply (interp_sub t (substHead u) (Env.ext n (interp n u)) (Env.ext_lookup n u)) ρ
      · gapply (app_cong_arg _ _)
        gapply (eq_symm' (Env (n + 1)))
        gapply (Env.ext_apply' n (interp n u))
  | @appL t t' u hstep ih =>
    gintro ρ
    gsimpl
    gapply (eq_trans' Dom) (([Dom.apply]ₛ ([interp n t]ₛ ρ)) ([interp n u]ₛ ρ))
      (([Dom.apply]ₛ ([Dom.thunk]ₛ (delay ([interp n t']ₛ ρ)))) ([interp n u]ₛ ρ))
      ([Dom.thunk]ₛ (delay (([Dom.apply]ₛ ([interp n t']ₛ ρ)) ([interp n u]ₛ ρ))))
    · gapply (Dom.apply_cong)
      · gapply (ih) ρ
      · grfl
    · gapply (eq_trans' Dom)
        (([Dom.apply]ₛ ([Dom.thunk]ₛ (delay ([interp n t']ₛ ρ)))) ([interp n u]ₛ ρ))
        ([Dom.thunk]ₛ (delay (([Dom.apply]ₛ (adv 1 (delay ([interp n t']ₛ ρ))))
          ([interp n u]ₛ ρ))))
        ([Dom.thunk]ₛ (delay (([Dom.apply]ₛ ([interp n t']ₛ ρ)) ([interp n u]ₛ ρ))))
      · gapply (Dom.apply_thunk) (delay ([interp n t']ₛ ρ)) ([interp n u]ₛ ρ)
      · grfl
  | @unfold t =>
    gintro ρ
    gsimpl
    gapply (eq_trans' Dom) ([interp n (Lam.fix t)]ₛ ρ)
      ([Dom.thunk]ₛ (delay ([interp (n + 1) t]ₛ ⟨ρ, [interp n (Lam.fix t)]ₛ ρ⟩)))
      ([Dom.thunk]ₛ (delay ([interp n (subst0 t (Lam.fix t))]ₛ ρ)))
    · gapply (interp_fix_apply n t) ρ
    · gapply (Dom.thunk_delay_cong_tm)
        ([interp (n + 1) t]ₛ ⟨ρ, [interp n (Lam.fix t)]ₛ ρ⟩)
        ([interp n (subst0 t (Lam.fix t))]ₛ ρ)
      gapply (eq_symm' Dom)
      gapply (eq_trans' Dom) ([interp n (subst0 t (Lam.fix t))]ₛ ρ)
        ([interp (n + 1) t]ₛ ([Env.ext n (interp n (Lam.fix t))]ₛ ρ))
        ([interp (n + 1) t]ₛ ⟨ρ, [interp n (Lam.fix t)]ₛ ρ⟩)
      · gapply (interp_sub t (substHead (Lam.fix t))
          (Env.ext n (interp n (Lam.fix t))) (Env.ext_lookup n (Lam.fix t))) ρ
      · gapply (app_cong_arg _ _)
        gapply (eq_symm' (Env (n + 1)))
        gapply (Env.ext_apply' n (interp n (Lam.fix t))) ρ

section multistep

gdef ThunkedP (n : Nat) : ([Env n] → Dom) → [Env n] → Dom :=
  λ a. λ ρ. [Dom.thunk]ₛ (delay (a ρ))

gdef Thunked (n : Nat) (a : SYNT ⦃[Env n] → Dom⦄) : [Env n] → Dom :=
  [ThunkedP n]ₛ [a]ₛ

def thunkPow (n : Nat) : Nat → SYNT ⦃[Env n] → Dom⦄ → SYNT ⦃[Env n] → Dom⦄
  | 0, a => a
  | k + 1, a => thunkPow n k (Thunked n a)

end multistep

end Lam
end
