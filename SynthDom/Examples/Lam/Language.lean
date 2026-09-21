module

public import SynthDom
public import SynthDom.Examples.Lam.Model
@[expose] public section

inductive Lam : Nat → Type where
  | unit {n : Nat} : Lam n
  | var {n : Nat} : Fin n → Lam n
  | app {n : Nat} : Lam n → Lam n → Lam n
  | lam {n : Nat} : Lam (n + 1) → Lam n
  | fix {n : Nat} : Lam (n + 1) → Lam n

namespace Lam

def Env : Nat → TYPE.{0}
  | 0 => TYPE.embed Unit
  | n + 1 => TYPE.prod (Env n) Dom

def lookup : (n : Nat) → Fin n → SYNT ⦃[Env n] → Dom⦄
  | n + 1, ⟨0, _⟩ => box(λ ρ : [Env (n + 1)]. π₂ ρ)
  | n + 1, ⟨i + 1, h⟩ =>
    box(λ ρ : [Env (n + 1)]. [lookup n ⟨i, Nat.lt_of_succ_lt_succ h⟩]ₛ (π₁ ρ))

def interp : (n : Nat) → Lam n → SYNT ⦃[Env n] → Dom⦄
  | n, .unit => box(λ _ : [Env n]. [Dom.num 0]ₛ)
  | n, .var i => lookup n i
  | n, .app t u => box(λ ρ : [Env n]. ([Dom.apply]ₛ ([interp n t]ₛ ρ)) ([interp n u]ₛ ρ))
  | n, .lam t => box(λ ρ : [Env n]. [Dom.lam]ₛ (delay (λ v. [interp (n + 1) t]ₛ ⟨ρ, v⟩)))
  | n, .fix t =>
    box(λ ρ : [Env n].
      fix y. [Dom.thunk]ₛ (delay ([interp (n + 1) t]ₛ ⟨ρ, adv 1 y⟩)))

section syntax_operations

def liftRen {n m : Nat} (ξ : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1)
  | ⟨0, _⟩ => 0
  | ⟨i + 1, h⟩ => (ξ ⟨i, Nat.lt_of_succ_lt_succ h⟩).succ

def ren : {n m : Nat} → (Fin n → Fin m) → Lam n → Lam m
  | _, _, _, .unit => .unit
  | _, _, ξ, .var i => .var (ξ i)
  | _, _, ξ, .app t u => .app (ren ξ t) (ren ξ u)
  | _, _, ξ, .lam t => .lam (ren (liftRen ξ) t)
  | _, _, ξ, .fix t => .fix (ren (liftRen ξ) t)

def liftSub {n m : Nat} (σ : Fin n → Lam m) : Fin (n + 1) → Lam (m + 1)
  | ⟨0, _⟩ => .var 0
  | ⟨i + 1, h⟩ => ren Fin.succ (σ ⟨i, Nat.lt_of_succ_lt_succ h⟩)

def sub : {n m : Nat} → (Fin n → Lam m) → Lam n → Lam m
  | _, _, _, .unit => .unit
  | _, _, σ, .var i => σ i
  | _, _, σ, .app t u => .app (sub σ t) (sub σ u)
  | _, _, σ, .lam t => .lam (sub (liftSub σ) t)
  | _, _, σ, .fix t => .fix (sub (liftSub σ) t)

def substHead {n : Nat} (u : Lam n) : Fin (n + 1) → Lam n
  | ⟨0, _⟩ => u
  | ⟨i + 1, h⟩ => .var ⟨i, Nat.lt_of_succ_lt_succ h⟩

def subst0 {n : Nat} (t : Lam (n + 1)) (u : Lam n) : Lam n :=
  sub (substHead u) t

inductive Step : {n : Nat} → Lam n → Lam n → Prop where
  | beta {n : Nat} (t : Lam (n + 1)) (u : Lam n) : Step (.app (.lam t) u) (subst0 t u)
  | appL {n : Nat} {t t' : Lam n} (u : Lam n) : Step t t' → Step (.app t u) (.app t' u)
  | unfold {n : Nat} (t : Lam (n + 1)) : Step (.fix t) (subst0 t (.fix t))

inductive StepsN : {n : Nat} → Nat → Lam n → Lam n → Prop where
  | refl {n : Nat} (e : Lam n) : StepsN 0 e e
  | tail {n : Nat} {k : Nat} {e e' e'' : Lam n} :
      StepsN k e e' → Step e' e'' → StepsN (k + 1) e e''

def Steps {n : Nat} (e e' : Lam n) : Prop := ∃ k, StepsN k e e'

theorem StepsN.append {n : Nat} {j k : Nat} {e e' e'' : Lam n} :
    StepsN k e e' → StepsN j e' e'' → StepsN (k + j) e e''
  | h, .refl _ => h
  | h, .tail hs hstep => .tail (h.append hs) hstep

theorem Steps.refl {n : Nat} (e : Lam n) : Steps e e := ⟨0, .refl e⟩

theorem Steps.single {n : Nat} {e e' : Lam n} (h : Step e e') : Steps e e' :=
  ⟨1, .tail (.refl e) h⟩

theorem Steps.trans {n : Nat} {e e' e'' : Lam n} : Steps e e' → Steps e' e'' → Steps e e''
  | ⟨_, h⟩, ⟨_, h'⟩ => ⟨_, h.append h'⟩

theorem Steps.appL {n : Nat} {t t' : Lam n} (u : Lam n) : Steps t t' →
    Steps (.app t u) (.app t' u) := by
  intro ⟨k, h⟩
  induction h with
  | refl _ => exact Steps.refl _
  | tail hs hstep ih => exact ih.trans (Steps.single (.appL u hstep))

theorem Steps.beta {n : Nat} (t : Lam (n + 1)) (u : Lam n) :
    Steps (.app (.lam t) u) (subst0 t u) := Steps.single (.beta t u)

theorem Steps.unfold {n : Nat} (t : Lam (n + 1)) :
    Steps (.fix t) (subst0 t (.fix t)) := Steps.single (.unfold t)

section typing

inductive Ty : Type where
  | unit : Ty
  | arr : Ty → Ty → Ty

abbrev Ctx (n : Nat) : Type := Fin n → Ty

def Ctx.cons {n : Nat} (a : Ty) (Γ : Ctx n) : Ctx (n + 1) := Fin.cases a Γ

inductive Typing : {n : Nat} → Ctx n → Lam n → Ty → Prop where
  | unit {n : Nat} {Γ : Ctx n} : Typing Γ .unit .unit
  | var {n : Nat} {Γ : Ctx n} (i : Fin n) : Typing Γ (.var i) (Γ i)
  | app {n : Nat} {Γ : Ctx n} {t u : Lam n} {a b : Ty} :
      Typing Γ t (.arr a b) → Typing Γ u a → Typing Γ (.app t u) b
  | lam {n : Nat} {Γ : Ctx n} {t : Lam (n + 1)} {a b : Ty} :
      Typing (Ctx.cons a Γ) t b → Typing Γ (.lam t) (.arr a b)
  | fix {n : Nat} {Γ : Ctx n} {t : Lam (n + 1)} {a : Ty} :
      Typing (Ctx.cons a Γ) t a → Typing Γ (.fix t) a

@[simp] theorem Ctx.cons_zero {n : Nat} (a : Ty) (Γ : Ctx n) :
    Ctx.cons a Γ ⟨0, Nat.succ_pos n⟩ = a := rfl

@[simp] theorem Ctx.cons_succ {n : Nat} (a : Ty) (Γ : Ctx n) (i : Fin n) :
    Ctx.cons a Γ i.succ = Γ i := rfl

end typing

gdef Env.liftP (n m : Nat) : ([Env m] → [Env n]) → [Env (m + 1)] → [Env (n + 1)] :=
  λ e. λ p. ⟨e (π₁ p), π₂ p⟩

gdef Env.lift (n m : Nat) (E : SYNT ⦃[Env m] → [Env n]⦄) : [Env (m + 1)] → [Env (n + 1)] :=
  [Env.liftP n m]ₛ [E]ₛ

end syntax_operations

section substitution_lemmas

@[simp] theorem liftRen_zero {n m : Nat} (ξ : Fin n → Fin m) : liftRen ξ 0 = 0 := rfl

@[simp] theorem liftRen_succ {n m : Nat} (ξ : Fin n → Fin m) (i : Fin n) :
    liftRen ξ i.succ = (ξ i).succ := rfl

@[simp] theorem liftSub_zero {n m : Nat} (σ : Fin n → Lam m) : liftSub σ 0 = .var 0 := rfl

@[simp] theorem liftSub_succ {n m : Nat} (σ : Fin n → Lam m) (i : Fin n) :
    liftSub σ i.succ = ren Fin.succ (σ i) := rfl

@[simp] theorem substHead_zero {n : Nat} (u : Lam n) : substHead u 0 = u := rfl

@[simp] theorem substHead_succ {n : Nat} (u : Lam n) (i : Fin n) :
    substHead u i.succ = .var i := rfl

theorem liftRen_comp {n m k : Nat} (ξ : Fin n → Fin m) (ζ : Fin m → Fin k) :
    liftRen ζ ∘ liftRen ξ = liftRen (ζ ∘ ξ) := by
  funext i
  refine Fin.cases ?_ ?_ i <;> intros <;> rfl

theorem ren_ren {n : Nat} (t : Lam n) : ∀ {m k : Nat} (ξ : Fin n → Fin m) (ζ : Fin m → Fin k),
    ren ζ (ren ξ t) = ren (ζ ∘ ξ) t := by
  induction t with
  | unit | var _ => intros; rfl
  | app t u iht ihu => intros; simp only [ren, iht, ihu]
  | lam t ih | «fix» t ih => intros m k ξ ζ; simp only [ren, ih, liftRen_comp]

theorem liftRen_succ_comp {n m : Nat} (ξ : Fin n → Fin m) :
    liftRen ξ ∘ Fin.succ = Fin.succ ∘ ξ := by
  funext i
  simp

theorem liftSub_liftRen {n m k : Nat} (ξ : Fin n → Fin m) (τ : Fin m → Lam k) :
    liftSub τ ∘ liftRen ξ = liftSub (τ ∘ ξ) := by
  funext i
  refine Fin.cases ?_ ?_ i <;> intros <;> rfl

theorem sub_ren {n : Nat} (t : Lam n) : ∀ {m k : Nat} (ξ : Fin n → Fin m) (τ : Fin m → Lam k),
    sub τ (ren ξ t) = sub (τ ∘ ξ) t := by
  induction t with
  | unit | var _ => intros; rfl
  | app t u iht ihu => intros; simp only [ren, sub, iht, ihu]
  | lam t ih | «fix» t ih => intros m k ξ τ; simp only [ren, sub, ih, liftSub_liftRen]

theorem liftSub_ren {n m k : Nat} (σ : Fin n → Lam m) (ξ : Fin m → Fin k) :
    liftSub (fun i => ren ξ (σ i)) = fun i => ren (liftRen ξ) (liftSub σ i) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    simp only [liftSub_succ, ren_ren, liftRen_succ_comp]

theorem ren_sub {n : Nat} (t : Lam n) : ∀ {m k : Nat} (σ : Fin n → Lam m) (ξ : Fin m → Fin k),
    ren ξ (sub σ t) = sub (fun i => ren ξ (σ i)) t := by
  induction t with
  | unit | var _ => intros; rfl
  | app t u iht ihu => intros; simp only [ren, sub, iht, ihu]
  | lam t ih | «fix» t ih => intros m k σ ξ; simp only [ren, sub, ih, liftSub_ren]

theorem liftSub_comp {n m k : Nat} (σ : Fin n → Lam m) (τ : Fin m → Lam k) :
    liftSub (fun i => sub τ (σ i)) = fun i => sub (liftSub τ) (liftSub σ i) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    simp only [liftSub_succ, ren_sub, sub_ren]
    congr 1

theorem sub_sub {n : Nat} (t : Lam n) : ∀ {m k : Nat} (σ : Fin n → Lam m) (τ : Fin m → Lam k),
    sub τ (sub σ t) = sub (fun i => sub τ (σ i)) t := by
  induction t with
  | unit | var _ => intros; rfl
  | app t u iht ihu => intros; simp only [sub, iht, ihu]
  | lam t ih | «fix» t ih => intros m k σ τ; simp only [sub, ih, liftSub_comp]

theorem liftSub_var {n : Nat} : liftSub (fun i : Fin n => Lam.var i) = fun i => Lam.var i := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    simp [ren]

theorem sub_var {n : Nat} (t : Lam n) : sub (fun i => Lam.var i) t = t := by
  induction t with
  | unit | var _ => rfl
  | app t u iht ihu => simp only [sub, iht, ihu]
  | lam t ih | «fix» t ih => simp only [sub, liftSub_var, ih]

theorem subst0_sub {n : Nat} (σ : Fin n → Lam 0) (t : Lam (n + 1)) (y : Lam 0) :
    subst0 (sub (liftSub σ) t) y = sub (Fin.cases y σ) t := by
  rw [subst0, sub_sub]
  congr 1
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    simp only [liftSub_succ, sub_ren, Fin.cases_succ]
    rw [show substHead y ∘ Fin.succ = fun i => Lam.var i by funext z; simp]
    exact sub_var (σ j)

end substitution_lemmas

section defining_equations

theorem interp_var (n : Nat) (i : Fin n) : interp n (.var i) = lookup n i := rfl

theorem interp_app (n : Nat) (t u : Lam n) :
    interp n (.app t u)
      = box(λ ρ : [Env n]. ([Dom.apply]ₛ ([interp n t]ₛ ρ)) ([interp n u]ₛ ρ)) := rfl

theorem interp_lam (n : Nat) (t : Lam (n + 1)) :
    interp n (.lam t)
      = box(λ ρ : [Env n]. [Dom.lam]ₛ (delay (λ v. [interp (n + 1) t]ₛ ⟨ρ, v⟩))) := rfl

theorem interp_fix (n : Nat) (t : Lam (n + 1)) :
    interp n (.fix t)
      = box(λ ρ : [Env n].
          fix y. [Dom.thunk]ₛ (delay ([interp (n + 1) t]ₛ ⟨ρ, adv 1 y⟩))) := rfl

end defining_equations

section pointwise_equations

gtheorem interp_fix_apply (n : Nat) (t : Lam (n + 1)) :
    ∀ ρ : [Env n]. (([interp n (Lam.fix t)]ₛ ρ)
      = [Dom.thunk]ₛ (delay ([interp (n + 1) t]ₛ ⟨ρ, [interp n (Lam.fix t)]ₛ ρ⟩))) := by
  gintro ρ
  gsimpl
  gfix
  grfl

end pointwise_equations

section beta

end beta

end Lam

end
