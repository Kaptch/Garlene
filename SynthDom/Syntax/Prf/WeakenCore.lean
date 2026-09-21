module

public import SynthDom.Syntax.Prf.Core

@[expose] public section

section prf
open Lean

theorem off_lw_succ (x : REN) (k : Nat) :
    offset_ren x.local_weaken (k+1) = offset_ren x (k+1) := rfl
theorem off_cons_succ (x : REN) (k : Nat) :
    offset_ren x.cons (k+1) = offset_ren x (k+1) := rfl
theorem off_global_lift_succ (x : REN) (k : Nat) :
    offset_ren x.global_lift (k+1) = offset_ren x k + 1 := rfl
theorem off_global_shift_succ (p : Nat) (x : REN) (k : Nat) :
    offset_ren (REN.global_shift p x) (k+1) = p + offset_ren x (k+1) := rfl
theorem cut_lw_succ (x : REN) (k : Nat) :
    cut_ren x.local_weaken (k+1) = cut_ren x (k+1) := rfl
theorem cut_cons_succ (x : REN) (k : Nat) :
    cut_ren x.cons (k+1) = cut_ren x (k+1) := rfl
theorem cut_global_lift_succ (x : REN) (k : Nat) :
    cut_ren x.global_lift (k+1) = cut_ren x k := rfl
theorem cut_global_shift_succ (p : Nat) (x : REN) (k : Nat) :
    cut_ren (REN.global_shift p x) (k+1) = cut_ren x (k+1) := rfl
theorem off_comp_succ (x y : REN) (n : Nat) :
    offset_ren (REN.comp x y) (n+1) = offset_ren y (offset_ren x (n+1)) := rfl
theorem cut_comp_succ (x y : REN) (n : Nat) :
    cut_ren (REN.comp x y) (n+1)
      = REN.comp (cut_ren x (n+1)) (cut_ren y (offset_ren x (n+1))) := rfl

theorem offset_comp_all (x y : REN) (n : Nat) :
    offset_ren (REN.comp x y) n = offset_ren y (offset_ren x n) := by
  cases n <;> simp

theorem cut_comp_all (x y : REN) (k : Nat) :
    cut_ren (REN.comp x y) k = REN.comp (cut_ren x k) (cut_ren y (offset_ren x k)) := by
  cases k <;> simp

theorem offset_succ_pos (ρ : REN) (n : Nat) : 0 < offset_ren ρ (n+1) := by
  exact (Nat.zero_lt_succ n).trans_le (offset_ren_ge ρ (n + 1))

theorem offset_cut (ρ : REN) (a b : Nat) :
    offset_ren ρ a + offset_ren (cut_ren ρ a) b = offset_ren ρ (a + b) := by
  induction ρ generalizing a b with
  | id => cases a <;> cases b <;> simp
  | comp x y IHx IHy =>
    cases a with
    | zero => simp
    | succ a' =>
      cases b with
      | zero => simp
      | succ b' =>
        rw [cut_comp_succ]
        show offset_ren y (offset_ren x (a'+1))
              + offset_ren (cut_ren y (offset_ren x (a'+1))) (offset_ren (cut_ren x (a'+1)) (b'+1))
            = offset_ren y (offset_ren x (a'+1+(b'+1)))
        set P := offset_ren x (a'+1) with hP
        set Q := offset_ren (cut_ren x (a'+1)) (b'+1) with hQ
        have hx := IHx (a'+1) (b'+1)
        rw [← hP, ← hQ] at hx
        rw [← hx]; exact IHy P Q
  | local_weaken x IH =>
    cases a with
    | zero => simp
    | succ a' =>
      have e : a' + 1 + b = (a'+b)+1 := by omega
      rw [off_lw_succ, cut_lw_succ, e, off_lw_succ, ← e]; exact IH (a'+1) b
  | cons x IH =>
    cases a with
    | zero => simp
    | succ a' =>
      have e : a' + 1 + b = (a'+b)+1 := by omega
      rw [off_cons_succ, cut_cons_succ, e, off_cons_succ, ← e]; exact IH (a'+1) b
  | global_lift x IH =>
    cases a with
    | zero => simp
    | succ a' =>
      rw [off_global_lift_succ, cut_global_lift_succ]
      have e : a' + 1 + b = (a'+b)+1 := by omega
      rw [e, off_global_lift_succ]
      have := IH a' b; omega
  | global_shift p x IH =>
    cases a with
    | zero => simp
    | succ a' =>
      have e : a' + 1 + b = (a'+b)+1 := by omega
      rw [off_global_shift_succ, cut_global_shift_succ, e, off_global_shift_succ, ← e]
      have := IH (a'+1) b; omega

theorem cut_cut (ρ : REN) (a b : Nat) : cut_ren (cut_ren ρ a) b = cut_ren ρ (a + b) := by
  induction ρ generalizing a b with
  | id => cases a <;> cases b <;> simp
  | comp x y IHx IHy =>
    cases a with
    | zero => simp
    | succ a' =>
      cases b with
      | zero => simp
      | succ b' =>
        rw [cut_comp_succ, cut_comp_succ]
        show REN.comp (cut_ren (cut_ren x (a'+1)) (b'+1))
                      (cut_ren (cut_ren y (offset_ren x (a'+1))) (offset_ren (cut_ren x (a'+1)) (b'+1)))
           = REN.comp (cut_ren x (a'+1+(b'+1))) (cut_ren y (offset_ren x (a'+1+(b'+1))))
        congr 1
        · exact IHx (a'+1) (b'+1)
        · rw [IHy]; congr 1; exact offset_cut x (a'+1) (b'+1)
  | local_weaken x IH =>
    cases a with
    | zero => simp
    | succ a' =>
      have e : a' + 1 + b = (a'+b)+1 := by omega
      rw [cut_lw_succ, e, cut_lw_succ, ← e]; exact IH (a'+1) b
  | cons x IH =>
    cases a with
    | zero => simp
    | succ a' =>
      have e : a' + 1 + b = (a'+b)+1 := by omega
      rw [cut_cons_succ, e, cut_cons_succ, ← e]; exact IH (a'+1) b
  | global_lift x IH =>
    cases a with
    | zero => simp
    | succ a' =>
      have e : a' + 1 + b = (a'+b)+1 := by omega
      rw [cut_global_lift_succ, e, cut_global_lift_succ]; exact IH a' b
  | global_shift p x IH =>
    cases a with
    | zero => simp
    | succ a' =>
      have e : a' + 1 + b = (a'+b)+1 := by omega
      rw [cut_global_shift_succ, e, cut_global_shift_succ, ← e]; exact IH (a'+1) b

theorem wvar_cut (σ : REN) (n a b : Nat) :
    weaken_var' σ (n + a) b
      = (offset_ren σ n + (weaken_var' (cut_ren σ n) a b).1,
          (weaken_var' (cut_ren σ n) a b).2) := by
  induction σ generalizing n a b with
  | id => cases n <;> simp [weaken_var', cut_ren, offset_ren]
  | comp x y IHx IHy =>
    simp only [weaken_var']
    rw [IHx n a b, cut_comp_all, offset_comp_all]
    simp only [weaken_var']
    rw [IHy (offset_ren x n) ((weaken_var' (cut_ren x n) a b).1)
      ((weaken_var' (cut_ren x n) a b).2)]
  | local_weaken x IH =>
    cases n with
    | zero => simp [cut_ren, offset_ren]
    | succ n' =>
      simp only [weaken_var', cut_lw_succ, off_lw_succ]
      rw [show n' + 1 + a = (n' + 1) + a from by omega, IH (n' + 1) a b]
      obtain ⟨j, hj⟩ :
          ∃ j, offset_ren x (n' + 1) + (weaken_var' (cut_ren x (n' + 1)) a b).1 = j + 1 :=
        ⟨_, (Nat.succ_pred_eq_of_pos (by have := offset_succ_pos x n'; omega)).symm⟩
      rw [hj]
  | cons x IH =>
    cases n with
    | zero => simp [cut_ren, offset_ren]
    | succ n' =>
      simp only [cut_cons_succ, off_cons_succ]
      rw [show n' + 1 + a = (n' + a) + 1 from by omega]
      simp only [weaken_var']
      rw [show (n' + a) + 1 = (n' + 1) + a from by omega, IH (n' + 1) a b]
      obtain ⟨j, hj⟩ :
          ∃ j, offset_ren x (n' + 1) + (weaken_var' (cut_ren x (n' + 1)) a b).1 = j + 1 :=
        ⟨_, (Nat.succ_pred_eq_of_pos (by have := offset_succ_pos x n'; omega)).symm⟩
      rw [hj]
  | global_lift x IH =>
    cases n with
    | zero => simp [cut_ren, offset_ren]
    | succ n' =>
      simp only [cut_global_lift_succ, off_global_lift_succ]
      rw [show n' + 1 + a = (n' + a) + 1 from by omega]
      simp only [weaken_var']
      rw [IH n' a b]
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  | global_shift p x IH =>
    cases n with
    | zero => simp [cut_ren, offset_ren]
    | succ n' =>
      simp only [cut_global_shift_succ, off_global_shift_succ, weaken_var']
      rw [show n' + 1 + a = (n' + 1) + a from by omega, IH (n' + 1) a b]
      simp only [Nat.add_assoc]

def REN.equiv (ρ1 ρ2 : REN) : Prop :=
  (∀ n m, weaken_var' ρ1 n m = weaken_var' ρ2 n m) ∧
  (∀ n, offset_ren ρ1 n = offset_ren ρ2 n)

theorem REN.equiv.wvar {ρ1 ρ2 : REN} (h : REN.equiv ρ1 ρ2) (n m : Nat) :
    weaken_var' ρ1 n m = weaken_var' ρ2 n m :=
  h.1 n m

theorem REN.equiv.offset {ρ1 ρ2 : REN} (h : REN.equiv ρ1 ρ2) (n : Nat) :
    offset_ren ρ1 n = offset_ren ρ2 n :=
  h.2 n

theorem REN.equiv.cut {ρ1 ρ2 : REN} (h : REN.equiv ρ1 ρ2) (j : Nat) :
    REN.equiv (cut_ren ρ1 j) (cut_ren ρ2 j) := by
  refine ⟨fun n m => ?_, fun n => ?_⟩
  · have hw := h.wvar (j + n) m
    rw [wvar_cut ρ1 j n m, wvar_cut ρ2 j n m, h.offset j] at hw
    rcases hρ1 : weaken_var' (cut_ren ρ1 j) n m with ⟨n1, m1⟩
    rcases hρ2 : weaken_var' (cut_ren ρ2 j) n m with ⟨n2, m2⟩
    simp only [hρ1, hρ2, Prod.mk.injEq] at hw ⊢
    exact ⟨Nat.add_left_cancel hw.1, hw.2⟩
  · have h1 := offset_cut ρ1 j n
    have h2 := offset_cut ρ2 j n
    rw [h.offset j, h.offset (j + n)] at h1
    omega

theorem REN.equiv.cons {ρ1 ρ2 : REN} (h : REN.equiv ρ1 ρ2) : REN.equiv ρ1.cons ρ2.cons := by
  refine ⟨fun n m => ?_, fun n => ?_⟩
  · cases n with
    | zero => cases m with
      | zero => rfl
      | succ m' => simp only [weaken_var']; rw [h.wvar 0 m']
    | succ n' => simp only [weaken_var']; rw [h.wvar (n' + 1) m]
  · cases n with
    | zero => rfl
    | succ n' => simp only [off_cons_succ]; rw [h.offset (n' + 1)]

theorem REN.equiv.global_lift {ρ1 ρ2 : REN} (h : REN.equiv ρ1 ρ2) :
    REN.equiv ρ1.global_lift ρ2.global_lift := by
  refine ⟨fun n m => ?_, fun n => ?_⟩
  · cases n with
    | zero => rfl
    | succ n' => simp only [weaken_var']; rw [h.wvar n' m]
  · cases n with
    | zero => rfl
    | succ n' => simp only [off_global_lift_succ]; rw [h.offset n']

theorem weaken_congr (e : EXPR.{i}) {ρ1 ρ2 : REN} (h : REN.equiv ρ1 ρ2) :
    weaken e ρ1 = weaken e ρ2 := by
  induction e generalizing ρ1 ρ2 with
  | embed A a => rfl
  | embed_apply A B f x IHf IHx => simp only [weaken]; rw [IHf h, IHx h]
  | pure e IH => simp only [weaken]; rw [IH h]
  | var' n m => simp only [weaken]; rw [h.wvar]
  | app B e1 e2 IH1 IH2 => simp only [weaken]; rw [IH1 h, IH2 h]
  | lam' t e IH => simp only [weaken]; rw [IH h.cons]
  | delay e IH => simp only [weaken]; rw [IH h.global_lift]
  | adv n e IH => simp only [weaken]; rw [h.offset, IH (h.cut n)]
  | fix' t e IH => simp only [weaken]; rw [IH h.cons]
  | pair e1 e2 IH1 IH2 => simp only [weaken]; rw [IH1 h, IH2 h]
  | proj B e d IH => simp only [weaken]; rw [IH h]
  | inl B e IH => simp only [weaken]; rw [IH h]
  | inr A e IH => simp only [weaken]; rw [IH h]
  | case A B e f g IHe IHf IHg => simp only [weaken]; rw [IHe h, IHf h, IHg h]
  | or e1 e2 IH1 IH2 => simp only [weaken]; rw [IH1 h, IH2 h]
  | and e1 e2 IH1 IH2 => simp only [weaken]; rw [IH1 h, IH2 h]
  | impl e1 e2 IH1 IH2 => simp only [weaken]; rw [IH1 h, IH2 h]
  | forall' t e IH => simp only [weaken]; rw [IH h.cons]
  | exists' t e IH => simp only [weaken]; rw [IH h.cons]
  | lift e IH => simp only [weaken]; rw [IH h]
  | true => rfl
  | false => rfl
  | eq B e1 e2 IH1 IH2 => simp only [weaken]; rw [IH1 h, IH2 h]
  | ax t f => rfl

theorem equiv_cons_comp (σ1 σ2 : REN) :
    REN.equiv (REN.comp σ1.cons σ2.cons) (REN.comp σ1 σ2).cons := by
  refine ⟨fun n m => ?_, fun n => ?_⟩
  · cases n with
    | zero => cases m with
      | zero => rfl
      | succ m' =>
        simp only [weaken_var']
        rcases h1 : weaken_var' σ1 0 m' with ⟨a, b⟩
        cases a <;> simp
    | succ n' =>
      simp only [weaken_var']
      rcases h1 : weaken_var' σ1 (n' + 1) m with ⟨a, b⟩
      cases a <;> simp
  · cases n with
    | zero => rfl
    | succ n' =>
      show offset_ren σ2.cons (offset_ren σ1.cons (n' + 1)) =
        offset_ren σ2 (offset_ren σ1 (n' + 1))
      rw [off_cons_succ]
      obtain ⟨j, hj⟩ : ∃ j, offset_ren σ1 (n' + 1) = j + 1 :=
        ⟨_, (Nat.succ_pred_eq_of_pos (offset_succ_pos σ1 n')).symm⟩
      rw [hj, off_cons_succ]

theorem equiv_global_lift_comp (σ1 σ2 : REN) :
    REN.equiv (REN.comp σ1.global_lift σ2.global_lift) (REN.comp σ1 σ2).global_lift := by
  refine ⟨fun n m => ?_, fun n => ?_⟩
  · cases n with
    | zero => rfl
    | succ n' => simp only [weaken_var']
  · cases n with
    | zero => rfl
    | succ n' => simp only [off_comp_succ, off_global_lift_succ]; rw [offset_comp_all]

theorem weaken_comp (e : EXPR.{i}) (σ1 σ2 : REN) :
    weaken (weaken e σ1) σ2 = weaken e (REN.comp σ1 σ2) := by
  induction e generalizing σ1 σ2 with
  | embed A a => rfl
  | embed_apply A B f x IHf IHx => simp only [weaken]; rw [IHf, IHx]
  | pure e IH => simp only [weaken]; rw [IH]
  | var' n m => simp only [weaken, weaken_var']
  | app B e1 e2 IH1 IH2 => simp only [weaken]; rw [IH1, IH2]
  | lam' t e IH =>
    simp only [weaken]; rw [IH]; congr 1
    exact weaken_congr e (equiv_cons_comp σ1 σ2)
  | delay e IH =>
    simp only [weaken]; rw [IH]; congr 1
    exact weaken_congr e (equiv_global_lift_comp σ1 σ2)
  | adv n e IH =>
    simp only [weaken]; rw [IH]
    cases n with
    | zero => simp
    | succ n' => rfl
  | fix' t e IH =>
    simp only [weaken]; rw [IH]; congr 1
    exact weaken_congr e (equiv_cons_comp σ1 σ2)
  | pair e1 e2 IH1 IH2 => simp only [weaken]; rw [IH1, IH2]
  | proj B e d IH => simp only [weaken]; rw [IH]
  | inl B e IH => simp only [weaken]; rw [IH]
  | inr A e IH => simp only [weaken]; rw [IH]
  | case A B e f g IHe IHf IHg => simp only [weaken]; rw [IHe, IHf, IHg]
  | or e1 e2 IH1 IH2 => simp only [weaken]; rw [IH1, IH2]
  | and e1 e2 IH1 IH2 => simp only [weaken]; rw [IH1, IH2]
  | impl e1 e2 IH1 IH2 => simp only [weaken]; rw [IH1, IH2]
  | forall' t e IH =>
    simp only [weaken]; rw [IH]; congr 1
    exact weaken_congr e (equiv_cons_comp σ1 σ2)
  | exists' t e IH =>
    simp only [weaken]; rw [IH]; congr 1
    exact weaken_congr e (equiv_cons_comp σ1 σ2)
  | lift e IH => simp only [weaken]; rw [IH]
  | true => rfl
  | false => rfl
  | eq B e1 e2 IH1 IH2 => simp only [weaken]; rw [IH1, IH2]
  | ax t f => rfl

theorem REN.equiv.refl (ρ : REN) : REN.equiv ρ ρ :=
  ⟨fun _ _ => rfl, fun _ => rfl⟩

theorem REN.equiv.symm {ρ1 ρ2 : REN} (h : REN.equiv ρ1 ρ2) : REN.equiv ρ2 ρ1 :=
  ⟨fun n m => (h.wvar n m).symm, fun n => (h.offset n).symm⟩

theorem REN.equiv.trans {ρ1 ρ2 ρ3 : REN} (h1 : REN.equiv ρ1 ρ2) (h2 : REN.equiv ρ2 ρ3) :
    REN.equiv ρ1 ρ3 :=
  ⟨fun n m => (h1.wvar n m).trans (h2.wvar n m),
   fun n => (h1.offset n).trans (h2.offset n)⟩

theorem cut_id (n : Nat) : cut_ren REN.id n = REN.id := by cases n <;> simp [cut_ren]
theorem off_id (n : Nat) : offset_ren REN.id n = n := by cases n <;> simp [offset_ren]

theorem equiv_id_cons : REN.equiv REN.id.cons REN.id := by
  refine ⟨fun n m => ?_, fun n => ?_⟩
  · cases n with
    | zero => cases m with | zero => rfl | succ m' => simp [weaken_var']
    | succ n' => simp [weaken_var']
  · cases n with | zero => rfl | succ n' => simp only [off_cons_succ, off_id]

theorem equiv_id_global_lift : REN.equiv REN.id.global_lift REN.id := by
  refine ⟨fun n m => ?_, fun n => ?_⟩
  · cases n with | zero => rfl | succ n' => simp [weaken_var']
  · cases n with | zero => rfl | succ n' => simp only [off_global_lift_succ, off_id]

theorem weaken_eq_self {σ : REN} (h : REN.equiv σ REN.id) (e : EXPR.{i}) : weaken e σ = e := by
  induction e generalizing σ with
  | embed A a => rfl
  | embed_apply A B f x IHf IHx => simp only [weaken]; rw [IHf h, IHx h]
  | pure e IH => simp only [weaken]; rw [IH h]
  | var' n m => simp only [weaken]; rw [h.wvar]; simp [weaken_var']
  | app B e1 e2 IH1 IH2 => simp only [weaken]; rw [IH1 h, IH2 h]
  | lam' t e IH => simp only [weaken]; rw [IH (h.cons.trans equiv_id_cons)]
  | delay e IH => simp only [weaken]; rw [IH (h.global_lift.trans equiv_id_global_lift)]
  | adv n e IH =>
    simp only [weaken]; rw [h.offset n, off_id]
    have hcut : REN.equiv (cut_ren REN.id n) REN.id := by rw [cut_id]; exact REN.equiv.refl _
    rw [IH ((h.cut n).trans hcut)]
  | fix' t e IH => simp only [weaken]; rw [IH (h.cons.trans equiv_id_cons)]
  | pair e1 e2 IH1 IH2 => simp only [weaken]; rw [IH1 h, IH2 h]
  | proj B e d IH => simp only [weaken]; rw [IH h]
  | inl B e IH => simp only [weaken]; rw [IH h]
  | inr A e IH => simp only [weaken]; rw [IH h]
  | case A B e f g IHe IHf IHg => simp only [weaken]; rw [IHe h, IHf h, IHg h]
  | or e1 e2 IH1 IH2 => simp only [weaken]; rw [IH1 h, IH2 h]
  | and e1 e2 IH1 IH2 => simp only [weaken]; rw [IH1 h, IH2 h]
  | impl e1 e2 IH1 IH2 => simp only [weaken]; rw [IH1 h, IH2 h]
  | forall' t e IH => simp only [weaken]; rw [IH (h.cons.trans equiv_id_cons)]
  | exists' t e IH => simp only [weaken]; rw [IH (h.cons.trans equiv_id_cons)]
  | lift e IH => simp only [weaken]; rw [IH h]
  | true => rfl
  | false => rfl
  | eq B e1 e2 IH1 IH2 => simp only [weaken]; rw [IH1 h, IH2 h]
  | ax t f => rfl

theorem weaken_id (e : EXPR.{i}) : weaken e REN.id = e := weaken_eq_self (REN.equiv.refl _) e

theorem equiv_global_shift_zero_id : REN.equiv (REN.global_shift 0 REN.id) REN.id := by
  refine ⟨fun a b => ?_, fun a => ?_⟩
  · simp only [weaken_var', Nat.zero_add]
  · cases a with
    | zero => rfl
    | succ a' => simp only [off_global_shift_succ, off_id, Nat.zero_add]

@[simp] theorem weaken_quote_cons_global_shift_zero {τ : TYPE.{i}} (e : SYNT τ) (k : Nat) (m : Option Nat) :
    weaken (EXPR.quote e k m) (REN.cons (REN.global_shift 0 REN.id)) = EXPR.quote e k m :=
  weaken_eq_self ((equiv_global_shift_zero_id.cons).trans equiv_id_cons) _

def REN.AgreeOn (ρ1 ρ2 : REN) (Γ : CTX.{i}) : Prop :=
  (∀ p q (Ψ : OCTX.{i}) (τ : TYPE.{i}), Γ[p]? = some Ψ → Ψ[q]? = some τ →
      weaken_var' ρ1 p q = weaken_var' ρ2 p q)
  ∧ (∀ n, n < Γ.length → offset_ren ρ1 n = offset_ren ρ2 n)

theorem REN.AgreeOn.cons {ρ1 ρ2 : REN} {Δ : OCTX.{i}} {Γs : CTX.{i}} (τ : TYPE.{i})
    (h : REN.AgreeOn ρ1 ρ2 (Δ :: Γs)) : REN.AgreeOn ρ1.cons ρ2.cons ((τ :: Δ) :: Γs) := by
  obtain ⟨hw, ho⟩ := h
  refine ⟨fun p q Ψ t Hp Hq => ?_, fun n hn => ?_⟩
  · cases p with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at Hp; subst Hp
      cases q with
      | zero => simp only [weaken_var']
      | succ q' =>
        simp only [List.getElem?_cons_succ] at Hq
        simp only [weaken_var']
        rw [hw 0 q' Δ t (by simp) Hq]
    | succ p' =>
      simp only [List.getElem?_cons_succ] at Hp
      simp only [weaken_var']
      rw [hw (p'+1) q Ψ t Hp Hq]
  · cases n with
    | zero => simp [offset_ren]
    | succ n' =>
      simp only [off_cons_succ]
      exact ho (n'+1) (by simp only [List.length_cons] at hn ⊢; omega)

theorem REN.AgreeOn.global_lift {ρ1 ρ2 : REN} {Γ : CTX.{i}}
    (h : REN.AgreeOn ρ1 ρ2 Γ) : REN.AgreeOn ρ1.global_lift ρ2.global_lift ([] :: Γ) := by
  obtain ⟨hw, ho⟩ := h
  refine ⟨fun p q Ψ t Hp Hq => ?_, fun n hn => ?_⟩
  · cases p with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at Hp; subst Hp; simp at Hq
    | succ p' =>
      simp only [List.getElem?_cons_succ] at Hp
      simp only [weaken_var']
      rw [hw p' q Ψ t Hp Hq]
  · cases n with
    | zero => simp [offset_ren]
    | succ n' =>
      simp only [off_global_lift_succ]
      rw [ho n' (by simp only [List.length_cons] at hn; omega)]

theorem REN.AgreeOn.cut {ρ1 ρ2 : REN} {Γ : CTX.{i}} (h : REN.AgreeOn ρ1 ρ2 Γ) (n : Nat)
    (hn : n < Γ.length) : REN.AgreeOn (cut_ren ρ1 n) (cut_ren ρ2 n) (Γ.drop n) := by
  obtain ⟨hw, ho⟩ := h
  have hoffn := ho n hn
  refine ⟨fun p q Ψ t Hp Hq => ?_, fun k hk => ?_⟩
  · have Hp' : Γ[n + p]? = some Ψ := by rw [List.getElem?_drop] at Hp; exact Hp
    have hwk := hw (n + p) q Ψ t Hp' Hq
    have e1 := wvar_cut ρ1 n p q
    have e2 := wvar_cut ρ2 n p q
    rw [hwk, e2] at e1
    rw [hoffn] at e1
    rcases hr1 : weaken_var' (cut_ren ρ1 n) p q with ⟨a1, b1⟩
    rcases hr2 : weaken_var' (cut_ren ρ2 n) p q with ⟨a2, b2⟩
    rw [hr1, hr2] at e1
    simp only [Prod.mk.injEq] at e1 ⊢
    omega
  · rw [List.length_drop] at hk
    have hnk : n + k < Γ.length := by omega
    have c1 := offset_cut ρ1 n k
    have c2 := offset_cut ρ2 n k
    rw [ho (n + k) hnk, hoffn] at c1
    omega

theorem weaken_congr_typed {Γ : CTX.{i}} {e : EXPR.{i}} {τ : TYPE.{i}} (H : TYPED Γ e τ) :
    ∀ {ρ1 ρ2 : REN}, REN.AgreeOn ρ1 ρ2 Γ → _root_.weaken e ρ1 = _root_.weaken e ρ2 := by
  induction H with
  | embed h => intro ρ1 ρ2 hag; rfl
  | embed_apply Hf Hx IHf IHx => intro ρ1 ρ2 hag; simp only [weaken]; rw [IHf hag, IHx hag]
  | pure h IH => intro ρ1 ρ2 hag; simp only [weaken]; rw [IH hag]
  | @var' Γ Δ τ p q Hp Hq =>
    intro ρ1 ρ2 hag
    simp only [weaken]; rw [hag.1 p q Δ τ Hp Hq]
  | app Hf Hx IHf IHx => intro ρ1 ρ2 hag; simp only [weaken]; rw [IHf hag, IHx hag]
  | @lam' Γ Δ A B e He IH => intro ρ1 ρ2 hag; simp only [weaken]; rw [IH (hag.cons A)]
  | @delay Γ e A h He IH => intro ρ1 ρ2 hag; simp only [weaken]; rw [IH hag.global_lift]
  | @adv n Γ e A hn He IH =>
    intro ρ1 ρ2 hag
    simp only [weaken]
    have hnlen : n < Γ.length := by
      have := typing_stack_len He; simp only [List.length_drop] at this; omega
    rw [hag.2 n hnlen, IH (hag.cut n hnlen)]
  | @fix' Γ Δ e A He IH => intro ρ1 ρ2 hag; simp only [weaken]; rw [IH (hag.cons _)]
  | pair He He' IH IH' => intro ρ1 ρ2 hag; simp only [weaken]; rw [IH hag, IH' hag]
  | projL He IH => intro ρ1 ρ2 hag; simp only [weaken]; rw [IH hag]
  | projR He IH => intro ρ1 ρ2 hag; simp only [weaken]; rw [IH hag]
  | inl He IH => intro ρ1 ρ2 hag; simp only [weaken]; rw [IH hag]
  | inr He IH => intro ρ1 ρ2 hag; simp only [weaken]; rw [IH hag]
  | case He Hf Hg IHe IHf IHg => intro ρ1 ρ2 hag; simp only [weaken]; rw [IHe hag, IHf hag, IHg hag]
  | or He He' IH IH' => intro ρ1 ρ2 hag; simp only [weaken]; rw [IH hag, IH' hag]
  | and He He' IH IH' => intro ρ1 ρ2 hag; simp only [weaken]; rw [IH hag, IH' hag]
  | impl He He' IH IH' => intro ρ1 ρ2 hag; simp only [weaken]; rw [IH hag, IH' hag]
  | @forall' Γ Δ A e He IH => intro ρ1 ρ2 hag; simp only [weaken]; rw [IH (hag.cons _)]
  | @exists' Γ Δ A e He IH => intro ρ1 ρ2 hag; simp only [weaken]; rw [IH (hag.cons _)]
  | lift He IH => intro ρ1 ρ2 hag; simp only [weaken]; rw [IH hag]
  | true h => intro ρ1 ρ2 hag; rfl
  | false h => intro ρ1 ρ2 hag; rfl
  | eq He He' IH IH' => intro ρ1 ρ2 hag; simp only [weaken]; rw [IH hag, IH' hag]
  | ax t f h => intro ρ1 ρ2 hag; rfl

theorem weaken_closed_gen {Γ : CTX.{i}} {e : EXPR.{i}} {τ : TYPE.{i}}
    (H : TYPED Γ e τ) {σ : REN} (h : REN.AgreeOn σ REN.id Γ) : weaken e σ = e :=
  (weaken_congr_typed H h).trans (weaken_id e)

theorem weaken_closed {e : EXPR.{i}} {τ : TYPE.{i}} {σ : REN}
    (H : TYPED [[]] e τ) : weaken e σ = e := by
  refine weaken_closed_gen H ?_
  refine ⟨?_, ?_⟩
  · intro n m Δ t hn hm
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hn
      subst hn
      simp at hm
    | succ n' => simp at hn
  · intro n hn
    simp only [List.length_singleton] at hn
    interval_cases n
    simp

theorem quote_eq_expr {τ : TYPE.{i}} (e : SYNT.{i} τ) (n : Nat) (m : Option Nat) :
    EXPR.quote e n m = e.expr := by
  rw [EXPR.quote]
  exact weaken_closed e.proof

theorem weaken_quote {τ : TYPE.{i}} (e : SYNT.{i} τ) (k : Nat) (m : Option Nat) (σ : REN) :
    weaken (EXPR.quote e k m) σ = EXPR.quote e k m := by
  rw [quote_eq_expr e k m]
  exact weaken_closed e.proof

theorem quote_reoffset {τ : TYPE.{i}} (e : SYNT.{i} τ) (n : Nat) (m : Option Nat)
    (n' : Nat) (m' : Option Nat) : EXPR.quote e n m = EXPR.quote e n' m' := by
  rw [quote_eq_expr e n m, quote_eq_expr e n' m']

@[simp] theorem weaken_synt_expr {τ : TYPE.{i}} (e : SYNT.{i} τ) (σ : REN) :
    weaken e.expr σ = e.expr :=
  weaken_closed e.proof

theorem TYPED.reexpr {Γ : CTX.{i}} {e e' : EXPR.{i}} {τ : TYPE.{i}}
    (h : e = e') (H : TYPED Γ e' τ) : TYPED Γ e τ := h ▸ H

end prf
