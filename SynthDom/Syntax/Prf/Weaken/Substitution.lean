module

public import SynthDom.Syntax.Prf.WeakenCore

@[expose] public section

section prf
open Lean

theorem asm_nat (n : Nat) (σ : REN) :
    REN.equiv (REN.comp (REN.global_shift n REN.id) σ)
              (REN.comp (cut_ren σ n) (REN.global_shift (offset_ren σ n) REN.id)) := by
  refine ⟨fun a b => ?_, fun a => ?_⟩
  · show weaken_var' (REN.comp (REN.global_shift n REN.id) σ) a b =
      weaken_var' (REN.comp (cut_ren σ n)
        (REN.global_shift (offset_ren σ n) REN.id)) a b
    simp only [weaken_var']
    rw [wvar_cut σ n a b]
  · show offset_ren (REN.comp (REN.global_shift n REN.id) σ) a =
      offset_ren (REN.comp (cut_ren σ n)
        (REN.global_shift (offset_ren σ n) REN.id)) a
    rw [offset_comp_all, offset_comp_all]
    cases a with
    | zero => simp
    | succ a' =>
      obtain ⟨j, hj⟩ : ∃ j, offset_ren (cut_ren σ n) (a' + 1) = j + 1 :=
        ⟨_, (Nat.succ_pred_eq_of_pos (offset_succ_pos _ _)).symm⟩
      rw [off_global_shift_succ, off_id, ← offset_cut σ n (a' + 1), hj, off_global_shift_succ, off_id, ← hj]

theorem subst_var_sr (σ : SUBST.{i}) (δ : REN) (Hσ : TSUBST σ Γ Δ) (m : Nat) (τ)
    (Hm : Δ[m]? = some τ) : weaken (subst_var σ 0 m) δ = subst_var (σ.sr_compose δ) 0 m := by
  induction Hσ generalizing m with
  | epsilon h => simp at Hm
  | cons He Hσ IH =>
    cases m with
    | zero => simp [subst_var, SUBST.sr_compose]
    | succ m' => simp only [subst_var, SUBST.sr_compose]; exact IH m' (by simpa using Hm)

theorem ssubst_var_sr (ss : SSUBST.{i}) (Γ Δ : CTX) (Hσ : TSSUBST ss Γ Δ) :
    ∀ (δ : REN) (n m : Nat) (Ψ τ), Δ[n]? = some Ψ → Ψ[m]? = some τ →
    weaken (ssubst_var ss n m) δ = ssubst_var (ss.sr_compose δ) n m := by
  induction Hσ with
  | single σ Hσ =>
    intro δ n m Ψ τ Hn Hm
    cases n with
    | zero =>
      simp only [ssubst_var, SSUBST.sr_compose]
      simp only [List.getElem?_cons_zero, Option.some.injEq] at Hn; subst Hn
      exact subst_var_sr σ δ Hσ m τ Hm
    | succ n' => simp at Hn
  | wk p Hp Hpeq Hσs Hσ IHs =>
    intro δ n m Ψ τ Hn Hm
    cases n with
    | zero =>
      simp only [ssubst_var, SSUBST.sr_compose]
      simp only [List.getElem?_cons_zero, Option.some.injEq] at Hn; subst Hn
      exact subst_var_sr _ δ Hσ m τ Hm
    | succ n' =>
      simp only [ssubst_var, SSUBST.sr_compose]
      simp only [List.getElem?_cons_succ] at Hn
      rw [weaken_comp, weaken_congr _ (asm_nat p δ), ← weaken_comp,
          IHs (cut_ren δ p) n' m Ψ τ Hn Hm]

theorem shift_cons (δ : REN) :
    REN.equiv (REN.comp (REN.local_weaken REN.id) δ.cons) (REN.comp δ (REN.local_weaken REN.id)) := by
  refine ⟨fun a b => ?_, fun a => ?_⟩
  · cases a with
    | zero =>
      show weaken_var' δ.cons 0 (b + 1) = _
      rcases hd : weaken_var' δ 0 b with ⟨a', b'⟩
      cases a' <;> simp [hd, weaken_var']
    | succ n =>
      show weaken_var' δ.cons (n + 1) b = _
      rcases hd : weaken_var' δ (n + 1) b with ⟨a', b'⟩
      cases a' <;> simp [hd, weaken_var']
  · cases a with
    | zero => simp [offset_ren]
    | succ n =>
      rw [offset_comp_all, offset_comp_all, off_lw_succ, off_id, off_cons_succ]
      obtain ⟨j, hj⟩ : ∃ j, offset_ren δ (n + 1) = j + 1 :=
        ⟨_, (Nat.succ_pred_eq_of_pos (offset_succ_pos _ _)).symm⟩
      rw [hj, off_lw_succ, off_id]

theorem subst_drop_sr (σ : SUBST.{i}) (δ : REN) : (σ.drop).sr_compose (δ.cons) = (σ.sr_compose δ).drop := by
  simp only [SUBST.drop]
  induction σ with
  | epsilon => rfl
  | cons e σ IH =>
    simp only [SUBST.sr_compose, SUBST.sr_compose, IH]
    rw [weaken_comp, weaken_comp, weaken_congr e (shift_cons δ)]

theorem subst_ext_sr (σ : SUBST.{i}) (δ : REN) : (σ.ext').sr_compose (δ.cons) = (σ.sr_compose δ).ext' := by
  simp only [SUBST.ext', SUBST.sr_compose, subst_drop_sr]; rfl

theorem ssubst_ext_sr (σ : SSUBST.{i}) (Γ Δ : CTX) (Hσ : TSSUBST σ Γ Δ) (δ : REN) :
    (σ.ext').sr_compose (δ.cons) = (σ.sr_compose δ).ext' := by
  cases Hσ with
  | single s Hs => simp only [SSUBST.ext', SSUBST.sr_compose, subst_ext_sr]
  | wk n Hn Hneq Hσs Hs =>
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp only [SSUBST.ext', SSUBST.sr_compose, subst_ext_sr, off_cons_succ, cut_cons_succ]

theorem wk1_sr (σ : SSUBST.{i}) (δ : REN) :
    (SSUBST.wk 1 σ .epsilon).sr_compose (δ.global_lift) = SSUBST.wk 1 (σ.sr_compose δ) .epsilon := by
  simp only [SSUBST.sr_compose]
  congr 1
  · simp [offset_ren]
  · congr 1; simp [cut_ren]

theorem offset_ssubst_sr (σ : SSUBST.{i}) (Γ Δ : CTX) (Hσ : TSSUBST σ Γ Δ) (δ : REN) (i : Nat)
    (hi : i < Δ.length) : offset_ssubst (σ.sr_compose δ) i = offset_ren δ (offset_ssubst σ i) := by
  induction Hσ generalizing δ i with
  | single s Hs =>
    cases i with
    | zero => simp
    | succ i' => simp only [List.length_singleton] at hi; omega
  | @wk σs Γdom Δs σhd Ψ Δ0 n Hn Hneq Hσs Hσ' IH =>
    cases i with
    | zero => simp
    | succ i' =>
      simp only [SSUBST.sr_compose, offset_ssubst]
      have hi' : i' < Δs.length := by simp only [List.length_cons] at hi; omega
      rw [IH (cut_ren δ n) i' hi', ← offset_cut δ n (offset_ssubst σs i')]

theorem cut_ssubst_sr (σ : SSUBST.{i}) (Γ Δ : CTX) (Hσ : TSSUBST σ Γ Δ) (δ : REN) (i : Nat)
    (hi : i < Δ.length) :
    cut_ssubst (σ.sr_compose δ) i = (cut_ssubst σ i).sr_compose (cut_ren δ (offset_ssubst σ i)) := by
  induction Hσ generalizing δ i with
  | single s Hs =>
    cases i with
    | zero => simp [cut_ssubst]
    | succ i' => simp only [List.length_singleton] at hi; omega
  | @wk σs Γdom Δs σhd Ψ Δ0 n Hn Hneq Hσs Hσ' IH =>
    cases i with
    | zero => simp [cut_ssubst]
    | succ i' =>
      simp only [SSUBST.sr_compose, cut_ssubst, offset_ssubst]
      have hi' : i' < Δs.length := by simp only [List.length_cons] at hi; omega
      rw [IH (cut_ren δ n) i' hi', cut_cut]

def TSSUBST.ext_typing_auto {ss : SSUBST.{i}} {Δ' : CTX.{i}} {Δ : OCTX.{i}} {Γs : CTX.{i}}
    {τ : TYPE.{i}} (Hσ : TSSUBST ss Δ' (Δ :: Γs)) :
    TSSUBST ss.ext' ((τ :: Δ'.headD []) :: Δ'.tail) ((τ :: Δ) :: Γs) :=
  match Δ', Hσ with
  | _ :: _, Hσ => TSSUBST.ext_typing' rfl rfl Hσ
  | [], Hσ => absurd (ssubst_len _ Hσ) (by simp)

theorem weaken_binds {Γ : CTX.{i}} {e : EXPR.{i}} {τ : TYPE.{i}} (H : TYPED Γ e τ) :
    ∀ {ss : SSUBST.{i}} {Δ' : CTX.{i}}, TSSUBST ss Δ' Γ → ∀ (δ : REN),
    weaken (binds ss e) δ = binds (ss.sr_compose δ) e := by
  induction H with
  | embed h => intro ss Δ' Hσ δ; rfl
  | embed_apply Hf Hx IHf IHx =>
    intro ss Δ' Hσ δ; simp only [embed_apply_subst, weaken]; rw [IHf Hσ, IHx Hσ]
  | pure h IH => intro ss Δ' Hσ δ; simp only [pure_subst, weaken]; rw [IH Hσ]
  | @var' Γ Δ τ p q Hp Hq =>
    intro ss Δ' Hσ δ
    show weaken (ssubst_var ss p q) δ = ssubst_var (ss.sr_compose δ) p q
    exact ssubst_var_sr ss Δ' Γ Hσ δ p q Δ τ Hp Hq
  | app Hf Hx IHf IHx => intro ss Δ' Hσ δ; simp only [app_subst, weaken]; rw [IHf Hσ, IHx Hσ]
  | lam' He IH =>
    intro ss Δ' Hσ δ
    simp only [binds, weaken]
    rw [IH (TSSUBST.ext_typing_auto Hσ) δ.cons, ssubst_ext_sr _ _ _ Hσ]
  | @delay Γ e A h He IH =>
    intro ss Δ' Hσ δ
    simp only [delay_subst, weaken]
    rw [IH (TSSUBST.wk 1 (Ψ := [[]]) (by simp) (by simp)
        (ssubst_transport_right (by simp) Hσ) (TSUBST.epsilon (by simp))) δ.global_lift, wk1_sr]
  | @adv n Γ e A hn He IH =>
    intro ss Δ' Hσ δ
    simp only [adv_subst, weaken]
    have hnlen : n < Γ.length := by
      have := typing_stack_len He
      simp only [List.length_drop] at this; omega
    rw [offset_ssubst_sr ss Δ' Γ Hσ δ n hnlen, cut_ssubst_sr ss Δ' Γ Hσ δ n hnlen]
    congr 1
    exact IH (cut_ssubst_typing ss Hσ n hnlen) (cut_ren δ (offset_ssubst ss n))
  | fix' He IH =>
    intro ss Δ' Hσ δ
    simp only [binds, weaken]
    rw [IH (TSSUBST.ext_typing_auto Hσ) δ.cons, ssubst_ext_sr _ _ _ Hσ]
  | pair He He' IH IH' =>
    intro ss Δ' Hσ δ; simp only [pair_subst, weaken]; rw [IH Hσ, IH' Hσ]
  | projL He IH => intro ss Δ' Hσ δ; simp only [proj_subst, weaken]; rw [IH Hσ]
  | projR He IH => intro ss Δ' Hσ δ; simp only [proj_subst, weaken]; rw [IH Hσ]
  | inl He IH => intro ss Δ' Hσ δ; simp only [inl_subst, weaken]; rw [IH Hσ]
  | inr He IH => intro ss Δ' Hσ δ; simp only [inr_subst, weaken]; rw [IH Hσ]
  | case He Hf Hg IHe IHf IHg => intro ss Δ' Hσ δ; simp only [case_subst, weaken]; rw [IHe Hσ, IHf Hσ, IHg Hσ]
  | or He He' IH IH' => intro ss Δ' Hσ δ; simp only [or_subst, weaken]; rw [IH Hσ, IH' Hσ]
  | and He He' IH IH' => intro ss Δ' Hσ δ; simp only [and_subst, weaken]; rw [IH Hσ, IH' Hσ]
  | impl He He' IH IH' => intro ss Δ' Hσ δ; simp only [impl_subst, weaken]; rw [IH Hσ, IH' Hσ]
  | forall' He IH =>
    intro ss Δ' Hσ δ
    simp only [binds, weaken]
    rw [IH (TSSUBST.ext_typing_auto Hσ) δ.cons, ssubst_ext_sr _ _ _ Hσ]
  | exists' He IH =>
    intro ss Δ' Hσ δ
    simp only [binds, weaken]
    rw [IH (TSSUBST.ext_typing_auto Hσ) δ.cons, ssubst_ext_sr _ _ _ Hσ]
  | lift He IH => intro ss Δ' Hσ δ; simp only [lift_subst, weaken]; rw [IH Hσ]
  | true h => intro ss Δ' Hσ δ; rfl
  | false h => intro ss Δ' Hσ δ; rfl
  | eq He He' IH IH' => intro ss Δ' Hσ δ; simp only [eq_subst, weaken]; rw [IH Hσ, IH' Hσ]
  | ax t f h => intro ss Δ' Hσ δ; rfl

theorem offset_cut_ss (σ : SSUBST.{i}) (a b : Nat) :
    offset_ssubst σ a + offset_ssubst (cut_ssubst σ a) b = offset_ssubst σ (a + b) := by
  induction σ generalizing a b with
  | single s => cases a <;> cases b <;> simp [offset_ssubst, cut_ssubst]
  | wk p σs sh IHs =>
    cases a with
    | zero => simp
    | succ a =>
      simp only [offset_ssubst, cut_ssubst]; rw [show a+1+b = (a+b)+1 from by omega]
      simp only [offset_ssubst]; have := IHs a b; omega

theorem cut_cut_ss (σ : SSUBST.{i}) (a b : Nat) :
    cut_ssubst (cut_ssubst σ a) b = cut_ssubst σ (a + b) := by
  induction σ generalizing a b with
  | single s => cases a <;> cases b <;> simp [cut_ssubst]
  | wk p σs sh IHs =>
    cases a with
    | zero => simp
    | succ a =>
      simp only [cut_ssubst]; rw [show a+1+b = (a+b)+1 from by omega]; simp only [cut_ssubst]
      exact IHs a b

theorem subst_sr_id (σ : SUBST.{i}) : σ.sr_compose REN.id = σ := by
  induction σ with
  | epsilon => rfl
  | cons e σ IH => simp only [SUBST.sr_compose, weaken_id, IH]

theorem ssubst_sr_id (σ : SSUBST.{i}) : σ.sr_compose REN.id = σ := by
  induction σ with
  | single s => simp only [SSUBST.sr_compose, subst_sr_id]
  | wk p σs σ IH => simp only [SSUBST.sr_compose, off_id, cut_id, IH, subst_sr_id]

theorem id_cons_ext (τ : TYPE.{i}) (Δ : OCTX.{i}) (Γs : CTX.{i}) :
    SSUBST.id (((τ::Δ)::Γs).map List.length) = (SSUBST.id ((Δ::Γs).map List.length)).ext' := by
  cases Γs with
  | nil => simp [SSUBST.id, SSUBST.ext', SUBST.id, SUBST.ext']
  | cons x xs =>
    simp only [List.map_cons, SSUBST.id, SSUBST.ext']
    congr 1

private def subst_len' : SUBST.{i} → Nat
  | .epsilon => 0
  | .cons _ σ => subst_len' σ + 1

private theorem subst_len_sr (σ : SUBST.{i}) (δ : REN) :
    subst_len' (σ.sr_compose δ) = subst_len' σ := by
  induction σ with
  | epsilon => rfl
  | cons e σ IH => simp only [SUBST.sr_compose, subst_len', IH]

private theorem subst_id_len (k : Nat) : subst_len' (SUBST.id.{i} k) = k := by
  induction k with
  | zero => rfl
  | succ k IH =>
    show subst_len' (SUBST.ext' (SUBST.id k)) = k + 1
    simp only [SUBST.ext', subst_len', SUBST.drop, subst_len_sr, IH]

private theorem subst_var_sr_inrange (σ : SUBST.{i}) (δ : REN) : ∀ (n m : Nat), m < subst_len' σ →
    subst_var (σ.sr_compose δ) n m = weaken (subst_var σ n m) δ := by
  induction σ with
  | epsilon => intro n m h; simp [subst_len'] at h
  | cons e σ IH =>
    intro n m h
    cases m with
    | zero => simp [SUBST.sr_compose, subst_var]
    | succ m' =>
      simp only [SUBST.sr_compose, subst_var]; exact IH n m' (by simp [subst_len'] at h; omega)

theorem subst_var_id (k : Nat) : ∀ (q : Nat), q < k → subst_var (SUBST.id k) 0 q = EXPR.var' 0 q := by
  induction k with
  | zero => intro q Hq; omega
  | succ k IH =>
    intro q Hq
    cases q with
    | zero => simp [SUBST.id, SUBST.ext', subst_var]
    | succ q' =>
      simp only [SUBST.id, SUBST.ext', subst_var, SUBST.drop]
      rw [subst_var_sr_inrange _ _ _ _ (by rw [subst_id_len]; omega), IH q' (by omega)]
      simp [weaken, weaken_var']

private def HeadId (k : Nat) (σ : SUBST.{i}) : Prop :=
  ∀ m, m < k → m < subst_len' σ ∧ subst_var σ 0 m = .var' 0 m

private theorem weaken_var'_lw_id (m : Nat) :
    weaken (EXPR.var'.{i} 0 m) (REN.local_weaken REN.id) = EXPR.var' 0 (m + 1) := by
  simp [weaken, weaken_var']

private theorem weaken_var'_global_shift_one (n m : Nat) :
    weaken (EXPR.var'.{i} n m) (REN.global_shift 1 REN.id) = EXPR.var' (n + 1) m := by
  simp [weaken, weaken_var', Nat.add_comm]

private theorem HeadId.ext' {k : Nat} {σ : SUBST.{i}} (h : HeadId k σ) :
    HeadId (k + 1) σ.ext' := by
  intro m hm
  cases m with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp only [SUBST.ext', SUBST.drop, subst_len', subst_len_sr]; omega
    · simp [SUBST.ext', subst_var]
  | succ m' =>
    obtain ⟨hlen, hval⟩ := h m' (by omega)
    refine ⟨?_, ?_⟩
    · simp only [SUBST.ext', SUBST.drop, subst_len', subst_len_sr]; omega
    · show subst_var (SUBST.cons (.var' 0 0) (σ.sr_compose (REN.local_weaken REN.id))) 0 (m' + 1)
          = EXPR.var' 0 (m' + 1)
      simp only [subst_var]
      rw [subst_var_sr_inrange σ _ 0 m' hlen, hval, weaken_var'_lw_id]

private inductive BindTarget.{i} where
  | identity
  | subst (σ : SSUBST.{i})

@[simp] private def BindTarget.fold (target : BindTarget.{i}) (identity : α)
    (subst : SSUBST.{i} → α) : α :=
  match target with
  | .identity => identity
  | .subst σ => subst σ

@[simp] private def BindTarget.map (target : BindTarget.{i})
    (f : SSUBST.{i} → SSUBST.{i}) : BindTarget.{i} :=
  target.fold .identity fun σ => .subst (f σ)

@[simp] private def BindTarget.apply (target : BindTarget.{i}) (e : EXPR.{i}) : EXPR.{i} :=
  target.fold e fun σ => binds σ e

@[simp] private def BindTarget.var (target : BindTarget.{i}) (n m : Nat) : EXPR.{i} :=
  target.fold (.var' n m) fun σ => ssubst_var σ n m

@[simp] private def BindTarget.offset (target : BindTarget.{i}) (n : Nat) : Nat :=
  target.fold n fun σ => offset_ssubst σ n

@[simp] private def BindTarget.ext (target : BindTarget.{i}) : BindTarget.{i} :=
  target.map (·.ext')

@[simp] private def BindTarget.delay (target : BindTarget.{i}) : BindTarget.{i} :=
  target.map fun σ => .wk 1 σ .epsilon

@[simp] private def BindTarget.cut (target : BindTarget.{i}) (n : Nat) : BindTarget.{i} :=
  target.map fun σ => cut_ssubst σ n

private inductive SubstOn : CTX.{i} → SSUBST.{i} → BindTarget.{i} → Prop where
  | refl {Γ : CTX.{i}} {σ : SSUBST.{i}} : SubstOn Γ σ (.subst σ)
  | identitySingle {Ψ : OCTX.{i}} {s : SUBST.{i}} (h : HeadId Ψ.length s) :
      SubstOn [Ψ] (.single s) .identity
  | identityWk {Ψ : OCTX.{i}} {Γ : CTX.{i}} {σs : SSUBST.{i}} {s : SUBST.{i}}
      (h : HeadId Ψ.length s) (tail : SubstOn Γ σs .identity) :
      SubstOn (Ψ :: Γ) (.wk 1 σs s) .identity
  | identityTop {Ψ : OCTX.{i}} {p : Nat} {σs : SSUBST.{i}} {s : SUBST.{i}}
      (h : HeadId Ψ.length s) : SubstOn [Ψ] (.wk p σs s) .identity
  | paddingTop {Ψ : OCTX.{i}} {p : Nat} {σs : SSUBST.{i}} {s : SUBST.{i}} :
      SubstOn [Ψ] (.wk p σs s) (.subst (.single s))
  | paddingWk {Ψ : OCTX.{i}} {Γ : CTX.{i}} {σs σs' : SSUBST.{i}} {s : SUBST.{i}}
      (p : Nat) (tail : SubstOn Γ σs (.subst σs')) :
      SubstOn (Ψ :: Γ) (.wk p σs s) (.subst (.wk p σs' s))

private theorem SubstOn.var {Γ : CTX.{i}} {σ : SSUBST.{i}} {target : BindTarget.{i}}
    (h : SubstOn Γ σ target) (n m : Nat) (Δ : OCTX.{i})
    (hn : Γ[n]? = some Δ) (hm : m < Δ.length) :
    ssubst_var σ n m = target.var n m := by
  induction h generalizing n m Δ with
  | refl => rfl
  | identitySingle hh =>
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hn
      subst hn
      exact (hh m hm).2
    | succ n => simp at hn
  | identityWk hh tail IH =>
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hn
      subst hn
      exact (hh m hm).2
    | succ n =>
      simp only [List.getElem?_cons_succ] at hn
      show weaken (ssubst_var _ n m) (REN.global_shift 1 REN.id) = _
      rw [IH n m Δ hn hm]
      exact weaken_var'_global_shift_one n m
  | identityTop hh =>
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hn
      subst hn
      exact (hh m hm).2
    | succ n => simp at hn
  | paddingTop =>
    cases n with
    | zero => rfl
    | succ n => simp at hn
  | paddingWk p tail IH =>
    cases n with
    | zero => rfl
    | succ n =>
      simp only [List.getElem?_cons_succ] at hn
      simp only [BindTarget.var, BindTarget.fold, ssubst_var]
      rw [IH n m Δ hn hm]
      rfl

private theorem SubstOn.offset {Γ : CTX.{i}} {σ : SSUBST.{i}} {target : BindTarget.{i}}
    (h : SubstOn Γ σ target) (n : Nat) (hn : n < Γ.length) :
    offset_ssubst σ n = target.offset n := by
  induction h generalizing n with
  | refl => rfl
  | identitySingle hh =>
    simp only [List.length_singleton] at hn
    interval_cases n
    rfl
  | identityWk hh tail IH =>
    cases n with
    | zero => rfl
    | succ n =>
      show 1 + offset_ssubst _ n = n + 1
      rw [IH n (by simp only [List.length_cons] at hn; omega)]
      simp only [BindTarget.offset, BindTarget.fold]
      omega
  | identityTop hh =>
    simp only [List.length_singleton] at hn
    interval_cases n
    rfl
  | paddingTop =>
    simp only [List.length_singleton] at hn
    interval_cases n
    rfl
  | paddingWk p tail IH =>
    cases n with
    | zero => rfl
    | succ n =>
      simp only [BindTarget.offset, BindTarget.fold, offset_ssubst]
      rw [IH n (by simp only [List.length_cons] at hn; omega)]
      rfl

private theorem SubstOn.ext {Ψ : OCTX.{i}} {Γs : CTX.{i}} {σ : SSUBST.{i}}
    {target : BindTarget.{i}} {A : TYPE.{i}} (h : SubstOn (Ψ :: Γs) σ target) :
    SubstOn ((A :: Ψ) :: Γs) σ.ext' target.ext := by
  cases h with
  | refl => exact .refl
  | identitySingle hh => exact .identitySingle (by simpa using hh.ext')
  | identityWk hh tail => exact .identityWk (by simpa using hh.ext') tail
  | identityTop hh => exact .identityTop (by simpa using hh.ext')
  | paddingTop => exact .paddingTop
  | paddingWk p tail => exact .paddingWk p tail

private theorem SubstOn.delay {Γ : CTX.{i}} {σ : SSUBST.{i}} {target : BindTarget.{i}}
    (h : SubstOn Γ σ target) : SubstOn ([] :: Γ) (.wk 1 σ .epsilon) target.delay := by
  cases target with
  | identity => exact .identityWk (fun m hm => by simp at hm) h
  | subst σ' => exact .paddingWk 1 h

private theorem SubstOn.cut {Γ : CTX.{i}} {σ : SSUBST.{i}} {target : BindTarget.{i}}
    (h : SubstOn Γ σ target) (n : Nat) (hn : n < Γ.length) :
    SubstOn (Γ.drop n) (cut_ssubst σ n) (target.cut n) := by
  induction h generalizing n with
  | refl => exact .refl
  | identitySingle hh =>
    simp only [List.length_singleton] at hn
    interval_cases n
    exact .identitySingle hh
  | identityWk hh tail IH =>
    cases n with
    | zero => exact .identityWk hh tail
    | succ n => exact IH n (by simp only [List.length_cons] at hn; omega)
  | identityTop hh =>
    simp only [List.length_singleton] at hn
    interval_cases n
    exact .identityTop hh
  | paddingTop =>
    simp only [List.length_singleton] at hn
    interval_cases n
    exact .paddingTop
  | paddingWk p tail IH =>
    cases n with
    | zero => exact .paddingWk p tail
    | succ n => exact IH n (by simp only [List.length_cons] at hn; omega)

private theorem SubstOn.cons {Γ : CTX.{i}} {σ σ' : SSUBST.{i}} (e : EXPR.{i})
    (h : SubstOn Γ σ (.subst σ')) : SubstOn Γ (σ.cons e) (.subst (σ'.cons e)) := by
  cases h with
  | refl => exact .refl
  | paddingTop => exact .paddingTop
  | paddingWk p tail => exact .paddingWk p tail

private theorem SubstOn.ssubst_id : ∀ (L L' : List Nat) (Γ : CTX.{i}), L.length = Γ.length →
    0 < L.length → SubstOn Γ (SSUBST.id (L ++ L')) (.subst (SSUBST.id L))
  | [], _, _, _, h => absurd h (by simp)
  | [_], L', Γ, hlen, _ => by
    obtain ⟨Ψ, rfl⟩ : ∃ Ψ, Γ = [Ψ] := by
      rcases Γ with _ | ⟨Ψ, Γs⟩
      · simp at hlen
      · rcases Γs with _ | ⟨a, b⟩
        · exact ⟨Ψ, rfl⟩
        · simp at hlen
    cases L' with
    | nil => simpa using SubstOn.refl
    | cons m ms => exact .paddingTop
  | _ :: k :: ks, L', Γ, hlen, _ => by
    obtain ⟨Ψ, Γs, rfl⟩ : ∃ Ψ Γs, Γ = Ψ :: Γs := by
      rcases Γ with _ | ⟨Ψ, Γs⟩
      · simp at hlen
      · exact ⟨Ψ, Γs, rfl⟩
    exact .paddingWk 1 (SubstOn.ssubst_id (k :: ks) L' Γs
      (by simpa using hlen) (by simp))

private theorem binds_congr_gen {Γ : CTX.{i}} {e : EXPR.{i}} {τ : TYPE.{i}}
    (H : TYPED Γ e τ) : ∀ {σ target}, SubstOn Γ σ target → binds σ e = target.apply e := by
  induction H with
  | embed h => intro σ target hσ; cases target <;> rfl
  | embed_apply Hf Hx IHf IHx =>
    intro σ target hσ
    cases target <;> simp [binds, IHf hσ, IHx hσ]
  | pure h IH => intro σ target hσ; cases target <;> simp [binds, IH hσ]
  | @var' Γ Δ τ p q Hp Hq =>
    intro σ target hσ
    have hq : q < Δ.length := (List.getElem?_eq_some_iff.mp Hq).1
    change ssubst_var σ p q = target.var p q
    exact hσ.var p q Δ Hp hq
  | app Hf Hx IHf IHx =>
    intro σ target hσ
    cases target <;> simp [binds, IHf hσ, IHx hσ]
  | lam' He IH =>
    intro σ target hσ
    cases target <;> simp only [BindTarget.apply, BindTarget.fold, binds]
    all_goals (rw [IH hσ.ext]; rfl)
  | @delay Γ e A h He IH =>
    intro σ target hσ
    cases target <;> simp [binds, IH hσ.delay]
  | @adv n Γ e A hn He IH =>
    intro σ target hσ
    have hnlen : n < Γ.length := by
      have := typing_stack_len He
      simp only [List.length_drop] at this
      omega
    cases target <;> simp [binds, hσ.offset n hnlen, IH (hσ.cut n hnlen)]
  | fix' He IH =>
    intro σ target hσ
    cases target <;> simp only [BindTarget.apply, BindTarget.fold, binds]
    all_goals (rw [IH hσ.ext]; rfl)
  | pair He He' IH IH' =>
    intro σ target hσ
    cases target <;> simp [binds, IH hσ, IH' hσ]
  | projL He IH => intro σ target hσ; cases target <;> simp [binds, IH hσ]
  | projR He IH => intro σ target hσ; cases target <;> simp [binds, IH hσ]
  | inl He IH => intro σ target hσ; cases target <;> simp [binds, IH hσ]
  | inr He IH => intro σ target hσ; cases target <;> simp [binds, IH hσ]
  | case He Hf Hg IHe IHf IHg =>
    intro σ target hσ
    cases target <;> simp [binds, IHe hσ, IHf hσ, IHg hσ]
  | or He He' IH IH' =>
    intro σ target hσ; cases target <;> simp [binds, IH hσ, IH' hσ]
  | and He He' IH IH' =>
    intro σ target hσ; cases target <;> simp [binds, IH hσ, IH' hσ]
  | impl He He' IH IH' =>
    intro σ target hσ; cases target <;> simp [binds, IH hσ, IH' hσ]
  | forall' He IH =>
    intro σ target hσ
    cases target <;> simp only [BindTarget.apply, BindTarget.fold, binds]
    all_goals (rw [IH hσ.ext]; rfl)
  | exists' He IH =>
    intro σ target hσ
    cases target <;> simp only [BindTarget.apply, BindTarget.fold, binds]
    all_goals (rw [IH hσ.ext]; rfl)
  | lift He IH => intro σ target hσ; cases target <;> simp [binds, IH hσ]
  | true h => intro σ target hσ; cases target <;> rfl
  | false h => intro σ target hσ; cases target <;> rfl
  | eq He He' IH IH' =>
    intro σ target hσ; cases target <;> simp [binds, IH hσ, IH' hσ]
  | ax t f h => intro σ target hσ; cases target <;> rfl

theorem binds_closed {e : EXPR.{i}} {τ : TYPE.{i}} {σ : SSUBST.{i}}
    (H : TYPED [[]] e τ) : binds σ e = e := by
  change binds σ e = BindTarget.identity.apply e
  apply binds_congr_gen H
  match σ with
  | .single τ' => exact .identitySingle (fun m hm => by simp at hm)
  | .wk p σs τ' => exact .identityTop (fun m hm => by simp at hm)

theorem binds_single_subst_pad {Γ0 : OCTX.{i}} {Γs Γ' : CTX.{i}} {e e' : EXPR.{i}}
    {τ σ : TYPE.{i}} (H : TYPED ((τ :: Γ0) :: Γs) e σ) :
    binds (single_subst (List.map List.length (Γ0 :: (Γs ++ Γ'))) e') e
      = binds (single_subst (List.map List.length (Γ0 :: Γs)) e') e := by
  have hmap : List.map List.length (Γ0 :: (Γs ++ Γ'))
      = List.map List.length (Γ0 :: Γs) ++ List.map List.length Γ' := by simp
  rw [hmap]
  exact binds_congr_gen H (SubstOn.cons e'
    (SubstOn.ssubst_id _ _ _ (by simp) (by simp)))

private theorem HeadId.id (k : Nat) : HeadId k (SUBST.id.{i} k) :=
  fun m hm => ⟨by rw [subst_id_len]; exact hm, subst_var_id k m hm⟩

private theorem SubstOn.id : ∀ (Γ : CTX.{i}), 0 < Γ.length →
    SubstOn Γ (SSUBST.id (Γ.map List.length)) .identity
  | [_], _ => .identitySingle (HeadId.id _)
  | _ :: Δ :: Δs, _ => .identityWk (HeadId.id _) (SubstOn.id (Δ :: Δs) (by simp))

theorem binds_ctx_id {Γ : CTX.{i}} {e : EXPR.{i}} {τ : TYPE.{i}} (H : TYPED Γ e τ) :
    binds (SSUBST.id (Γ.map List.length)) e = e :=
  binds_congr_gen H (SubstOn.id Γ (typing_stack_len H))

@[simp] theorem binds_synt_expr {τ : TYPE.{i}} (e : SYNT.{i} τ) (σ : SSUBST.{i}) :
    binds σ e.expr = e.expr :=
  binds_closed e.proof

@[simp] theorem binds_quote {τ : TYPE.{i}} (e : SYNT.{i} τ) (k : Nat) (m : Option Nat)
    (σ : SSUBST.{i}) : binds σ (EXPR.quote e k m) = EXPR.quote e k m := by
  rw [quote_eq_expr e k m]
  exact binds_synt_expr e σ

theorem offset_ssubst_id (Γ : CTX.{i}) :
    ∀ n, n < Γ.length → offset_ssubst (SSUBST.id (Γ.map List.length)) n = n := by
  induction Γ with
  | nil => intro n h; simp at h
  | cons Δ Γs IH =>
    cases Γs with
    | nil => intro n h; simp at h; subst h; rfl
    | cons Δ2 Γs2 =>
      intro n h
      cases n with
      | zero => rfl
      | succ n' =>
        rw [List.map_cons, List.map_cons]
        show 1 + offset_ssubst (SSUBST.id (List.length Δ2 :: Γs2.map List.length)) n' = n' + 1
        rw [← List.map_cons, IH n' (by simp at h ⊢; omega)]; omega

theorem cut_ssubst_id (Γ : CTX.{i}) :
    ∀ n, n < Γ.length →
    cut_ssubst (SSUBST.id (Γ.map List.length)) n = SSUBST.id ((Γ.drop n).map List.length) := by
  induction Γ with
  | nil => intro n h; simp at h
  | cons Δ Γs IH =>
    cases Γs with
    | nil => intro n h; simp at h; subst h; rfl
    | cons Δ2 Γs2 =>
      intro n h
      cases n with
      | zero => rfl
      | succ n' =>
        rw [List.map_cons, List.map_cons]
        show cut_ssubst (SSUBST.id (List.length Δ2 :: Γs2.map List.length)) n'
          = SSUBST.id ((List.drop (n'+1) (Δ :: Δ2 :: Γs2)).map List.length)
        rw [← List.map_cons, IH n' (by simp at h ⊢; omega)]
        congr 1

theorem weaken_eq_binds {Γ : CTX.{i}} {e : EXPR.{i}} {τ : TYPE.{i}} (H : TYPED Γ e τ) :
    ∀ (δ : REN), weaken e δ = binds (δ.subst_of_ren (Γ.map List.length)) e := by
  intro δ
  calc
    weaken e δ = weaken (binds (SSUBST.id (Γ.map List.length)) e) δ :=
      congrArg (weaken · δ) (binds_ctx_id H).symm
    _ = binds ((SSUBST.id (Γ.map List.length)).sr_compose δ) e :=
      weaken_binds H (TSSUBST.id Γ (typing_stack_len H)) δ
    _ = binds (δ.subst_of_ren (Γ.map List.length)) e := rfl

theorem weaken_global_shift_zero (e : EXPR.{i}) : weaken e (REN.global_shift 0 REN.id) = e :=
  weaken_eq_self equiv_global_shift_zero_id e

theorem global_shift_comp_equiv (a r : Nat) :
    REN.equiv (REN.comp (REN.global_shift a REN.id) (REN.global_shift r REN.id))
      (REN.global_shift (r + a) REN.id) := by
  refine ⟨fun n m => ?_, fun n => ?_⟩
  · simp only [weaken_var']
    rcases h : weaken_var' REN.id n m with ⟨a', b'⟩
    simp only [weaken_var'] at h
    obtain ⟨rfl, rfl⟩ : a' = n ∧ b' = m := by simpa using h.symm
    congr 1
    omega
  · simp only [offset_comp_all]
    cases n with
    | zero => simp [offset_ren]
    | succ n' =>
      rw [off_global_shift_succ, off_id]
      rw [show a + (n' + 1) = (a + n') + 1 from by omega,
        off_global_shift_succ, off_id, off_global_shift_succ, off_id]
      omega

theorem ssubst_var_shift (σ : SSUBST.{i}) (Γ Δ : CTX.{i}) (Hσ : TSSUBST σ Γ Δ) :
    ∀ (p n m : Nat) (Ψ τ), p < Δ.length → Δ[p+n]? = some Ψ → Ψ[m]? = some τ →
    ssubst_var σ (p+n) m
      = weaken (ssubst_var (cut_ssubst σ p) n m) (REN.global_shift (offset_ssubst σ p) REN.id) := by
  induction Hσ with
  | single s Hs =>
    intro p n m Ψ τ hp Hn Hm
    cases p with
    | zero => simp only [Nat.zero_add, cut_ssubst_zero, offset_ssubst_zero, weaken_global_shift_zero]
    | succ p' => simp only [List.length_singleton] at hp; omega
  | @wk σs Γd Δs sh Ψ0 Δ0 r Hr Hreq Hσs Hs IH =>
    intro p n m Ψ τ hp Hn Hm
    cases p with
    | zero => simp only [Nat.zero_add, cut_ssubst_zero, offset_ssubst_zero, weaken_global_shift_zero]
    | succ p' =>
      have hp' : p' < Δs.length := by simp only [List.length_cons] at hp; omega
      rw [show p'+1+n = (p'+n)+1 from by omega, List.getElem?_cons_succ] at Hn
      rw [show p'+1+n = (p'+n)+1 from by omega]
      show weaken (ssubst_var σs (p'+n) m) (REN.global_shift r REN.id)
        = weaken (ssubst_var (cut_ssubst σs p') n m)
            (REN.global_shift (r + offset_ssubst σs p') REN.id)
      rw [IH p' n m Ψ τ hp' Hn Hm, weaken_comp,
          weaken_congr _ (global_shift_comp_equiv (offset_ssubst σs p') r)]

def SUBST.tail : SUBST.{i} → SUBST.{i}
  | .epsilon => .epsilon
  | .cons _ σ => σ

def SSUBST.head0 : SSUBST.{i} → SUBST.{i}
  | .single τ => τ
  | .wk _ _ τ => τ

def SSUBST.tick0slot0 (σ : SSUBST.{i}) : EXPR.{i} :=
  subst_var σ.head0 0 0

def SSUBST.drop0 : SSUBST.{i} → SSUBST.{i}
  | .single τ => .single τ.tail
  | .wk n σs τ => .wk n σs τ.tail

def SSUBST.scr (σ : SSUBST.{i}) : REN → SSUBST.{i}
  | .id => σ
  | .comp δ1 δ2 => (σ.scr δ2).scr δ1
  | .local_weaken δ' => σ.drop0.scr δ'
  | .cons δ' => (σ.drop0.scr δ').cons σ.tick0slot0
  | .global_lift δ' =>
    match σ with
    | .single τ => .single τ
    | .wk r σs τ => .wk r (σs.scr δ') τ
  | .global_shift p δ' =>
    (cut_ssubst σ p).scr δ' |>.sr_compose (REN.global_shift (offset_ssubst σ p) REN.id)

theorem subst_var_tail (e : EXPR.{i}) (τ : SUBST.{i}) (n m : Nat) :
    subst_var (SUBST.cons e τ).tail n m = subst_var (SUBST.cons e τ) n (m + 1) := by
  simp [SUBST.tail, subst_var]

theorem ssubst_var_drop0_succ_wk (r : Nat) (σs : SSUBST.{i}) (τ : SUBST.{i}) (p m : Nat) :
    ssubst_var (SSUBST.wk r σs τ).drop0 (p + 1) m = ssubst_var (SSUBST.wk r σs τ) (p + 1) m := by
  simp [SSUBST.drop0, ssubst_var]

theorem ssubst_var_cons_succ_wk (e : EXPR.{i}) (r : Nat) (σs : SSUBST.{i}) (τ : SUBST.{i})
    (p m : Nat) :
    ssubst_var ((SSUBST.wk r σs τ).cons e) (p + 1) m = ssubst_var (SSUBST.wk r σs τ) (p + 1) m := by
  simp [SSUBST.cons, ssubst_var]

theorem ssubst_var_cons_zero_zero (e : EXPR.{i}) (σ : SSUBST.{i}) :
    ssubst_var (σ.cons e) 0 0 = e := by
  cases σ <;> simp [SSUBST.cons, ssubst_var, subst_var]

theorem ssubst_var_cons_zero_succ (e : EXPR.{i}) (σ : SSUBST.{i}) (m : Nat) :
    ssubst_var (σ.cons e) 0 (m + 1) = ssubst_var σ 0 m := by
  cases σ <;> simp [SSUBST.cons, ssubst_var, subst_var]

theorem subst_var_tail_inrange {τ : SUBST.{i}} {Γ : CTX.{i}} {Δ : OCTX.{i}} (Hτ : TSUBST τ Γ Δ)
    (hΔ : 0 < Δ.length) (q : Nat) : subst_var τ.tail 0 q = subst_var τ 0 (q+1) := by
  cases Hτ with
  | epsilon h => simp at hΔ
  | cons He Hσ => simp [SUBST.tail, subst_var]

theorem ssubst_var_drop0 {σ : SSUBST.{i}} {Γ : CTX.{i}} {t : TYPE.{i}} {Δ0 : OCTX.{i}}
    {Δs : CTX.{i}} (Hσ : TSSUBST σ Γ ((t :: Δ0) :: Δs)) :
    ∀ (p q Ψ τ), (Δ0 :: Δs)[p]? = some Ψ → Ψ[q]? = some τ →
    ssubst_var σ.drop0 p q = ssubst_var σ p (match p with | 0 => q+1 | _ => q) := by
  intro p q Ψ τ Hp Hq
  cases Hσ with
  | single s Hs =>
    cases p with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at Hp; subst Hp
      exact subst_var_tail_inrange Hs (by simp) q
    | succ p' => simp at Hp
  | wk r Hr Hreq Hσs Hs =>
    cases p with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at Hp; subst Hp
      exact subst_var_tail_inrange Hs (by simp) q
    | succ p' => exact ssubst_var_drop0_succ_wk r _ _ p' q

def TSUBST.tail_typing {τ : SUBST.{i}} {Γ : CTX.{i}} {t : TYPE.{i}} {Δ0 : OCTX.{i}}
    (Hτ : TSUBST τ Γ (t :: Δ0)) : TSUBST τ.tail Γ Δ0 := by
  cases Hτ with | cons He Hσ => exact Hσ

def TSSUBST.drop0_typing {σ : SSUBST.{i}} {Γ : CTX.{i}} {t : TYPE.{i}} {Δ0 : OCTX.{i}}
    {Δs : CTX.{i}} (Hσ : TSSUBST σ Γ ((t :: Δ0) :: Δs)) : TSSUBST σ.drop0 Γ (Δ0 :: Δs) := by
  cases Hσ with
  | single s Hs => exact TSSUBST.single _ (TSUBST.tail_typing Hs)
  | wk r Hr Hreq Hσs Hs => exact TSSUBST.wk r Hr Hreq Hσs (TSUBST.tail_typing Hs)

theorem TSSUBST.tick0slot0_typing {σ : SSUBST.{i}} {Γ : CTX.{i}} {t : TYPE.{i}} {Δ0 : OCTX.{i}}
    {Δs : CTX.{i}} (Hσ : TSSUBST σ Γ ((t :: Δ0) :: Δs)) : TYPED Γ σ.tick0slot0 t := by
  cases Hσ with
  | single s Hs => cases Hs with | cons He _ => exact He
  | wk r Hr Hreq Hσs Hs => cases Hs with | cons He _ => exact He

def global_shift_id_typing (Γ' : CTX.{i}) (a : Nat) (ha : a < Γ'.length) :
    TYPED_REN (REN.global_shift a REN.id) Γ' (Γ'.drop a) := by
  have e1 : Γ' = Γ'.take a ++ Γ'.drop a := (List.take_append_drop a Γ').symm
  have hlen : a = (Γ'.take a).length := by rw [List.length_take]; omega
  have hpos : 0 < (Γ'.drop a).length := by rw [List.length_drop]; omega
  conv_lhs => rw [e1]
  exact TYPED_REN.global_shift a hlen (TYPED_REN.id hpos)

theorem TSSUBST.scr_typing {δ : REN} {Γ Δ : CTX.{i}} (Hδ : TYPED_REN δ Γ Δ) :
    ∀ {σ : SSUBST.{i}} {Γ' : CTX.{i}}, TSSUBST σ Γ' Γ → Nonempty (TSSUBST (σ.scr δ) Γ' Δ) := by
  induction Hδ with
  | id h => intro σ Γ' Hσ; exact ⟨Hσ⟩
  | comp H1 H2 IH1 IH2 => intro σ Γ' Hσ; exact ⟨(IH1 (IH2 Hσ).some).some⟩
  | local_weaken t H IH => intro σ Γ' Hσ; exact ⟨(IH (TSSUBST.drop0_typing Hσ)).some⟩
  | cons t H IH =>
    intro σ Γ' Hσ
    exact ⟨TSSUBST.cons (IH (TSSUBST.drop0_typing Hσ)).some
      (TSSUBST.tick0slot0_typing Hσ)⟩
  | global_lift H IH =>
    intro σ Γ' Hσ
    cases Hσ with
    | single s Hs =>
      exfalso
      have h1 := ren_len _ H; have h2 := typing_ren_len H
      simp only [List.length_nil, Nat.le_zero_eq, List.length_eq_zero_iff] at h2
      simp only [h2, List.length_nil] at h1; exact absurd h1 (by simp)
    | wk r Hr Hreq Hσs Hs => exact ⟨TSSUBST.wk r Hr Hreq (IH Hσs).some Hs⟩
  | @global_shift σρ Γ0 Δ0 Ψ0 n hn H IH =>
    intro σ Γ' Hσ
    subst hn
    have hΓ0 : 0 < Γ0.length := by have := ren_len _ H; have := typing_ren_len H; omega
    have hn' : Ψ0.length < (Ψ0 ++ Γ0).length := by rw [List.length_append]; omega
    have hcut := cut_ssubst_typing σ Hσ Ψ0.length hn'
    rw [List.drop_append, Nat.sub_self, List.drop_eq_nil_of_le (le_refl _),
        List.nil_append] at hcut
    have hoff : offset_ssubst σ Ψ0.length < Γ'.length := offset_ssubst_len σ Hσ Ψ0.length hn'
    have hscr := (IH hcut).some
    refine ⟨?_⟩
    show TSSUBST (((cut_ssubst σ Ψ0.length).scr σρ).sr_compose
      (REN.global_shift (offset_ssubst σ Ψ0.length) REN.id)) Γ' Δ0
    exact TSSUBST.sr_compose_typing hscr (global_shift_id_typing Γ' (offset_ssubst σ Ψ0.length) hoff)

theorem ssubst_var_cons_succ_typed {X : SSUBST.{i}} {Γ' : CTX.{i}} {Φ : OCTX.{i}}
    {Δ0 : CTX.{i}} {e : EXPR.{i}}
    (HX : TSSUBST X Γ' (Φ :: Δ0)) (hΔ : 0 < Δ0.length) (p q : Nat) :
    ssubst_var (X.cons e) (p+1) q = ssubst_var X (p+1) q := by
  cases HX with
  | single s Hs => simp at hΔ
  | wk r Hr Hreq Hσs Hs => exact ssubst_var_cons_succ_wk e r _ _ p q

theorem scr_var {δ : REN} {Γ Δ : CTX.{i}} (Hδ : TYPED_REN δ Γ Δ) :
    ∀ {σ : SSUBST.{i}} {Γ' : CTX.{i}}, TSSUBST σ Γ' Γ →
    ∀ (p q Ψ τ), Δ[p]? = some Ψ → Ψ[q]? = some τ →
    ssubst_var (σ.scr δ) p q = ssubst_var σ (weaken_var' δ p q).1 (weaken_var' δ p q).2 := by
  induction Hδ with
  | id h => intro σ Γ' Hσ p q Ψ τ Hp Hq; rfl
  | @comp ρ1 Δm Ψ0 ρ2 Γ0 H1 H2 IH1 IH2 =>
    intro σ Γ' Hσ p q Ψ τ Hp Hq
    show ssubst_var ((σ.scr ρ2).scr ρ1) p q = _
    obtain ⟨Ψ', G1, G2⟩ := weaken_var'_correct ρ1 p q H1 Ψ τ Hp Hq
    rw [IH1 (TSSUBST.scr_typing H2 Hσ).some p q Ψ τ Hp Hq, IH2 Hσ _ _ Ψ' τ G1 G2]
    simp only [weaken_var']
  | @local_weaken ρ Ψ0 Γ0 Φ0 Δ0 t H IH =>
    intro σ Γ' Hσ p q Ψ τ Hp Hq
    show ssubst_var (σ.drop0.scr ρ) p q = _
    rw [IH (TSSUBST.drop0_typing Hσ) p q Ψ τ Hp Hq]
    obtain ⟨Ψ', G1, G2⟩ := weaken_var'_correct ρ p q H Ψ τ Hp Hq
    rw [ssubst_var_drop0 Hσ (weaken_var' ρ p q).1 (weaken_var' ρ p q).2 Ψ' τ G1 G2]
    simp only [weaken_var']
    rcases hw : weaken_var' ρ p q with ⟨n', m'⟩; cases n' <;> simp
  | @cons ρ Ψ0 Γ0 Φ0 Δ0 t H IH =>
    intro σ Γ' Hσ p q Ψ τ Hp Hq
    show ssubst_var ((σ.drop0.scr ρ).cons σ.tick0slot0) p q = _
    have Hd := TSSUBST.drop0_typing Hσ
    cases p with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at Hp; subst Hp
      cases q with
      | zero => rw [ssubst_var_cons_zero_zero]; simp only [weaken_var']; cases σ <;> rfl
      | succ q' =>
        rw [ssubst_var_cons_zero_succ]
        simp only [List.getElem?_cons_succ] at Hq
        rw [IH Hd 0 q' Φ0 τ (by simp) Hq]
        obtain ⟨Ψ', G1, G2⟩ := weaken_var'_correct ρ 0 q' H Φ0 τ (by simp) Hq
        rw [ssubst_var_drop0 Hσ (weaken_var' ρ 0 q').1 (weaken_var' ρ 0 q').2 Ψ' τ G1 G2]
        simp only [weaken_var']
        rcases hw : weaken_var' ρ 0 q' with ⟨n', m'⟩; cases n' <;> simp
    | succ p' =>
      simp only [List.getElem?_cons_succ] at Hp
      have hΔ0 : 0 < Δ0.length := by
        rcases List.getElem?_eq_some_iff.mp Hp with ⟨h, _⟩; omega
      rw [ssubst_var_cons_succ_typed (TSSUBST.scr_typing H Hd).some hΔ0]
      rw [IH Hd (p'+1) q Ψ τ Hp Hq]
      obtain ⟨Ψ', G1, G2⟩ := weaken_var'_correct ρ (p'+1) q H Ψ τ Hp Hq
      rw [ssubst_var_drop0 Hσ (weaken_var' ρ (p'+1) q).1 (weaken_var' ρ (p'+1) q).2 Ψ' τ G1 G2]
      simp only [weaken_var']
      rcases hw : weaken_var' ρ (p'+1) q with ⟨n', m'⟩; cases n' <;> simp
  | @global_lift ρ Γ0 Δ0 H IH =>
    intro σ Γ' Hσ p q Ψ τ Hp Hq
    cases Hσ with
    | single s Hs =>
      exfalso; have h1 := ren_len _ H; have h2 := typing_ren_len H
      simp only [List.length_nil, Nat.le_zero_eq, List.length_eq_zero_iff] at h2
      simp only [h2, List.length_nil] at h1; exact absurd h1 (by simp)
    | wk r Hr Hreq Hσs Hs =>
      cases p with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at Hp; subst Hp
        simp only [SSUBST.scr, ssubst_var, weaken_var']
      | succ p' =>
        simp only [List.getElem?_cons_succ] at Hp
        simp only [SSUBST.scr, ssubst_var]
        rw [IH Hσs p' q Ψ τ Hp Hq]
        simp only [weaken_var']
        rcases hw : weaken_var' ρ p' q with ⟨n', m'⟩; rfl
  | @global_shift σρ Γ0 Δ0 Ψ0 n hn H IH =>
    intro σ Γ' Hσ p q Ψ τ Hp Hq
    subst hn
    show ssubst_var (((cut_ssubst σ Ψ0.length).scr σρ).sr_compose
      (REN.global_shift (offset_ssubst σ Ψ0.length) REN.id)) p q = _
    have hΓ0 : 0 < Γ0.length := by have := ren_len _ H; have := typing_ren_len H; omega
    have hn' : Ψ0.length < (Ψ0 ++ Γ0).length := by rw [List.length_append]; omega
    have hcut := cut_ssubst_typing σ Hσ Ψ0.length hn'
    rw [List.drop_append, Nat.sub_self, List.drop_eq_nil_of_le (le_refl _), List.nil_append] at hcut
    obtain ⟨Ψ', G1, G2⟩ := weaken_var'_correct σρ p q H Ψ τ Hp Hq
    rw [← ssubst_var_sr ((cut_ssubst σ Ψ0.length).scr σρ) (Γ'.drop (offset_ssubst σ Ψ0.length)) Δ0
        ((TSSUBST.scr_typing H hcut).some)
        (REN.global_shift (offset_ssubst σ Ψ0.length) REN.id) p q Ψ τ Hp Hq]
    rw [IH hcut p q Ψ τ Hp Hq]
    simp only [weaken_var']
    rcases hw : weaken_var' σρ p q with ⟨n', m'⟩
    rw [hw] at G1 G2
    rw [ssubst_var_shift σ Γ' (Ψ0 ++ Γ0) Hσ Ψ0.length n' m' Ψ' τ hn' (by
        rw [List.getElem?_append_right (by omega)]
        simp only [Nat.add_sub_cancel_left]; exact G1) G2]

theorem offset_cons (e : EXPR.{i}) (σ : SSUBST.{i}) (n : Nat) :
    offset_ssubst (σ.cons e) n = offset_ssubst σ n := by
  cases σ <;> cases n <;> simp [SSUBST.cons, offset_ssubst]

theorem offset_drop0 (σ : SSUBST.{i}) (n : Nat) :
    offset_ssubst σ.drop0 n = offset_ssubst σ n := by
  cases σ <;> cases n <;> simp [SSUBST.drop0, offset_ssubst]

theorem cut_cons_succ_wk (e : EXPR.{i}) (r : Nat) (σs : SSUBST.{i}) (τ : SUBST.{i}) (k : Nat) :
    cut_ssubst ((SSUBST.wk r σs τ).cons e) (k+1) = cut_ssubst (SSUBST.wk r σs τ) (k+1) := by
  simp [SSUBST.cons, cut_ssubst]

theorem cut_drop0_succ_wk (r : Nat) (σs : SSUBST.{i}) (τ : SUBST.{i}) (k : Nat) :
    cut_ssubst (SSUBST.wk r σs τ).drop0 (k+1) = cut_ssubst (SSUBST.wk r σs τ) (k+1) := by
  simp [SSUBST.drop0, cut_ssubst]

theorem cut_cons_succ_typed {X : SSUBST.{i}} {Γ' : CTX.{i}} {Φ : OCTX.{i}} {Δ0 : CTX.{i}}
    {e : EXPR.{i}} (HX : TSSUBST X Γ' (Φ :: Δ0)) (hΔ : 0 < Δ0.length) (k : Nat) :
    cut_ssubst (X.cons e) (k+1) = cut_ssubst X (k+1) := by
  cases HX with
  | single s Hs => simp at hΔ
  | wk r Hr Hreq Hσs Hs => exact cut_cons_succ_wk e r _ _ k

theorem cut_drop0_succ_typed {X : SSUBST.{i}} {Γ' : CTX.{i}} {Φ : OCTX.{i}} {Δ0 : CTX.{i}}
    (HX : TSSUBST X Γ' (Φ :: Δ0)) (hΔ : 0 < Δ0.length) (k : Nat) :
    cut_ssubst X.drop0 (k+1) = cut_ssubst X (k+1) := by
  cases HX with
  | single s Hs => simp at hΔ
  | wk r Hr Hreq Hσs Hs => exact cut_drop0_succ_wk r _ _ k

theorem offset_scr {δ : REN} {Γ Δ : CTX.{i}} (Hδ : TYPED_REN δ Γ Δ) :
    ∀ {σ : SSUBST.{i}} {Γ' : CTX.{i}}, TSSUBST σ Γ' Γ →
    ∀ (n : Nat), n < Δ.length → offset_ssubst (σ.scr δ) n = offset_ssubst σ (offset_ren δ n) := by
  induction Hδ with
  | id h => intro σ Γ' Hσ n hn; simp [SSUBST.scr, off_id]
  | @comp ρ1 Δm Ψ0 ρ2 Γ0 H1 H2 IH1 IH2 =>
    intro σ Γ' Hσ n hn
    show offset_ssubst ((σ.scr ρ2).scr ρ1) n = offset_ssubst σ (offset_ren (REN.comp ρ1 ρ2) n)
    rw [IH1 (TSSUBST.scr_typing H2 Hσ).some n hn, offset_comp_all,
        IH2 Hσ (offset_ren ρ1 n) (offset_ren_len ρ1 H1 n hn)]
  | @local_weaken ρ Ψ0 Γ0 Φ0 Δ0 t H IH =>
    intro σ Γ' Hσ n hn
    show offset_ssubst (σ.drop0.scr ρ) n = offset_ssubst σ (offset_ren (REN.local_weaken ρ) n)
    rw [IH (TSSUBST.drop0_typing Hσ) n hn, offset_drop0]
    cases n with | zero => simp [offset_ren] | succ n' => simp only [off_lw_succ]
  | @cons ρ Ψ0 Γ0 Φ0 Δ0 t H IH =>
    intro σ Γ' Hσ n hn
    show offset_ssubst ((σ.drop0.scr ρ).cons σ.tick0slot0) n
       = offset_ssubst σ (offset_ren (REN.cons ρ) n)
    rw [offset_cons, IH (TSSUBST.drop0_typing Hσ) n hn, offset_drop0]
    cases n with | zero => simp [offset_ren] | succ n' => simp only [off_cons_succ]
  | @global_lift ρ Γ0 Δ0 H IH =>
    intro σ Γ' Hσ n hn
    cases Hσ with
    | single s Hs =>
      exfalso; have h1 := ren_len _ H; have h2 := typing_ren_len H
      simp only [List.length_nil, Nat.le_zero_eq, List.length_eq_zero_iff] at h2
      simp only [h2, List.length_nil] at h1; exact absurd h1 (by simp)
    | wk r Hr Hreq Hσs Hs =>
      cases n with
      | zero => simp
      | succ n' =>
        simp only [SSUBST.scr, offset_ssubst]
        rw [IH Hσs n' (by simp at hn ⊢; omega)]
        cases n' with
        | zero => simp [offset_ren, offset_ssubst]
        | succ n'' => simp only [offset_ren]; rfl
  | @global_shift σρ Γ0 Δ0 Ψ0 n0 hn0 H IH =>
    intro σ Γ' Hσ n hn
    subst hn0
    show offset_ssubst (((cut_ssubst σ Ψ0.length).scr σρ).sr_compose
      (REN.global_shift (offset_ssubst σ Ψ0.length) REN.id)) n = offset_ssubst σ (offset_ren _ n)
    have hΓ0 : 0 < Γ0.length := by have := ren_len _ H; have := typing_ren_len H; omega
    have hn' : Ψ0.length < (Ψ0 ++ Γ0).length := by rw [List.length_append]; omega
    have hcut := cut_ssubst_typing σ Hσ Ψ0.length hn'
    rw [List.drop_append, Nat.sub_self, List.drop_eq_nil_of_le (le_refl _), List.nil_append] at hcut
    have hsc := TSSUBST.scr_typing H hcut
    rw [offset_ssubst_sr _ _ _ hsc.some _ n hn, IH hcut n hn]
    cases n with
    | zero => simp [offset_ren]
    | succ n'' =>
      have hpos : 0 < offset_ssubst (cut_ssubst σ Ψ0.length) (offset_ren σρ (n''+1)) := by
        have := offset_succ_pos σρ n''
        obtain ⟨k, hk⟩ : ∃ k, offset_ren σρ (n''+1) = k+1 :=
          ⟨_, (Nat.succ_pred_eq_of_pos this).symm⟩
        rw [hk]; exact offset_ssubst_pos _ hcut _ (by omega)
      obtain ⟨j, hj⟩ : ∃ j, offset_ssubst (cut_ssubst σ Ψ0.length) (offset_ren σρ (n''+1)) = j+1 :=
        ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
      conv_lhs => rw [hj, off_global_shift_succ, off_id, ← hj]
      exact offset_cut_ss σ Ψ0.length (offset_ren σρ (n''+1))

theorem cut_scr {δ : REN} {Γ Δ : CTX.{i}} (Hδ : TYPED_REN δ Γ Δ) :
    ∀ {σ : SSUBST.{i}} {Γ' : CTX.{i}}, TSSUBST σ Γ' Γ →
    ∀ (n : Nat), n < Δ.length →
    cut_ssubst (σ.scr δ) n = (cut_ssubst σ (offset_ren δ n)).scr (cut_ren δ n) := by
  induction Hδ with
  | id h => intro σ Γ' Hσ n hn; simp [SSUBST.scr, off_id, cut_id]
  | @comp ρ1 Δm Ψ0 ρ2 Γ0 H1 H2 IH1 IH2 =>
    intro σ Γ' Hσ n hn
    show cut_ssubst ((σ.scr ρ2).scr ρ1) n
       = (cut_ssubst σ (offset_ren (REN.comp ρ1 ρ2) n)).scr (cut_ren (REN.comp ρ1 ρ2) n)
    rw [IH1 (TSSUBST.scr_typing H2 Hσ).some n hn, offset_comp_all, cut_comp_all,
        IH2 Hσ (offset_ren ρ1 n) (offset_ren_len ρ1 H1 n hn)]
    rfl
  | @local_weaken ρ Ψ0 Γ0 Φ0 Δ0 t H IH =>
    intro σ Γ' Hσ n hn
    show cut_ssubst (σ.drop0.scr ρ) n
       = (cut_ssubst σ (offset_ren (REN.local_weaken ρ) n)).scr (cut_ren (REN.local_weaken ρ) n)
    rw [IH (TSSUBST.drop0_typing Hσ) n hn]
    cases n with
    | zero => simp only [offset_ren, cut_ren, cut_ssubst_zero]; rfl
    | succ n' =>
      have hΓ0 : 0 < Γ0.length := by
        have := typing_ren_len H; simp only [List.length_cons] at hn this; omega
      have hpos : 0 < offset_ren ρ (n'+1) := offset_succ_pos ρ n'
      obtain ⟨k, hk⟩ : ∃ k, offset_ren ρ (n'+1) = k+1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
      rw [off_lw_succ, cut_lw_succ, hk, cut_drop0_succ_typed Hσ hΓ0]
  | @cons ρ Ψ0 Γ0 Φ0 Δ0 t H IH =>
    intro σ Γ' Hσ n hn
    show cut_ssubst ((σ.drop0.scr ρ).cons σ.tick0slot0) n
       = (cut_ssubst σ (offset_ren (REN.cons ρ) n)).scr (cut_ren (REN.cons ρ) n)
    cases n with
    | zero => simp only [cut_ssubst_zero, offset_ren, cut_ren]; rfl
    | succ n' =>
      have hΔ0 : 0 < Δ0.length := by simp only [List.length_cons] at hn; omega
      have hΓ0 : 0 < Γ0.length := by have := typing_ren_len H; simp only [List.length_cons] at this; omega
      rw [cut_cons_succ_typed (TSSUBST.scr_typing H (TSSUBST.drop0_typing Hσ)).some hΔ0,
          IH (TSSUBST.drop0_typing Hσ) (n'+1) hn]
      have hpos : 0 < offset_ren ρ (n'+1) := offset_succ_pos ρ n'
      obtain ⟨k, hk⟩ : ∃ k, offset_ren ρ (n'+1) = k+1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
      rw [off_cons_succ, cut_cons_succ, hk, cut_drop0_succ_typed Hσ hΓ0]
  | @global_lift ρ Γ0 Δ0 H IH =>
    intro σ Γ' Hσ n hn
    cases Hσ with
    | single s Hs =>
      exfalso; have h1 := ren_len _ H; have h2 := typing_ren_len H
      simp only [List.length_nil, Nat.le_zero_eq, List.length_eq_zero_iff] at h2
      simp only [h2, List.length_nil] at h1; exact absurd h1 (by simp)
    | wk r Hr Hreq Hσs Hs =>
      cases n with
      | zero => simp [cut_ren]
      | succ n' =>
        simp only [SSUBST.scr, cut_ssubst, offset_ren, cut_ren]
        rw [IH Hσs n' (by simp at hn ⊢; omega)]
  | @global_shift σρ Γ0 Δ0 Ψ0 n0 hn0 H IH =>
    intro σ Γ' Hσ n hn
    subst hn0
    have hΓ0 : 0 < Γ0.length := by have := ren_len _ H; have := typing_ren_len H; omega
    have hn' : Ψ0.length < (Ψ0 ++ Γ0).length := by rw [List.length_append]; omega
    have hcut := cut_ssubst_typing σ Hσ Ψ0.length hn'
    rw [List.drop_append, Nat.sub_self, List.drop_eq_nil_of_le (le_refl _), List.nil_append] at hcut
    have hsc := (TSSUBST.scr_typing H hcut).some
    show cut_ssubst (((cut_ssubst σ Ψ0.length).scr σρ).sr_compose
      (REN.global_shift (offset_ssubst σ Ψ0.length) REN.id)) n
      = (cut_ssubst σ (offset_ren (REN.global_shift Ψ0.length σρ) n)).scr
          (cut_ren (REN.global_shift Ψ0.length σρ) n)
    cases n with
    | zero => simp only [cut_ssubst_zero, offset_ren, cut_ren]; rfl
    | succ n' =>
      rw [cut_ssubst_sr _ _ _ hsc _ (n'+1) hn]
      have hpos : 0 < offset_ssubst ((cut_ssubst σ Ψ0.length).scr σρ) (n'+1) :=
        offset_ssubst_pos _ hsc (n'+1) (by omega)
      obtain ⟨k, hk⟩ : ∃ k, offset_ssubst ((cut_ssubst σ Ψ0.length).scr σρ) (n'+1) = k+1 :=
        ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
      rw [IH hcut (n'+1) hn, hk, cut_global_shift_succ, cut_id, ssubst_sr_id, cut_cut_ss,
          off_global_shift_succ, cut_global_shift_succ]

theorem subst_tail_sr (σ : SUBST.{i}) (δ : REN) : (σ.sr_compose δ).tail = σ.tail.sr_compose δ := by
  cases σ <;> rfl

theorem sr_drop0 (σ : SSUBST.{i}) (δ : REN) : (σ.sr_compose δ).drop0 = σ.drop0.sr_compose δ := by
  cases σ <;> simp [SSUBST.sr_compose, SSUBST.drop0, subst_tail_sr]

theorem sr_cons (e : EXPR.{i}) (σ : SSUBST.{i}) (δ : REN) :
    (σ.cons e).sr_compose δ = (σ.sr_compose δ).cons (weaken e δ) := by
  cases σ <;> simp [SSUBST.sr_compose, SSUBST.cons, SUBST.sr_compose]

theorem sr_tick0slot0_typed {σ : SSUBST.{i}} {Γ' : CTX.{i}} {t : TYPE.{i}} {Δ0 : OCTX.{i}}
    {Δs : CTX.{i}} (Hσ : TSSUBST σ Γ' ((t :: Δ0) :: Δs)) (δ : REN) :
    (σ.sr_compose δ).tick0slot0 = weaken σ.tick0slot0 δ := by
  cases Hσ with
  | single s Hs =>
    cases Hs with
    | cons He Hσ => simp [SSUBST.sr_compose, SSUBST.tick0slot0, SSUBST.head0, SUBST.sr_compose, subst_var]
  | wk n Hn Hneq Hσs Hs =>
    cases Hs with
    | cons He Hσ => simp [SSUBST.sr_compose, SSUBST.tick0slot0, SSUBST.head0, SUBST.sr_compose, subst_var]

theorem subst_sr_comp (σ : SUBST.{i}) (a b : REN) :
    (σ.sr_compose a).sr_compose b = σ.sr_compose (REN.comp a b) := by
  induction σ with
  | epsilon => rfl
  | cons e σ IH => simp only [SUBST.sr_compose, IH, weaken_comp]

theorem ssubst_sr_comp (σ : SSUBST.{i}) (a b : REN) :
    (σ.sr_compose a).sr_compose b = σ.sr_compose (REN.comp a b) := by
  induction σ generalizing a b with
  | single s => simp only [SSUBST.sr_compose, subst_sr_comp]
  | wk p σs s IH => simp only [SSUBST.sr_compose, subst_sr_comp, offset_comp_all, cut_comp_all, IH]

theorem subst_sr_congr (σ : SUBST.{i}) {a b : REN} (h : REN.equiv a b) :
    σ.sr_compose a = σ.sr_compose b := by
  induction σ with
  | epsilon => rfl
  | cons e σ IH => simp only [SUBST.sr_compose, IH, weaken_congr e h]

theorem ssubst_sr_congr (σ : SSUBST.{i}) {a b : REN} (h : REN.equiv a b) :
    σ.sr_compose a = σ.sr_compose b := by
  induction σ generalizing a b with
  | single s => simp only [SSUBST.sr_compose, subst_sr_congr s h]
  | wk p σs s IH => simp only [SSUBST.sr_compose, subst_sr_congr s h, h.offset p, IH (h.cut p)]

theorem scr_sr {δ : REN} {Γ Δ : CTX.{i}} (Hδ : TYPED_REN δ Γ Δ) :
    ∀ {σ : SSUBST.{i}} {Γ' : CTX.{i}}, TSSUBST σ Γ' Γ → ∀ (c : REN),
    (σ.sr_compose c).scr δ = (σ.scr δ).sr_compose c := by
  induction Hδ with
  | id h => intro σ Γ' Hσ c; rfl
  | @comp ρ1 Δm Ψ0 ρ2 Γ0 H1 H2 IH1 IH2 =>
    intro σ Γ' Hσ c
    show (((σ.sr_compose c).scr ρ2).scr ρ1) = ((σ.scr ρ2).scr ρ1).sr_compose c
    rw [IH2 Hσ, IH1 (TSSUBST.scr_typing H2 Hσ).some]
  | @local_weaken ρ Ψ0 Γ0 Φ0 Δ0 t H IH =>
    intro σ Γ' Hσ c
    show ((σ.sr_compose c).drop0.scr ρ) = (σ.drop0.scr ρ).sr_compose c
    rw [sr_drop0, IH (TSSUBST.drop0_typing Hσ)]
  | @cons ρ Ψ0 Γ0 Φ0 Δ0 t H IH =>
    intro σ Γ' Hσ c
    show (((σ.sr_compose c).drop0.scr ρ).cons (σ.sr_compose c).tick0slot0)
       = ((σ.drop0.scr ρ).cons σ.tick0slot0).sr_compose c
    rw [sr_drop0, IH (TSSUBST.drop0_typing Hσ), sr_cons, sr_tick0slot0_typed Hσ]
  | @global_lift ρ Γ0 Δ0 H IH =>
    intro σ Γ' Hσ c
    cases Hσ with
    | single s Hs =>
      exfalso; have h1 := ren_len _ H; have h2 := typing_ren_len H
      simp only [List.length_nil, Nat.le_zero_eq, List.length_eq_zero_iff] at h2
      simp only [h2, List.length_nil] at h1; exact absurd h1 (by simp)
    | @wk σs Γd Δs sh Ψ Δ00 r Hr Hreq Hσs Hs =>
      simp only [SSUBST.sr_compose, SSUBST.scr]
      rw [IH Hσs]
  | @global_shift σρ Γ0 Δ0 Ψ0 n0 hn0 H IH =>
    intro σ Γ' Hσ c
    subst hn0
    have hΓ0 : 0 < Γ0.length := by have := ren_len _ H; have := typing_ren_len H; omega
    have hn' : Ψ0.length < (Ψ0 ++ Γ0).length := by rw [List.length_append]; omega
    have hcut := cut_ssubst_typing σ Hσ Ψ0.length hn'
    rw [List.drop_append, Nat.sub_self, List.drop_eq_nil_of_le (le_refl _), List.nil_append] at hcut
    show (((cut_ssubst (σ.sr_compose c) Ψ0.length).scr σρ).sr_compose
            (REN.global_shift (offset_ssubst (σ.sr_compose c) Ψ0.length) REN.id))
       = ((((cut_ssubst σ Ψ0.length).scr σρ).sr_compose
            (REN.global_shift (offset_ssubst σ Ψ0.length) REN.id)).sr_compose c)
    rw [offset_ssubst_sr σ Γ' (Ψ0 ++ Γ0) Hσ c Ψ0.length hn',
        cut_ssubst_sr σ Γ' (Ψ0 ++ Γ0) Hσ c Ψ0.length hn']
    rw [IH hcut (cut_ren c (offset_ssubst σ Ψ0.length))]
    rw [ssubst_sr_comp, ssubst_sr_comp]
    exact ssubst_sr_congr _ (asm_nat (offset_ssubst σ Ψ0.length) c).symm

theorem ssubst_cons_shape {σ : SSUBST.{i}} {Γ' Γ : CTX.{i}} (Hσ : TSSUBST σ Γ' Γ) :
    ∃ Δ0 Δs, Γ = Δ0 :: Δs := by
  cases Hσ with
  | single s Hs => exact ⟨_, [], rfl⟩
  | wk n Hn Hneq Hσs Hs => exact ⟨_, _, rfl⟩

theorem ext'_drop0 {σ : SSUBST.{i}} {Γ' : CTX.{i}} {Δ : OCTX.{i}} {Δs : CTX.{i}}
    (Hσ : TSSUBST σ Γ' (Δ :: Δs)) : σ.ext'.drop0 = σ.drop := by
  cases Hσ with
  | single s Hs => rfl
  | @wk σs Γd Δs2 sh Ψ Δ0 n Hn Hneq Hσs Hs =>
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    show SSUBST.drop0 (SSUBST.wk _ _ _) = SSUBST.drop (SSUBST.wk _ _ _)
    simp only [SSUBST.drop0, SSUBST.drop, SSUBST.sr_compose]
    rw [show offset_ren (REN.local_weaken REN.id) (n'+1) = n'+1 from rfl,
        show cut_ren (REN.local_weaken REN.id) (n'+1) = REN.id from rfl, ssubst_sr_id]
    rfl

theorem ext'_tick0slot0 (σ : SSUBST.{i}) : σ.ext'.tick0slot0 = EXPR.var' 0 0 := by
  cases σ <;> rfl

theorem ext'_eq_cons_drop {σ : SSUBST.{i}} {Γ' : CTX.{i}} {Δ : OCTX.{i}} {Δs : CTX.{i}}
    (Hσ : TSSUBST σ Γ' (Δ :: Δs)) : σ.ext' = σ.drop.cons (EXPR.var' 0 0) := by
  cases Hσ with
  | single s Hs => rfl
  | @wk σs Γd Δs2 sh Ψ Δ0 n Hn Hneq Hσs Hs =>
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    show SSUBST.ext' (SSUBST.wk _ _ _) = SSUBST.cons (SSUBST.drop (SSUBST.wk _ _ _)) _
    simp only [SSUBST.cons, SSUBST.drop, SSUBST.sr_compose]
    rw [show offset_ren (REN.local_weaken REN.id) (n'+1) = n'+1 from rfl,
        show cut_ren (REN.local_weaken REN.id) (n'+1) = REN.id from rfl, ssubst_sr_id]
    rfl

theorem scr_ext {δ : REN} {Γ Δ : CTX.{i}} (Hδ : TYPED_REN δ Γ Δ)
    {σ : SSUBST.{i}} {Γ' : CTX.{i}} (Hσ : TSSUBST σ Γ' Γ) :
    σ.ext'.scr (δ.cons) = (σ.scr δ).ext' := by
  obtain ⟨Δ0, Δs, rfl⟩ := ssubst_cons_shape Hσ
  have Hscr := (TSSUBST.scr_typing Hδ Hσ).some
  obtain ⟨E0, Es, hE⟩ := ssubst_cons_shape Hscr
  show (σ.ext'.drop0.scr δ).cons σ.ext'.tick0slot0 = (σ.scr δ).ext'
  rw [ext'_drop0 Hσ, ext'_tick0slot0]
  rw [ext'_eq_cons_drop (Δ := E0) (Δs := Es) (by rw [← hE]; exact Hscr)]
  simp only [SSUBST.drop]
  rw [scr_sr Hδ Hσ]

theorem binds_weaken {Γ : CTX.{i}} {e : EXPR.{i}} {τ : TYPE.{i}} (H : TYPED Γ e τ) :
    ∀ {Δ' : CTX.{i}} {δ : REN} (_Hδ : TYPED_REN δ Δ' Γ) {σ : SSUBST.{i}} {Ψ : CTX.{i}}
      (_Hσ : TSSUBST σ Ψ Δ'), binds σ (weaken e δ) = binds (σ.scr δ) e := by
  induction H with
  | embed h => intro Δ' δ Hδ σ Ψ Hσ; rfl
  | embed_apply Hf Hx IHf IHx =>
    intro Δ' δ Hδ σ Ψ Hσ; simp only [weaken, embed_apply_subst]; rw [IHf Hδ Hσ, IHx Hδ Hσ]
  | pure h IH => intro Δ' δ Hδ σ Ψ Hσ; simp only [weaken, pure_subst]; rw [IH Hδ Hσ]
  | @var' Γ Δ τ p q Hp Hq =>
    intro Δ' δ Hδ σ Ψ Hσ
    show ssubst_var σ (weaken_var' δ p q).1 (weaken_var' δ p q).2 = ssubst_var (σ.scr δ) p q
    rw [scr_var Hδ Hσ p q Δ τ Hp Hq]
  | app Hf Hx IHf IHx =>
    intro Δ' δ Hδ σ Ψ Hσ; simp only [weaken, app_subst]; rw [IHf Hδ Hσ, IHx Hδ Hσ]
  | @lam' Γ Δ A B e He IH =>
    intro Δ' δ Hδ σ Ψ Hσ
    simp only [weaken, binds]; obtain ⟨Δ'0, Δ's, rfl⟩ := ssubst_cons_shape Hσ
    congr 1; rw [IH (TYPED_REN.cons A Hδ) (TSSUBST.ext_typing_auto Hσ), scr_ext Hδ Hσ]
  | @delay Γ e A h He IH =>
    intro Δ' δ Hδ σ Ψ Hσ
    simp only [weaken, delay_subst]
    show EXPR.delay (binds (SSUBST.wk 1 σ SUBST.epsilon) (weaken e δ.global_lift))
       = EXPR.delay (binds (SSUBST.wk 1 (σ.scr δ) SUBST.epsilon) e)
    rw [IH (TYPED_REN.global_lift Hδ)
        (TSSUBST.wk 1 (Ψ := [[]]) (by simp) (by simp)
          (ssubst_transport_right (by simp) Hσ) (TSUBST.epsilon (by simp)))]
    rfl
  | @adv n Γ e A hn He IH =>
    intro Δ' δ Hδ σ Ψ Hσ
    simp only [weaken, adv_subst]
    have hnlen : n < Γ.length := by
      have := typing_stack_len He; simp only [List.length_drop] at this; omega
    rw [offset_scr Hδ Hσ n hnlen, cut_scr Hδ Hσ n hnlen]
    congr 1
    rw [IH (cut_ren_typing δ Hδ n hnlen)
        (cut_ssubst_typing σ Hσ (offset_ren δ n) (offset_ren_len δ Hδ n hnlen))]
  | @fix' Γ Δ e A He IH =>
    intro Δ' δ Hδ σ Ψ Hσ
    simp only [weaken, binds]; obtain ⟨Δ'0, Δ's, rfl⟩ := ssubst_cons_shape Hσ
    congr 1; rw [IH (TYPED_REN.cons _ Hδ) (TSSUBST.ext_typing_auto Hσ), scr_ext Hδ Hσ]
  | pair He He' IH IH' =>
    intro Δ' δ Hδ σ Ψ Hσ; simp only [weaken, pair_subst]; rw [IH Hδ Hσ, IH' Hδ Hσ]
  | projL He IH => intro Δ' δ Hδ σ Ψ Hσ; simp only [weaken, proj_subst]; rw [IH Hδ Hσ]
  | projR He IH => intro Δ' δ Hδ σ Ψ Hσ; simp only [weaken, proj_subst]; rw [IH Hδ Hσ]
  | inl He IH => intro Δ' δ Hδ σ Ψ Hσ; simp only [weaken, inl_subst]; rw [IH Hδ Hσ]
  | inr He IH => intro Δ' δ Hδ σ Ψ Hσ; simp only [weaken, inr_subst]; rw [IH Hδ Hσ]
  | case He Hf Hg IHe IHf IHg => intro Δ' δ Hδ σ Ψ Hσ; simp only [weaken, case_subst]; rw [IHe Hδ Hσ, IHf Hδ Hσ, IHg Hδ Hσ]
  | or He He' IH IH' =>
    intro Δ' δ Hδ σ Ψ Hσ; simp only [weaken, or_subst]; rw [IH Hδ Hσ, IH' Hδ Hσ]
  | and He He' IH IH' =>
    intro Δ' δ Hδ σ Ψ Hσ; simp only [weaken, and_subst]; rw [IH Hδ Hσ, IH' Hδ Hσ]
  | impl He He' IH IH' =>
    intro Δ' δ Hδ σ Ψ Hσ; simp only [weaken, impl_subst]; rw [IH Hδ Hσ, IH' Hδ Hσ]
  | @forall' Γ Δ A e He IH =>
    intro Δ' δ Hδ σ Ψ Hσ
    simp only [weaken, binds]; obtain ⟨Δ'0, Δ's, rfl⟩ := ssubst_cons_shape Hσ
    congr 1; rw [IH (TYPED_REN.cons _ Hδ) (TSSUBST.ext_typing_auto Hσ), scr_ext Hδ Hσ]
  | @exists' Γ Δ A e He IH =>
    intro Δ' δ Hδ σ Ψ Hσ
    simp only [weaken, binds]; obtain ⟨Δ'0, Δ's, rfl⟩ := ssubst_cons_shape Hσ
    congr 1; rw [IH (TYPED_REN.cons _ Hδ) (TSSUBST.ext_typing_auto Hσ), scr_ext Hδ Hσ]
  | lift He IH => intro Δ' δ Hδ σ Ψ Hσ; simp only [weaken, lift_subst]; rw [IH Hδ Hσ]
  | true h => intro Δ' δ Hδ σ Ψ Hσ; rfl
  | false h => intro Δ' δ Hδ σ Ψ Hσ; rfl
  | eq He He' IH IH' =>
    intro Δ' δ Hδ σ Ψ Hσ; simp only [weaken, eq_subst]; rw [IH Hδ Hσ, IH' Hδ Hσ]
  | ax t f h => intro Δ' δ Hδ σ Ψ Hσ; rfl

theorem comp_lw_id_equiv (ρ : REN) :
    REN.equiv (REN.comp ρ (REN.local_weaken REN.id)) (REN.local_weaken ρ) := by
  refine ⟨fun n m => ?_, fun n => ?_⟩
  · simp only [weaken_var']
  · simp only [offset_comp_all]
    cases n with
    | zero => simp [offset_ren]
    | succ n' =>
      obtain ⟨j, hj⟩ : ∃ j, offset_ren ρ (n' + 1) = j + 1 :=
        ⟨_, (Nat.succ_pred_eq_of_pos (offset_succ_pos ρ n')).symm⟩
      rw [hj, off_lw_succ, off_id, off_lw_succ, hj]

theorem comp_global_shift_id_equiv (n : Nat) (σρ : REN) :
    REN.equiv (REN.comp σρ (REN.global_shift n REN.id)) (REN.global_shift n σρ) := by
  refine ⟨fun a b => ?_, fun a => ?_⟩
  · simp only [weaken_var']
  · simp only [offset_comp_all]
    cases a with
    | zero => simp [offset_ren]
    | succ a' =>
      obtain ⟨j, hj⟩ : ∃ j, offset_ren σρ (a' + 1) = j + 1 :=
        ⟨_, (Nat.succ_pred_eq_of_pos (offset_succ_pos σρ a')).symm⟩
      rw [hj, off_global_shift_succ, off_id, off_global_shift_succ, hj]

theorem id_scr_eq_subst_of_ren {δ : REN} {Γ Δ : CTX.{i}} (Hδ : TYPED_REN δ Δ Γ) :
    (SSUBST.id.{i} (Δ.map List.length)).scr δ = δ.subst_of_ren (Γ.map List.length) := by
  have key : ∀ {Γ' Δ' : CTX.{i}} {ρ : REN}, TYPED_REN ρ Δ' Γ' →
      (SSUBST.id.{i} (Δ'.map List.length)).scr ρ = (SSUBST.id.{i} (Γ'.map List.length)).sr_compose ρ := by
    intro Γ' Δ' ρ Hρ
    induction Hρ with
    | id h => simp only [SSUBST.scr, ssubst_sr_id]
    | @comp ρ1 Δm Ψ0 ρ2 Γ0 H1 H2 IH1 IH2 =>
      show ((SSUBST.id (Γ0.map List.length)).scr ρ2).scr ρ1 = _
      rw [IH2]
      refine (scr_sr H1 (TSSUBST.id Δm (by simpa using ren_len _ H2)) ρ2).trans ?_
      simp only [IH1, ssubst_sr_comp]
    | @local_weaken ρ Ψ0 Γ0 Φ0 Δ0 t H IH =>
      show (SSUBST.id (((t :: Ψ0) :: Γ0).map List.length)).drop0.scr ρ = _
      rw [id_cons_ext, ext'_drop0 (TSSUBST.id ((Ψ0 :: Γ0)) (by simp)), SSUBST.drop]
      refine (scr_sr H (TSSUBST.id (Ψ0 :: Γ0) (by simp)) (REN.local_weaken REN.id)).trans ?_
      simp only [IH, ssubst_sr_comp]
      exact ssubst_sr_congr _ (comp_lw_id_equiv ρ)
    | @cons ρ Ψ0 Γ0 Φ0 Δ0 t H IH =>
      show (SSUBST.id (((t :: Ψ0) :: Γ0).map List.length)).scr (ρ.cons) = _
      rw [id_cons_ext]
      refine (scr_ext H (TSSUBST.id (Ψ0 :: Γ0) (by simp))).trans ?_
      conv_rhs => rw [id_cons_ext, ssubst_ext_sr _ _ _ (TSSUBST.id (Φ0 :: Δ0) (by simp))]
      rw [IH]
    | @global_lift ρ Γ0 Δ0 H IH =>
      obtain ⟨g0, gs, rfl⟩ : ∃ g0 gs, Γ0 = g0 :: gs := by
        cases Γ0 with | nil => exact absurd (ren_len' _ H) (by simp) | cons a b => exact ⟨a, b, rfl⟩
      obtain ⟨d0, ds, rfl⟩ : ∃ d0 ds, Δ0 = d0 :: ds := by
        cases Δ0 with | nil => exact absurd (ren_len _ H) (by simp) | cons a b => exact ⟨a, b, rfl⟩
      show (SSUBST.id (([] :: g0 :: gs).map List.length)).scr (ρ.global_lift) = _
      rw [List.map_cons, List.map_cons, List.length_nil]
      show SSUBST.wk 1 ((SSUBST.id ((g0 :: gs).map List.length)).scr ρ) SUBST.epsilon = _
      rw [IH]
      show _ = (SSUBST.wk 1 (SSUBST.id ((d0 :: ds).map List.length)) SUBST.epsilon).sr_compose
        ρ.global_lift
      rw [wk1_sr]
    | @global_shift σρ Γ0 Δ0 Ψ0 n hn H IH =>
      subst hn
      have hΓ0 : 0 < Γ0.length := by have := ren_len _ H; have := typing_ren_len H; omega
      have hΨΓ : 0 < (Ψ0 ++ Γ0).length := by rw [List.length_append]; omega
      have hn' : Ψ0.length < (Ψ0 ++ Γ0).length := by rw [List.length_append]; omega
      have hcut := cut_ssubst_id (Ψ0 ++ Γ0) Ψ0.length hn'
      rw [List.drop_append, Nat.sub_self, List.drop_eq_nil_of_le (le_refl _),
          List.nil_append] at hcut
      have hoff := offset_ssubst_id (Ψ0 ++ Γ0) Ψ0.length hn'
      show (((cut_ssubst (SSUBST.id ((Ψ0 ++ Γ0).map List.length)) Ψ0.length).scr σρ).sr_compose
              (REN.global_shift (offset_ssubst (SSUBST.id ((Ψ0 ++ Γ0).map List.length))
                Ψ0.length) REN.id)) = _
      rw [hcut, List.drop_zero, hoff, IH, ssubst_sr_comp]
      exact ssubst_sr_congr _ (comp_global_shift_id_equiv Ψ0.length σρ)
  rw [key Hδ, REN.subst_of_ren]

theorem drop0_cons (e : EXPR.{i}) (σ : SSUBST.{i}) : (σ.cons e).drop0 = σ := by
  cases σ <;> rfl

theorem tick0slot0_cons (e : EXPR.{i}) (σ : SSUBST.{i}) : (σ.cons e).tick0slot0 = e := by
  cases σ <;> rfl

theorem weaken_single_subst {τ στ : TYPE.{i}} {Γ0 Δ0 : OCTX.{i}} {Γs Δs : CTX.{i}}
    {e a : EXPR.{i}} {δ : REN}
    (He : TYPED ((τ :: Γ0) :: Γs) e στ) (Ha : TYPED (Γ0 :: Γs) a τ)
    (Hδ : TYPED_REN δ (Δ0 :: Δs) (Γ0 :: Γs)) :
    weaken (binds (single_subst (List.map List.length (Γ0 :: Γs)) a) e) δ
      = binds (single_subst (List.map List.length (Δ0 :: Δs)) (weaken a δ)) (weaken e δ.cons) := by
  have Hσ1 : TSSUBST (single_subst (List.map List.length (Γ0 :: Γs)) a) (Γ0 :: Γs)
      ((τ :: Γ0) :: Γs) := TSSUBST.single_subst Ha
  have Hδc : TYPED_REN δ.cons ((τ :: Δ0) :: Δs) ((τ :: Γ0) :: Γs) := TYPED_REN.cons τ Hδ
  have Hσ2 : TSSUBST (single_subst (List.map List.length (Δ0 :: Δs)) (weaken a δ)) (Δ0 :: Δs)
      ((τ :: Δ0) :: Δs) := TSSUBST.single_subst (weaken_typing Ha Hδ)
  rw [weaken_binds He Hσ1 δ, binds_weaken He Hδc Hσ2]
  congr 1

  show ((SSUBST.id (List.map List.length (Γ0 :: Γs))).cons a).sr_compose δ
     = ((SSUBST.id (List.map List.length (Δ0 :: Δs))).cons (weaken a δ)).scr δ.cons
  rw [sr_cons]
  show ((SSUBST.id (List.map List.length (Γ0 :: Γs))).sr_compose δ).cons (weaken a δ) = _
  rw [show ((SSUBST.id (List.map List.length (Δ0 :: Δs))).cons (weaken a δ)).scr δ.cons
        = (((SSUBST.id (List.map List.length (Δ0 :: Δs))).cons (weaken a δ)).drop0.scr δ).cons
            ((SSUBST.id (List.map List.length (Δ0 :: Δs))).cons (weaken a δ)).tick0slot0 from rfl]
  rw [drop0_cons, tick0slot0_cons, id_scr_eq_subst_of_ren Hδ, REN.subst_of_ren]

end prf
