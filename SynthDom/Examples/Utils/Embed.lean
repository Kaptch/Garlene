module

public import SynthDom
@[expose] public section

open CategoryTheory Logic

noncomputable section
namespace embed_sem

universe i

private lemma pure_embed_some {Γ : CTX.{i}} {A : Type} (φ : A → Prop) {e : EXPR.{i}}
    (hd : (expr_interp Γ e (TYPE.embed A)).Dom) :
    expr_interp Γ (EXPR.embed_apply A Prop (EXPR.embed (A → Prop) φ) e).pure TYPE.prop
      = Part.some (interp_pure (interp_embed_apply A Prop (interp_embed (A → Prop) φ)
          ((expr_interp Γ e (TYPE.embed A)).get hd))) := by
  simp only [expr_interp, Part.assert_pos, bind, Part.Dom.bind hd, Part.pure_eq_some,
    Part.bind_some, cast_eq]

theorem get_of_some {α} {o : Part α} {a : α} (h : o.Dom) (he : o = Part.some a) :
    o.get h = a := by simp only [he, Part.get_some]

theorem and_some {Γ : CTX.{i}} {e1 e2 : EXPR.{i}}
    (h1 : (expr_interp Γ e1 TYPE.prop).Dom) (h2 : (expr_interp Γ e2 TYPE.prop).Dom) :
    expr_interp Γ (e1.and e2) TYPE.prop
      = Part.some (interp_and ((expr_interp Γ e1 TYPE.prop).get h1)
          ((expr_interp Γ e2 TYPE.prop).get h2)) := by
  simp only [expr_interp, bind, Part.Dom.bind h1, Part.Dom.bind h2]
  rfl

private lemma and_pure_extend {Γ : CTX.{i}} (X Y Z : ⟦Γ⟧ₛ ⟶ ⟦TYPE.embed Prop⟧ₜ)
    (h : ∀ (n : (ℕ)ᵒᵖ) (γ : ⟦Γ⟧ₛ.obj n), ((ConcreteCategory.hom (X.app n)) γ).down →
      ((ConcreteCategory.hom (Y.app n)) γ).down → ((ConcreteCategory.hom (Z.app n)) γ).down) :
    interp_and (interp_pure X) (interp_pure Y)
      = interp_and (interp_and (interp_pure X) (interp_pure Y)) (interp_pure Z) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro γ
  apply ULift.ext
  apply Sieve.ext
  intro m f
  simp only [interp_pure, interp_and, Logic.pure, Logic.pureI, NatTrans.comp_app,
    ConcreteCategory.comp_apply, ConcreteCategory.hom_ofHom]
  exact ⟨fun hh => ⟨hh, h _ _ hh.1 hh.2⟩, fun hh => hh.1⟩

private lemma pure_embed_prop_some {Γ : CTX.{i}} (P : Prop) :
    expr_interp Γ ⟪⌜δ(P)⌝⟫ TYPE.prop = Part.some (interp_pure (interp_embed Prop P)) := by
  simp only [expr_interp, Part.assert_pos, bind, Part.pure_eq_some, Part.bind_some, cast_eq]

theorem pure_imp2_eq {Γ : CTX.{i}} (P Q R : Prop) (h : P → Q → R) (hlen : 0 < Γ.length) :
    EQ Γ TYPE.prop ⟪(⌜δ(P)⌝) ∧ (⌜δ(Q)⌝)⟫ ⟪((⌜δ(P)⌝) ∧ (⌜δ(Q)⌝)) ∧ (⌜δ(R)⌝)⟫ := by
  have TP : TYPED Γ ⟪⌜δ(P)⌝⟫ TYPE.prop := TYPED.pure (TYPED.embed hlen)
  have TQ : TYPED Γ ⟪⌜δ(Q)⌝⟫ TYPE.prop := TYPED.pure (TYPED.embed hlen)
  have TR : TYPED Γ ⟪⌜δ(R)⌝⟫ TYPE.prop := TYPED.pure (TYPED.embed hlen)
  have hp := expr_interp_correct TP
  have hq := expr_interp_correct TQ
  have hr := expr_interp_correct TR
  have hdl := expr_interp_correct (TYPED.and TP TQ)
  refine EQ.ax (TYPED.and TP TQ) (TYPED.and (TYPED.and TP TQ) TR) ?_
  rw [and_some hp hq, and_some hdl hr, get_of_some hdl (and_some hp hq),
    get_of_some hp (pure_embed_prop_some P), get_of_some hq (pure_embed_prop_some Q),
    get_of_some hr (pure_embed_prop_some R)]
  exact congrArg Part.some (and_pure_extend _ _ _ fun _ _ => h)

theorem pure_close₂_eq {Γ : CTX.{i}} {A : Type} (φ ψ : A → Prop) (R : Prop)
    (h : ∀ a, φ a → ψ a → R) (ex : EXPR.{i}) (Hx : TYPED Γ ex (TYPE.embed A)) :
    EQ Γ TYPE.prop
      (EXPR.and (EXPR.pure (EXPR.embed_apply A Prop (EXPR.embed (A → Prop) φ) ex))
        (EXPR.pure (EXPR.embed_apply A Prop (EXPR.embed (A → Prop) ψ) ex)))
      (EXPR.and
        (EXPR.and (EXPR.pure (EXPR.embed_apply A Prop (EXPR.embed (A → Prop) φ) ex))
          (EXPR.pure (EXPR.embed_apply A Prop (EXPR.embed (A → Prop) ψ) ex)))
        ⟪⌜δ(R)⌝⟫) := by
  have hlen : 0 < Γ.length := typing_stack_len Hx
  have hx : (expr_interp Γ ex (TYPE.embed A)).Dom := expr_interp_correct Hx
  have Tφ := TYPED.pure (TYPED.embed_apply (TYPED.embed hlen (a := φ)) Hx)
  have Tψ := TYPED.pure (TYPED.embed_apply (TYPED.embed hlen (a := ψ)) Hx)
  have TR : TYPED Γ ⟪⌜δ(R)⌝⟫ TYPE.prop := TYPED.pure (TYPED.embed hlen)
  have hdφ := expr_interp_correct Tφ
  have hdψ := expr_interp_correct Tψ
  have hdR := expr_interp_correct TR
  have hdl := expr_interp_correct (TYPED.and Tφ Tψ)
  refine EQ.ax (TYPED.and Tφ Tψ) (TYPED.and (TYPED.and Tφ Tψ) TR) ?_
  rw [and_some hdφ hdψ, and_some hdl hdR, get_of_some hdl (and_some hdφ hdψ),
    get_of_some hdφ (pure_embed_some φ hx), get_of_some hdψ (pure_embed_some ψ hx),
    get_of_some hdR (pure_embed_prop_some R)]
  exact congrArg Part.some (and_pure_extend _ _ _ fun _ _ => h _)

theorem pure_close₂_all (A : Type) (φ ψ : A → Prop) (R : Prop) (h : ∀ a, φ a → ψ a → R) :
    ⊢ᵍ ⟪∀ x : (Δ A). ((⌜δ(φ) ⊙ x⌝) → ((⌜δ(ψ) ⊙ x⌝) → (⌜δ(R)⌝)))⟫ := by
  refine GOAL_forall_intro `x ?_
  refine GOAL_impl_intro `H1
    (TYPED.pure (TYPED.embed_apply (TYPED.embed (by simp))
      (TYPED.var_explicit (Γ := [[TYPE.embed A]]) (nm := `x) (0 : Fin 1) (0 : Fin 1)))) ?_
  refine GOAL_impl_intro `H2
    (TYPED.pure (TYPED.embed_apply (TYPED.embed (by simp))
      (TYPED.var_explicit (Γ := [[TYPE.embed A]]) (nm := `x) (0 : Fin 1) (0 : Fin 1)))) ?_
  refine GOAL_and_elim_r (GOAL_simplify_prop
    (pure_close₂_eq φ ψ R h (EXPR.var `x 0 0)
      (TYPED.var_explicit (Γ := [[TYPE.embed A]]) (nm := `x) (0 : Fin 1) (0 : Fin 1))) ?_)
  gsplit
  · gassumption
  · gassumption

theorem pure_imp2 (P Q R : Prop) (h : P → Q → R) :
    ⊢ᵍ ⟪(⌜δ(P)⌝) → ((⌜δ(Q)⌝) → (⌜δ(R)⌝))⟫ := by
  refine GOAL_impl_intro `hP (TYPED.pure (TYPED.embed (by simp))) ?_
  refine GOAL_impl_intro `hQ (TYPED.pure (TYPED.embed (by simp))) ?_
  refine GOAL_and_elim_r (GOAL_simplify_prop (pure_imp2_eq P Q R h (by simp)) ?_)
  gsplit
  · gassumption
  · gassumption

theorem pure_imp1 (P Q : Prop) (h : P → Q) :
    ⊢ᵍ ⟪(⌜δ(P)⌝) → (⌜δ(Q)⌝)⟫ := by
  refine GOAL_impl_intro `hP (TYPED.pure (TYPED.embed (by simp))) ?_
  gapply (pure_imp2 P True Q (fun hp _ => h hp))
  · gassumption
  · gembed
    trivial

end embed_sem
end

end
