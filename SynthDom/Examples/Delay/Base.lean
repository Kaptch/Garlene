module

public import SynthDom
public import SynthDom.Examples.Utils.Funext
@[expose] public section

section guarded_delay
open CategoryTheory

gtype Delay (A : TYPE) := ν X. [A] ⊕ ▸X

gdef Delay.ret (A : TYPE) : A → [Delay A] :=
  λ a. [Delay.MK A]ₛ (inl a)

gdef Delay.step (A : TYPE) : ▸ [Delay A] → [Delay A] :=
  λ w. [Delay.MK A]ₛ (inr w)

gdef Delay.map (A B : TYPE) : (A → B) → [Delay A] → [Delay B] :=
  fix μ. λ f. λ d.
    [Delay.MK B]ₛ (case ([Delay.PROJ A]ₛ d)
      (λ a. inl (f a))
      (λ w. inr (delay (((adv 1 μ) f) (adv 1 w)))))

gdef Delay.bind (A B : TYPE) : (A → [Delay B]) → [Delay A] → [Delay B] :=
  fix μ. λ k. λ d.
    case ([Delay.PROJ A]ₛ d)
      k
      (λ w. [Delay.MK B]ₛ (inr (delay (((adv 1 μ) k) (adv 1 w)))))

gtheorem Delay.delay_eta (A : TYPE) :
    ∀ t : ▸ [Delay A]. (delay (adv 1 t) = t) := by
    gintro t
    exact ⟨PROVES.eq_def
      (EQ.sym' (EQ.eta_delay (TYPED.var_explicit (Γ := [[⦃▸[Delay A]⦄]]) (nm := `t)
        (0 : Fin 1) (0 : Fin 1))))⟩

section destructor_equations

gtheorem Delay.map_ret (A B : TYPE) :
    ∀ f : (A → B). ∀ a : A.
      (([Delay.map A B]ₛ f) ([Delay.MK A]ₛ (inl a)) = [Delay.MK B]ₛ (inl (f a))) := by
    gintro f a
    gunfold Delay.map
    gfix
    grewrite (Delay.PROJ_MK A)
    gsimpl
    grfl

gtheorem Delay.map_step (A B : TYPE) :
    ∀ f : (A → B). ∀ w : ▸ [Delay A].
      (([Delay.map A B]ₛ f) ([Delay.MK A]ₛ (inr w))
        = [Delay.MK B]ₛ (inr (delay (([Delay.map A B]ₛ f) (adv 1 w))))) := by
    gintro f w
    gunfold Delay.map
    gfix
    grewrite (Delay.PROJ_MK A)
    gsimpl
    grfl

gtheorem Delay.bind_ret (A B : TYPE) :
    ∀ k : (A → [Delay B]). ∀ a : A.
      (([Delay.bind A B]ₛ k) ([Delay.MK A]ₛ (inl a)) = k a) := by
    gintro k a
    gunfold Delay.bind
    gfix
    grewrite (Delay.PROJ_MK A)
    gsimpl
    grfl

gtheorem Delay.bind_step (A B : TYPE) :
    ∀ k : (A → [Delay B]). ∀ w : ▸ [Delay A].
      (([Delay.bind A B]ₛ k) ([Delay.MK A]ₛ (inr w))
        = [Delay.MK B]ₛ (inr (delay (([Delay.bind A B]ₛ k) (adv 1 w))))) := by
    gintro k w
    gunfold Delay.bind
    gfix
    grewrite (Delay.PROJ_MK A)
    gsimpl
    grfl

end destructor_equations

gtheorem Delay.map_id (A : TYPE) :
    ∀ d : [Delay A]. (([Delay.map A A]ₛ (λ x : A. x)) d = d) := by
    glöb IH
    gintro d
    gunfold Delay.map
    gfix
    gcases ([Delay.PROJ A]ₛ d) with (⟨v, h⟩ | ⟨v, h⟩)
    · grewrite h
      gsimpl
      grewrite ← h
      gapply (Delay.MK_PROJ A)
    · grewrite h
      gsimpl
      gassert Htlf of ((delay _) = delay (adv 1 v))
      · gmono IH as G
        gapply G
      grewrite Htlf
      grewrite (Delay.delay_eta A) v
      grewrite ← h
      gapply (Delay.MK_PROJ A)

gtheorem Delay.bind_ret_l (A B : TYPE) :
    ∀ k : (A → [Delay B]). ∀ a : A.
      (([Delay.bind A B]ₛ k) ([Delay.ret A]ₛ a) = k a) := by
    gintro k a
    gunfold Delay.bind
    gfix
    gunfold Delay.ret
    gsimpl
    grewrite (Delay.PROJ_MK A)
    gsimpl
    grfl

gtheorem Delay.bind_ret_r (A : TYPE) :
    ∀ d : [Delay A]. (([Delay.bind A A]ₛ (λ x : A. [Delay.MK A]ₛ (inl x))) d = d) := by
    glöb IH
    gintro d
    gunfold Delay.bind
    gfix
    gcases ([Delay.PROJ A]ₛ d) with (⟨v, h⟩ | ⟨v, h⟩)
    · grewrite h
      gsimpl
      grewrite ← h
      gapply (Delay.MK_PROJ A)
    · grewrite h
      gsimpl
      gassert Htlf of ((delay _) = delay (adv 1 v))
      · gmono IH as G
        gapply G
      grewrite Htlf
      grewrite (Delay.delay_eta A) v
      grewrite ← h
      gapply (Delay.MK_PROJ A)

section composition_laws

gtheorem Delay.map_comp (A B C : TYPE) :
    ∀ f : (A → B). ∀ g : (B → C). ∀ d : [Delay A].
      (([Delay.map B C]ₛ g) (([Delay.map A B]ₛ f) d)
        = ([Delay.map A C]ₛ (λ x : A. g (f x))) d) := by
    glöb IH
    gintro f g d
    gcases ([Delay.PROJ A]ₛ d) with (⟨v, h⟩ | ⟨v, h⟩)
    · gassert HMK of (([Delay.MK A]ₛ (inl v)) = d)
      · grewrite ← h
        gapply (Delay.MK_PROJ A)
      grewrite ← HMK
      grewrite (Delay.map_ret A B)
      grewrite (Delay.map_ret B C)
      grewrite (Delay.map_ret A C)
      grfl
    · gassert HMK of (([Delay.MK A]ₛ (inr v)) = d)
      · grewrite ← h
        gapply (Delay.MK_PROJ A)
      grewrite ← HMK
      grewrite (Delay.map_step A B)
      grewrite (Delay.map_step B C)
      grewrite (Delay.map_step A C)
      gcong
      gmono IH as G
      gapply G f  g  (adv 1 v)

gtheorem Delay.bind_assoc (A B C : TYPE) :
    ∀ k : (A → [Delay B]). ∀ g : (B → [Delay C]). ∀ d : [Delay A].
      (([Delay.bind B C]ₛ g) (([Delay.bind A B]ₛ k) d)
        = ([Delay.bind A C]ₛ (λ a : A. ([Delay.bind B C]ₛ g) (k a))) d) := by
    glöb IH
    gintro k g d
    gcases ([Delay.PROJ A]ₛ d) with (⟨v, h⟩ | ⟨v, h⟩)
    · gassert HMK of (([Delay.MK A]ₛ (inl v)) = d)
      · grewrite ← h
        gapply (Delay.MK_PROJ A)
      grewrite ← HMK
      grewrite (Delay.bind_ret A B)
      grewrite (Delay.bind_ret A C)
      grfl
    · gassert HMK of (([Delay.MK A]ₛ (inr v)) = d)
      · grewrite ← h
        gapply (Delay.MK_PROJ A)
      grewrite ← HMK
      grewrite (Delay.bind_step A B)
      grewrite (Delay.bind_step B C)
      grewrite (Delay.bind_step A C)
      gcong
      gmono IH as G
      gapply G k  g  (adv 1 v)

gtheorem Delay.later_eq_trans (A : TYPE) :
    ∀ x : [Delay A]. ∀ y : [Delay A]. ∀ z : [Delay A].
      ((lift (delay (x = y))) → ((lift (delay (y = z))) → lift (delay (x = z)))) := by
    gintro x y z H1 H2
    gmono H1 H2 as E1 E2
    grewrite E1
    gexact E2

end composition_laws

section pointfree_laws

gtheorem Delay.map_id' (A : TYPE) :
    (([Delay.map A A]ₛ [idfun A]ₛ) = [idfun (Delay A)]ₛ) := by
  gapply (gfunext _ _) ([Delay.map A A]ₛ [idfun A]ₛ) ([idfun (Delay A)]ₛ)
  gintro d
  gunfold idfun
  gsimpl
  gapply (Delay.map_id A) d

gtheorem Delay.bind_ret_r' (A : TYPE) :
    (([Delay.bind A A]ₛ [Delay.ret A]ₛ) = [idfun (Delay A)]ₛ) := by
  gapply (gfunext _ _) ([Delay.bind A A]ₛ [Delay.ret A]ₛ) ([idfun (Delay A)]ₛ)
  gintro d
  gunfold idfun
  gunfold Delay.ret
  gsimpl
  gapply (Delay.bind_ret_r A) d

gtheorem Delay.map_comp' (A B C : TYPE) :
    ∀ f : (A → B). ∀ g : (B → C).
      ((([comp (Delay A) (Delay B) (Delay C)]ₛ ([Delay.map B C]ₛ g)) ([Delay.map A B]ₛ f))
        = [Delay.map A C]ₛ (([comp A B C]ₛ g) f)) := by
  gintro f g
  gapply (gfunext _ _)
    (([comp (Delay A) (Delay B) (Delay C)]ₛ ([Delay.map B C]ₛ g)) ([Delay.map A B]ₛ f))
    ([Delay.map A C]ₛ (([comp A B C]ₛ g) f))
  gintro d
  gunfold comp
  gsimpl
  gapply (Delay.map_comp A B C) f g d

gtheorem Delay.bind_assoc' (A B C : TYPE) :
    ∀ k : (A → [Delay B]). ∀ g : (B → [Delay C]).
      ((([comp (Delay A) (Delay B) (Delay C)]ₛ ([Delay.bind B C]ₛ g)) ([Delay.bind A B]ₛ k))
        = [Delay.bind A C]ₛ (([comp A (Delay B) (Delay C)]ₛ ([Delay.bind B C]ₛ g)) k)) := by
  gintro k g
  gapply (gfunext _ _)
    (([comp (Delay A) (Delay B) (Delay C)]ₛ ([Delay.bind B C]ₛ g)) ([Delay.bind A B]ₛ k))
    ([Delay.bind A C]ₛ (([comp A (Delay B) (Delay C)]ₛ ([Delay.bind B C]ₛ g)) k))
  gintro d
  gunfold comp
  gsimpl
  gapply (Delay.bind_assoc A B C) k g d

end pointfree_laws

end guarded_delay

end
