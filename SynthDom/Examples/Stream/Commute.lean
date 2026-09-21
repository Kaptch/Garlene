module

public import SynthDom
public import SynthDom.Examples.Stream.Base
@[expose] public section

section stream_delay_distr
open CategoryTheory

gdef Delay.swap (X : TYPE) : [Delay ⦃▸ X⦄] → ▸ [Delay X] :=
  fix μ. λ d.
    case ([Delay.PROJ ⦃▸ X⦄]ₛ d)
      (λ w. delay ([Delay.MK X]ₛ (inl (adv 1 w))))
      (λ w. delay ([Delay.MK X]ₛ (inr ((adv 1 μ) (adv 1 w)))))

section swap_equations
gtheorem Delay.swap_ret (X : TYPE) :
    ∀ w : ▸ X.
      (([Delay.swap X]ₛ ([Delay.MK ⦃▸ X⦄]ₛ (inl w)))
        = delay ([Delay.MK X]ₛ (inl (adv 1 w)))) := by
    gintro w
    gunfold Delay.swap
    gfix
    grewrite (Delay.PROJ_MK ⦃▸ X⦄)
    gsimpl
    grfl

gtheorem Delay.swap_step (X : TYPE) :
    ∀ w : ▸ [Delay ⦃▸ X⦄].
      (([Delay.swap X]ₛ ([Delay.MK ⦃▸ X⦄]ₛ (inr w)))
        = delay ([Delay.MK X]ₛ (inr ([Delay.swap X]ₛ (adv 1 w))))) := by
    gintro w
    gunfold Delay.swap
    gfix
    grewrite (Delay.PROJ_MK ⦃▸ X⦄)
    gsimpl
    grfl

end swap_equations

gdef Str.distr (A : TYPE) : [Delay (Str A)] → [Str (Delay A)] :=
  fix μ. λ d.
    [Str.MK (Delay A)]ₛ
      ⟨([Delay.map (Str A) A]ₛ (λ s : [Str A]. π₁ ([Str.PROJ A]ₛ s))) d,
       delay ((adv 1 μ)
         (adv 1 ([Delay.swap (Str A)]ₛ
           (([Delay.map (Str A) ⦃▸ [Str A]⦄]ₛ
               (λ s : [Str A]. π₂ ([Str.PROJ A]ₛ s))) d))))⟩

section distr_equations
gtheorem Str.distr_cons (A : TYPE) :
    ∀ d : [Delay (Str A)].
      (([Str.distr A]ₛ d)
        = [Str.MK (Delay A)]ₛ
            ⟨([Delay.map (Str A) A]ₛ (λ s : [Str A]. π₁ ([Str.PROJ A]ₛ s))) d,
             delay (([Str.distr A]ₛ
               (adv 1 ([Delay.swap (Str A)]ₛ
                 (([Delay.map (Str A) ⦃▸ [Str A]⦄]ₛ
                     (λ s : [Str A]. π₂ ([Str.PROJ A]ₛ s))) d)))))⟩) := by
    gintro d
    gunfold Str.distr
    gfix
    grfl

gtheorem Str.distr_hd (A : TYPE) :
    ∀ d : [Delay (Str A)].
      (π₁ ([Str.PROJ (Delay A)]ₛ (([Str.distr A]ₛ d)))
        = ([Delay.map (Str A) A]ₛ (λ s : [Str A]. π₁ ([Str.PROJ A]ₛ s))) d) := by
    gintro d
    grewrite (Str.distr_cons A)
    grewrite (Str.PROJ_MK (Delay A))
    gsimpl
    grfl

gtheorem Str.distr_hd_fn (A : TYPE) :
    ((λ x : [Delay (Str A)]. π₁ ([Str.PROJ (Delay A)]ₛ ([Str.distr A]ₛ x)))
      = (λ x : [Delay (Str A)].
          ([Delay.map (Str A) A]ₛ (λ s : [Str A]. π₁ ([Str.PROJ A]ₛ s))) x)) := by
  gapply (gfunext _ _)
    (λ x : [Delay (Str A)]. π₁ ([Str.PROJ (Delay A)]ₛ ([Str.distr A]ₛ x)))
    (λ x : [Delay (Str A)].
      ([Delay.map (Str A) A]ₛ (λ s : [Str A]. π₁ ([Str.PROJ A]ₛ s))) x)
  gintro x
  gsimpl
  gapply (Str.distr_hd A) x

gtheorem Str.distr_tl (A : TYPE) :
    ∀ d : [Delay (Str A)].
      (π₂ ([Str.PROJ (Delay A)]ₛ (([Str.distr A]ₛ d)))
        = delay (([Str.distr A]ₛ
            (adv 1 ([Delay.swap (Str A)]ₛ
              (([Delay.map (Str A) ⦃▸ [Str A]⦄]ₛ
                  (λ s : [Str A]. π₂ ([Str.PROJ A]ₛ s))) d)))))) := by
    gintro d
    grewrite (Str.distr_cons A)
    grewrite (Str.PROJ_MK (Delay A))
    gsimpl
    grfl

end distr_equations

section distr_laws
gtheorem Str.distr_ret (A : TYPE) :
    ∀ t : [Str A].
      (([Str.distr A]ₛ ([Delay.MK (Str A)]ₛ (inl t)))
        = ([Str.map A (Delay A)]ₛ (λ a : A. [Delay.MK A]ₛ (inl a))) t) := by
    glöb IH
    gintro t
    grewrite (Str.distr_cons A)
    grewrite (Delay.map_ret (Str A) A)
    grewrite (Delay.map_ret (Str A) ⦃▸ [Str A]⦄)
    grewrite (Delay.swap_ret (Str A))
    grewrite (Str.map_cons A (Delay A))
    gsimpl
    gcong
    gmono IH as G
    gapply G (adv 1 (π₂ ([Str.PROJ A]ₛ t)))

end distr_laws

section congr_glue
gtheorem Delay.map_congr (A B : TYPE) :
    ∀ f : (A → B). ∀ g : (A → B).
      ((∀ x : A. (f x = g x))
        → ∀ d : [Delay A]. (([Delay.map A B]ₛ f) d = ([Delay.map A B]ₛ g) d)) := by
    glöb IH
    gintro f g H d
    gcases ([Delay.PROJ A]ₛ d) with (⟨v, h⟩ | ⟨v, h⟩)
    · gassert HMK of (([Delay.MK A]ₛ (inl v)) = d)
      · grewrite ← h
        gapply (Delay.MK_PROJ A)
      grewrite ← HMK
      grewrite (Delay.map_ret A B)
      grewrite (Delay.map_ret A B)
      grewrite H v
      grfl
    · gassert HMK of (([Delay.MK A]ₛ (inr v)) = d)
      · grewrite ← h
        gapply (Delay.MK_PROJ A)
      grewrite ← HMK
      grewrite (Delay.map_step A B)
      grewrite (Delay.map_step A B)
      gcong
      gmono IH as G
      gapply G f  g  (adv 1 v)
      gexact H

end congr_glue

section dup_law
gtheorem Str.mapDup_ret_delayed (A : TYPE) :
    ∀ w : ▸ [Str A].
      (delay (([Delay.map (Str A)
                          (Str (Str A))]ₛ (λ t : [Str A]. [Str.dup A]ₛ t))
                ([Delay.MK (Str A)]ₛ (inl (adv 1 w))))
        = delay ([Delay.MK (Str (Str A))]ₛ
                  (inl ([Str.dup A]ₛ (adv 1 w))))) := by
    gintro w
    gnext
    grewrite (Delay.map_ret (Str A) (Str (Str A)))
      (λ t : [Str A]. [Str.dup A]ₛ t) (adv 1 w)
    grfl

gtheorem Str.mapDup_step_delayed (A : TYPE) :
    ∀ v : ▸ [Delay (Str A)].
      (delay (([Delay.map (Str A)
                          (Str (Str A))]ₛ (λ t : [Str A]. [Str.dup A]ₛ t))
                ([Delay.MK (Str A)]ₛ
                  (inr ([Delay.swap (Str A)]ₛ
                    (([Delay.map (Str A)
                                 ⦃▸ [Str A]⦄]ₛ
                        (λ s : [Str A]. π₂ ([Str.PROJ A]ₛ s))) (adv 1 v))))))
        = delay ([Delay.MK (Str (Str A))]ₛ
                  (inr (delay (([Delay.map (Str A)
                                           (Str (Str A))]ₛ
                                  (λ t : [Str A]. [Str.dup A]ₛ t))
                          (adv 1 ([Delay.swap (Str A)]ₛ
                            (([Delay.map (Str A)
                                         ⦃▸ [Str A]⦄]ₛ
                                (λ s : [Str A]. π₂ ([Str.PROJ A]ₛ s))) (adv 1 v))))))))) := by
    gintro v
    gnext
    gapply (Delay.map_step (Str A) (Str (Str A)))
      (λ t : [Str A]. [Str.dup A]ₛ t) (([Delay.swap (Str A)]ₛ
      (([Delay.map (Str A)
                   ⦃▸ [Str A]⦄]ₛ
          (λ s : [Str A]. π₂ ([Str.PROJ A]ₛ s))) (adv 1 v))))

gtheorem Str.dup_swap_comm (A : TYPE) :
    ∀ d : [Delay (Str A)].
      (([Delay.swap (Str (Str A))]ₛ
          (([Delay.map (Str (Str A))
                       ⦃▸ [Str (Str A)]⦄]ₛ
              (λ s : [Str (Str A)]. π₂ ([Str.PROJ (Str A)]ₛ s)))
            (([Delay.map (Str A)
                         (Str (Str A))]ₛ (λ t : [Str A]. [Str.dup A]ₛ t)) d)))
        = delay (([Delay.map (Str A)
                             (Str (Str A))]ₛ (λ t : [Str A]. [Str.dup A]ₛ t))
            (adv 1 ([Delay.swap (Str A)]ₛ
              (([Delay.map (Str A)
                           ⦃▸ [Str A]⦄]ₛ
                  (λ s : [Str A]. π₂ ([Str.PROJ A]ₛ s))) d))))) := by
    glöb IH
    gintro d
    gcases ([Delay.PROJ (Str A)]ₛ d) with (⟨v, hd⟩ | ⟨v, hd⟩)
    · gassert HMK of (([Delay.MK (Str A)]ₛ (inl v)) = d)
      · grewrite ← hd
        gapply (Delay.MK_PROJ (Str A))
      grewrite ← HMK
      grewrite (Delay.map_ret (Str A)
                  (Str (Str A)))
      gsimpl
      grewrite (Delay.map_ret (Str (Str A))
                  ⦃▸ [Str (Str A)]⦄)
      gsimpl
      grewrite (Delay.swap_ret (Str (Str A)))
      grewrite (Delay.map_ret (Str A) ⦃▸ [Str A]⦄)
      grewrite (Delay.swap_ret (Str A))
      gsimpl
      grewrite (Str.mapDup_ret_delayed A) (π₂ ([Str.PROJ A]ₛ v))
      grewrite (Str.dup_tl A)
      gsimpl
      grfl
    · gassert HMK of (([Delay.MK (Str A)]ₛ (inr v)) = d)
      · grewrite ← hd
        gapply (Delay.MK_PROJ (Str A))
      grewrite ← HMK
      grewrite (Delay.map_step (Str A)
                  (Str (Str A)))
      grewrite (Delay.map_step (Str (Str A))
                  ⦃▸ [Str (Str A)]⦄)
      gsimpl
      grewrite (Delay.swap_step (Str (Str A)))
      gsimpl
      grewrite (Delay.map_step (Str A)
                       ⦃▸ [Str A]⦄)
      grewrite (Delay.swap_step (Str A))
      gsimpl
      grewrite (Str.mapDup_step_delayed A) v
      gmono IH as G
      gcong
      gapply G (adv 1 v)

gtheorem Str.mapHd_dup_id (A : TYPE) :
    ∀ d : [Delay (Str A)].
      ((([Delay.map (Str (Str A)) (Str A)]ₛ
          (λ s : [Str (Str A)]. π₁ ([Str.PROJ (Str A)]ₛ s)))
        (([Delay.map (Str A) (Str (Str A))]ₛ
            (λ t : [Str A]. [Str.dup A]ₛ t)) d))
        = d) := by
    gintro d
    grewrite (Delay.map_comp (Str A)
                (Str (Str A))
                (Str A))
    grewrite (Str.extract_dup_fn A)
    gapply (Delay.map_id (Str A))

gtheorem Str.distr_dup (A : TYPE) :
    ∀ d : [Delay (Str A)].
      (([Str.dup (Delay A)]ₛ ([Str.distr A]ₛ d))
        = ([Str.map (Delay (Str A))
                    (Str (Delay A))]ₛ
            (λ c : [Delay (Str A)]. [Str.distr A]ₛ c))
          ([Str.distr (Str A)]ₛ
            (([Delay.map (Str A)
                         (Str (Str A))]ₛ
                (λ t : [Str A]. [Str.dup A]ₛ t)) d))) := by
    glöb IH
    gintro d
    grewrite (Str.dup_cons (Delay A))
    grewrite (Str.distr_tl A)
    gsimpl
    grewrite (Str.map_cons (Delay (Str A))
                (Str (Delay A)))
    grewrite (Str.distr_hd (Str A))
    grewrite (Str.distr_tl (Str A))
    gsimpl
    grewrite (Str.mapHd_dup_id A)
    grewrite (Str.dup_swap_comm A)
    gsimpl
    gcong
    gmono IH as G
    gapply G (adv 1 ([Delay.swap (Str A)]ₛ
      (([Delay.map (Str A)
                   ⦃▸ [Str A]⦄]ₛ
          (λ s : [Str A]. π₂ ([Str.PROJ A]ₛ s))) d)))

end dup_law

section mult_infra
gtheorem Delay.bind_congr (A B : TYPE) :
    ∀ k : (A → [Delay B]). ∀ g : (A → [Delay B]).
      ((∀ x : A. (k x = g x))
        → ∀ d : [Delay A]. (([Delay.bind A B]ₛ k) d = ([Delay.bind A B]ₛ g) d)) := by
    glöb IH
    gintro k g H d
    gcases ([Delay.PROJ A]ₛ d) with (⟨v, hd⟩ | ⟨v, hd⟩)
    · gassert HMK of (([Delay.MK A]ₛ (inl v)) = d)
      · grewrite ← hd
        gapply (Delay.MK_PROJ A)
      grewrite ← HMK
      grewrite (Delay.bind_ret A B)
      grewrite (Delay.bind_ret A B)
      grewrite H v
      grfl
    · gassert HMK of (([Delay.MK A]ₛ (inr v)) = d)
      · grewrite ← hd
        gapply (Delay.MK_PROJ A)
      grewrite ← HMK
      grewrite (Delay.bind_step A B)
      grewrite (Delay.bind_step A B)
      gcong
      gmono IH as G
      gapply G k g (adv 1 v)
      gexact H

gtheorem Delay.map_bind (A B C : TYPE) :
    ∀ k : (A → [Delay B]). ∀ f : (B → C). ∀ d : [Delay A].
      (([Delay.map B C]ₛ f) (([Delay.bind A B]ₛ k) d)
        = ([Delay.bind A C]ₛ (λ x : A. ([Delay.map B C]ₛ f) (k x))) d) := by
    glöb IH
    gintro k f d
    gcases ([Delay.PROJ A]ₛ d) with (⟨v, hd⟩ | ⟨v, hd⟩)
    · gassert HMK of (([Delay.MK A]ₛ (inl v)) = d)
      · grewrite ← hd
        gapply (Delay.MK_PROJ A)
      grewrite ← HMK
      grewrite (Delay.bind_ret A B)
      grewrite (Delay.bind_ret A C)
      grfl
    · gassert HMK of (([Delay.MK A]ₛ (inr v)) = d)
      · grewrite ← hd
        gapply (Delay.MK_PROJ A)
      grewrite ← HMK
      grewrite (Delay.bind_step A B)
      grewrite (Delay.map_step B C)
      grewrite (Delay.bind_step A C)
      gcong
      gmono IH as G
      gapply G k f (adv 1 v)

gtheorem Delay.bind_map (A B C : TYPE) :
    ∀ g : (A → B). ∀ k : (B → [Delay C]). ∀ d : [Delay A].
      (([Delay.bind B C]ₛ k) (([Delay.map A B]ₛ g) d)
        = ([Delay.bind A C]ₛ (λ x : A. k (g x))) d) := by
    glöb IH
    gintro g k d
    gcases ([Delay.PROJ A]ₛ d) with (⟨v, hd⟩ | ⟨v, hd⟩)
    · gassert HMK of (([Delay.MK A]ₛ (inl v)) = d)
      · grewrite ← hd
        gapply (Delay.MK_PROJ A)
      grewrite ← HMK
      grewrite (Delay.map_ret A B)
      grewrite (Delay.bind_ret B C)
      grewrite (Delay.bind_ret A C)
      grfl
    · gassert HMK of (([Delay.MK A]ₛ (inr v)) = d)
      · grewrite ← hd
        gapply (Delay.MK_PROJ A)
      grewrite ← HMK
      grewrite (Delay.map_step A B)
      grewrite (Delay.bind_step B C)
      grewrite (Delay.bind_step A C)
      gcong
      gmono IH as G
      gapply G g k (adv 1 v)

end mult_infra

section swap_natural
gtheorem Delay.swap_natural (X Y : TYPE) :
    ∀ h : (X → Y). ∀ c : [Delay ⦃▸ X⦄].
      (([Delay.swap Y]ₛ
          (([Delay.map ⦃▸ X⦄ ⦃▸ Y⦄]ₛ
              (λ w : ▸ X. delay (h (adv 1 w)))) c))
        = delay (([Delay.map X Y]ₛ h) (adv 1 ([Delay.swap X]ₛ c)))) := by
    glöb IH
    gintro h c
    gcases ([Delay.PROJ ⦃▸ X⦄]ₛ c) with (⟨v, hd⟩ | ⟨v, hd⟩)
    · gassert HMK of (([Delay.MK ⦃▸ X⦄]ₛ (inl v)) = c)
      · grewrite ← hd
        gapply (Delay.MK_PROJ ⦃▸ X⦄)
      grewrite ← HMK
      grewrite (Delay.map_ret ⦃▸ X⦄ ⦃▸ Y⦄)
      grewrite (Delay.swap_ret Y)
      grewrite (Delay.swap_ret X)
      gsimpl
      gnext
      grewrite (Delay.map_ret X Y) h (adv 1 v)
      grfl
    · gassert HMK of (([Delay.MK ⦃▸ X⦄]ₛ (inr v)) = c)
      · grewrite ← hd
        gapply (Delay.MK_PROJ ⦃▸ X⦄)
      grewrite ← HMK
      grewrite (Delay.map_step ⦃▸ X⦄ ⦃▸ Y⦄)
      grewrite (Delay.swap_step Y)
      grewrite (Delay.swap_step X)
      gsimpl
      gmono IH as G
      grewrite G h (adv 1 v)
      grewrite (Delay.map_step X Y) h
      grfl

end swap_natural

section join_swap
gtheorem Str.join_swap_comm (A : TYPE) :
    ∀ dd : [Delay (Delay (Str A))].
      (([Delay.swap (Str A)]ₛ
          (([Delay.map (Str A)
                       ⦃▸ [Str A]⦄]ₛ
              (λ s : [Str A]. π₂ ([Str.PROJ A]ₛ s)))
            (([Delay.bind (Delay (Str A))
                          (Str A)]ₛ
                (λ c : [Delay (Str A)]. c)) dd)))
        = delay ((([Delay.bind (Delay (Str A))
                               (Str A)]ₛ
              (λ c : [Delay (Str A)]. c))
            (adv 1 ([Delay.swap (Delay (Str A))]ₛ
              (([Delay.map (Delay (Str A))
                           ⦃▸ [Delay (Str A)]⦄]ₛ
                  (λ c : [Delay (Str A)].
                    [Delay.swap (Str A)]ₛ
                      (([Delay.map (Str A)
                                   ⦃▸ [Str A]⦄]ₛ
                          (λ s : [Str A]. π₂ ([Str.PROJ A]ₛ s))) c))) dd)))))) := by
    glöb IH
    gintro dd
    gcases ([Delay.PROJ (Delay (Str A))]ₛ dd) with (⟨v, hd⟩ | ⟨v, hd⟩)
    · gassert HMK of (([Delay.MK (Delay (Str A))]ₛ (inl v)) = dd)
      · grewrite ← hd
        gapply (Delay.MK_PROJ (Delay (Str A)))
      grewrite ← HMK
      grewrite (Delay.bind_ret (Delay (Str A))
                  (Str A))
      gsimpl
      grewrite (Delay.map_ret (Delay (Str A)) ⦃▸ [Delay (Str A)]⦄)
      gsimpl
      grewrite (Delay.swap_ret (Delay (Str A)))
      gsimpl
      grewrite ← (Delay.delay_eta (Str A))
        (([Delay.swap (Str A)]ₛ
          (([Delay.map (Str A)
                       ⦃▸ [Str A]⦄]ₛ
              (λ s : [Str A]. π₂ ([Str.PROJ A]ₛ s))) v)))
      gnext
      gsimpl
      grewrite (Delay.bind_ret (Delay (Str A)) (Str A))
        (λ c : [Delay (Str A)]. c) (adv 1 ([Delay.swap (Str A)]ₛ
        (([Delay.map (Str A)
                     ⦃▸ [Str A]⦄]ₛ
            (λ s : [Str A]. π₂ ([Str.PROJ A]ₛ s))) v)))
      gsimpl
      grfl
    · gassert HMK of (([Delay.MK (Delay (Str A))]ₛ (inr v)) = dd)
      · grewrite ← hd
        gapply (Delay.MK_PROJ (Delay (Str A)))
      grewrite ← HMK
      grewrite (Delay.bind_step (Delay (Str A))
                  (Str A))
      grewrite (Delay.map_step (Str A)
                  ⦃▸ [Str A]⦄)
      gsimpl
      grewrite (Delay.swap_step (Str A))
      gsimpl
      grewrite (Delay.map_step (Delay (Str A))
                       ⦃▸ [Delay (Str A)]⦄)
      grewrite (Delay.swap_step (Delay (Str A)))
      gsimpl
      gmono IH as G
      grewrite G (adv 1 v)
      grewrite (Delay.bind_step (Delay (Str A)) (Str A))
        (λ c : [Delay (Str A)]. c)
      grfl

end join_swap

section mapTl_distr
gtheorem Str.mapTl_distr_comm (A : TYPE) :
    ∀ dd : [Delay (Delay (Str A))].
      ((([Delay.map (Str (Delay A))
                    ⦃▸ [Str (Delay A)]⦄]ₛ
          (λ s : [Str (Delay A)].
            π₂ ([Str.PROJ (Delay A)]ₛ s)))
        (([Delay.map (Delay (Str A))
                     (Str (Delay A))]ₛ
            (λ c : [Delay (Str A)]. [Str.distr A]ₛ c)) dd))
        = (([Delay.map ⦃▸ [Delay (Str A)]⦄
                       ⦃▸ [Str (Delay A)]⦄]ₛ
            (λ w : ▸ [Delay (Str A)].
              delay ([Str.distr A]ₛ (adv 1 w))))
          (([Delay.map (Delay (Str A))
                       ⦃▸ [Delay (Str A)]⦄]ₛ
              (λ c : [Delay (Str A)].
                [Delay.swap (Str A)]ₛ
                  (([Delay.map (Str A)
                               ⦃▸ [Str A]⦄]ₛ
                      (λ s : [Str A]. π₂ ([Str.PROJ A]ₛ s))) c))) dd))) := by
    glöb IH
    gintro dd
    gcases ([Delay.PROJ (Delay (Str A))]ₛ dd) with (⟨v, hd⟩ | ⟨v, hd⟩)
    · gassert HMK of (([Delay.MK (Delay (Str A))]ₛ (inl v)) = dd)
      · grewrite ← hd
        gapply (Delay.MK_PROJ (Delay (Str A)))
      grewrite ← HMK
      grewrite (Delay.map_ret (Delay (Str A))
                  (Str (Delay A)))
      grewrite (Delay.map_ret (Str (Delay A))
                  ⦃▸ [Str (Delay A)]⦄)
      grewrite (Str.distr_tl A)
      grewrite (Delay.map_ret (Delay (Str A)) ⦃▸ [Delay (Str A)]⦄)
      grewrite (Delay.map_ret ⦃▸ [Delay (Str A)]⦄ ⦃▸ [Str (Delay A)]⦄)
      grfl
    · gassert HMK of (([Delay.MK (Delay (Str A))]ₛ (inr v)) = dd)
      · grewrite ← hd
        gapply (Delay.MK_PROJ (Delay (Str A)))
      grewrite ← HMK
      grewrite (Delay.map_step (Delay (Str A))
                  (Str (Delay A)))
      grewrite (Delay.map_step (Str (Delay A))
                  ⦃▸ [Str (Delay A)]⦄)
      grewrite (Delay.map_step (Delay (Str A))
                  ⦃▸ [Delay (Str A)]⦄)
      grewrite (Delay.map_step ⦃▸ [Delay (Str A)]⦄ ⦃▸ [Str (Delay A)]⦄)
      gcong
      gmono IH as G
      gapply G (adv 1 v)

end mapTl_distr

section mult_law
gtheorem Str.distr_join (A : TYPE) :
    ∀ dd : [Delay (Delay (Str A))].
      (([Str.distr A]ₛ
          (([Delay.bind (Delay (Str A))
                        (Str A)]ₛ
              (λ c : [Delay (Str A)]. c)) dd))
        = ([Str.map (Delay (Delay A))
                    (Delay A)]ₛ
            (λ c : [Delay (Delay A)].
              ([Delay.bind (Delay A) A]ₛ (λ x : [Delay A]. x)) c))
          ([Str.distr (Delay A)]ₛ
            (([Delay.map (Delay (Str A))
                         (Str (Delay A))]ₛ
                (λ c : [Delay (Str A)]. [Str.distr A]ₛ c)) dd))) := by
    glöb IH
    gintro dd
    grewrite (Str.distr_cons A)
    grewrite (Str.join_swap_comm A)
    gsimpl
    grewrite (Str.map_cons (Delay (Delay A))
                (Delay A))
    grewrite (Str.distr_hd (Delay A))
    grewrite (Str.distr_tl (Delay A))
    gsimpl
    grewrite (Delay.map_bind (Delay (Str A))
                (Str A) A)
    gsimpl
    grewrite (Delay.map_comp (Delay (Str A))
                (Str (Delay A))
                (Delay A))
    grewrite (Str.distr_hd_fn A)
    grewrite (Delay.bind_map (Delay (Str A))
                (Delay A) A)
    gsimpl
    grewrite (Str.mapTl_distr_comm A) dd
    grewrite (Delay.swap_natural (Delay (Str A)) (Str (Delay A)))
      (λ c : [Delay (Str A)]. [Str.distr A]ₛ c)
      (([Delay.map (Delay (Str A)) ⦃▸ [Delay (Str A)]⦄]ₛ
          (λ c : [Delay (Str A)].
            [Delay.swap (Str A)]ₛ
              (([Delay.map (Str A) ⦃▸ [Str A]⦄]ₛ
                  (λ s : [Str A]. π₂ ([Str.PROJ A]ₛ s))) c))) dd)
    gsimpl
    gcong
    gmono IH as G
    gapply G (adv 1 ([Delay.swap (Delay (Str A))]ₛ
      (([Delay.map (Delay (Str A))
                   ⦃▸ [Delay (Str A)]⦄]ₛ
          (λ c : [Delay (Str A)].
            [Delay.swap (Str A)]ₛ
              (([Delay.map (Str A)
                           ⦃▸ [Str A]⦄]ₛ
                  (λ s : [Str A]. π₂ ([Str.PROJ A]ₛ s))) c))) dd)))

end mult_law

section pointfree_laws

gtheorem Str.mapHd_dup_id' (A : TYPE) :
    ((([comp (Delay (Str A)) (Delay (Str (Str A))) (Delay (Str A))]ₛ
        ([Delay.map (Str (Str A)) (Str A)]ₛ
          (λ s : [Str (Str A)]. π₁ ([Str.PROJ (Str A)]ₛ s))))
      ([Delay.map (Str A) (Str (Str A))]ₛ (λ t : [Str A]. [Str.dup A]ₛ t)))
      = [idfun (Delay (Str A))]ₛ) := by
  gapply (gfunext _ _)
    (([comp (Delay (Str A)) (Delay (Str (Str A))) (Delay (Str A))]ₛ
        ([Delay.map (Str (Str A)) (Str A)]ₛ
          (λ s : [Str (Str A)]. π₁ ([Str.PROJ (Str A)]ₛ s))))
      ([Delay.map (Str A) (Str (Str A))]ₛ (λ t : [Str A]. [Str.dup A]ₛ t)))
    ([idfun (Delay (Str A))]ₛ)
  gintro d
  gunfold comp
  gunfold idfun
  gsimpl
  gapply (Str.mapHd_dup_id A) d

gtheorem Str.distr_dup' (A : TYPE) :
    ((([comp (Delay (Str A)) (Str (Delay A)) (Str (Str (Delay A)))]ₛ
        [Str.dup (Delay A)]ₛ) [Str.distr A]ₛ)
      = ([comp (Delay (Str A)) (Str (Delay (Str A))) (Str (Str (Delay A)))]ₛ
          ([Str.map (Delay (Str A)) (Str (Delay A))]ₛ
            (λ c : [Delay (Str A)]. [Str.distr A]ₛ c)))
        (([comp (Delay (Str A)) (Delay (Str (Str A))) (Str (Delay (Str A)))]ₛ
            [Str.distr (Str A)]ₛ)
          ([Delay.map (Str A) (Str (Str A))]ₛ (λ t : [Str A]. [Str.dup A]ₛ t)))) := by
  gapply (gfunext _ _)
    (([comp (Delay (Str A)) (Str (Delay A)) (Str (Str (Delay A)))]ₛ
        [Str.dup (Delay A)]ₛ) [Str.distr A]ₛ)
    (([comp (Delay (Str A)) (Str (Delay (Str A))) (Str (Str (Delay A)))]ₛ
        ([Str.map (Delay (Str A)) (Str (Delay A))]ₛ
          (λ c : [Delay (Str A)]. [Str.distr A]ₛ c)))
      (([comp (Delay (Str A)) (Delay (Str (Str A))) (Str (Delay (Str A)))]ₛ
          [Str.distr (Str A)]ₛ)
        ([Delay.map (Str A) (Str (Str A))]ₛ (λ t : [Str A]. [Str.dup A]ₛ t))))
  gintro d
  gunfold comp
  gsimpl
  gapply (Str.distr_dup A) d

end pointfree_laws

end stream_delay_distr

end
