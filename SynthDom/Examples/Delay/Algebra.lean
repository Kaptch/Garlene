module

public import SynthDom
public import SynthDom.Examples.Delay.Base
public import SynthDom.Examples.Utils.Funext
@[expose] public section

section free_delay_algebra
open CategoryTheory

gdef Delay.ext (A B : TYPE) : (▸ B → B) → (A → B) → [Delay A] → B :=
  fix e. λ s. λ f. λ d.
    case ([Delay.PROJ A]ₛ d)
      f
      (λ w. s (delay ((((adv 1 e) s) f) (adv 1 w))))

gtheorem Delay.ret_mk (A : TYPE) :
    ∀ a : A. (([Delay.ret A]ₛ a) = [Delay.MK A]ₛ (inl a)) := by
  gintro a
  gunfold Delay.ret
  gsimpl
  grfl

gtheorem Delay.step_mk (A : TYPE) :
    ∀ w : ▸ [Delay A]. (([Delay.step A]ₛ w) = [Delay.MK A]ₛ (inr w)) := by
  gintro w
  gunfold Delay.step
  gsimpl
  grfl

gtheorem Delay.ext_ret (A B : TYPE) :
    ∀ s : (▸ B → B). ∀ f : (A → B). ∀ a : A.
      (((([Delay.ext A B]ₛ s) f) ([Delay.ret A]ₛ a)) = f a) := by
  gintro s f a
  gunfold Delay.ext
  gfix
  gunfold Delay.ret
  gsimpl
  grewrite (Delay.PROJ_MK A)
  gsimpl
  grfl

gtheorem Delay.ext_step (A B : TYPE) :
    ∀ s : (▸ B → B). ∀ f : (A → B). ∀ w : ▸ [Delay A].
      (((([Delay.ext A B]ₛ s) f) ([Delay.step A]ₛ w))
        = s (delay ((([Delay.ext A B]ₛ s) f) (adv 1 w)))) := by
  gintro s f w
  gunfold Delay.ext
  gfix
  gunfold Delay.step
  gsimpl
  grewrite (Delay.PROJ_MK A)
  gsimpl
  grfl

gtheorem Delay.ext_unique (A B : TYPE) :
    ∀ s : (▸ B → B). ∀ f : (A → B). ∀ h : ([Delay A] → B).
      ((∀ a : A. (h ([Delay.ret A]ₛ a) = f a))
        → ((∀ w : ▸ [Delay A]. (h ([Delay.step A]ₛ w) = s (delay (h (adv 1 w)))))
          → ∀ d : [Delay A]. (h d = (([Delay.ext A B]ₛ s) f) d))) := by
  gintro s f h Hret Hstep
  glöb IH
  gintro d
  gcases ([Delay.PROJ A]ₛ d) with (⟨v, hd⟩ | ⟨v, hd⟩)
  · gassert HMK of (([Delay.MK A]ₛ (inl v)) = d)
    · grewrite ← hd
      gapply (Delay.MK_PROJ A)
    grewrite ← HMK
    grewrite ← (Delay.ret_mk A) v
    grewrite Hret v
    grewrite (Delay.ext_ret A B)
    grfl
  · gassert HMK of (([Delay.MK A]ₛ (inr v)) = d)
    · grewrite ← hd
      gapply (Delay.MK_PROJ A)
    grewrite ← HMK
    grewrite ← (Delay.step_mk A) v
    grewrite Hstep v
    grewrite (Delay.ext_step A B)
    gcong
    gmono IH as G
    gapply G

gtheorem Delay.ext_unique_pointfree (A B : TYPE) :
    ∀ s : (▸ B → B). ∀ f : (A → B). ∀ h : ([Delay A] → B).
      ((∀ a : A. (h ([Delay.ret A]ₛ a) = f a))
        → ((∀ w : ▸ [Delay A]. (h ([Delay.step A]ₛ w) = s (delay (h (adv 1 w)))))
          → (h = ([Delay.ext A B]ₛ s) f))) := by
  gintro s f h Hret Hstep
  gapply (gfunext _ _) h (([Delay.ext A B]ₛ s) f)
  gintro d
  gapply (Delay.ext_unique A B) s f h d
  · gexact Hret
  · gexact Hstep

end free_delay_algebra

section derived_monad

gtheorem Delay.bind_eq_ext (A B : TYPE) :
    ∀ k : (A → [Delay B]).
      (([Delay.bind A B]ₛ k) = ([Delay.ext A (Delay B)]ₛ [Delay.step B]ₛ) k) := by
  gintro k
  gapply (Delay.ext_unique_pointfree _ _) [Delay.step B]ₛ k ([Delay.bind A B]ₛ k)
  · gintro a
    gapply (Delay.bind_ret_l A B) k a
  · gintro w
    grewrite (Delay.step_mk A) w
    grewrite (Delay.bind_step A B)
    grewrite (Delay.step_mk B)
    grfl

gtheorem Delay.map_eq_ext (A B : TYPE) :
    ∀ f : (A → B).
      (([Delay.map A B]ₛ f)
        = ([Delay.ext A (Delay B)]ₛ [Delay.step B]ₛ) (([comp A B (Delay B)]ₛ [Delay.ret B]ₛ) f)) := by
  gintro f
  gapply (Delay.ext_unique_pointfree _ _) [Delay.step B]ₛ
    (([comp A B (Delay B)]ₛ [Delay.ret B]ₛ) f) ([Delay.map A B]ₛ f)
  · gintro a
    gunfold comp
    gsimpl
    grewrite (Delay.ret_mk A) a
    grewrite (Delay.map_ret A B)
    grewrite (Delay.ret_mk B)
    grfl
  · gintro w
    grewrite (Delay.step_mk A) w
    grewrite (Delay.map_step A B)
    grewrite (Delay.step_mk B)
    grfl

gtheorem Delay.bind_ret_l_free (A B : TYPE) :
    ∀ k : (A → [Delay B]). ∀ a : A.
      (([Delay.bind A B]ₛ k) ([Delay.ret A]ₛ a) = k a) := by
  gintro k a
  grewrite (Delay.bind_eq_ext A B) k
  gapply (Delay.ext_ret _ _) [Delay.step B]ₛ k a

gtheorem Delay.bind_ret_r_free (A : TYPE) :
    (([Delay.bind A A]ₛ [Delay.ret A]ₛ) = [idfun (Delay A)]ₛ) := by
  grewrite (Delay.bind_eq_ext A A) [Delay.ret A]ₛ
  grewrite ← (Delay.ext_unique_pointfree A (Delay A)) [Delay.step A]ₛ [Delay.ret A]ₛ
    [idfun (Delay A)]ₛ
  · gintro a
    gunfold idfun
    gsimpl
    grfl
  · gintro w
    gunfold idfun
    gsimpl
    grewrite (Delay.delay_eta A) w
    grfl
  grfl

gtheorem Delay.map_id_free (A : TYPE) :
    (([Delay.map A A]ₛ [idfun A]ₛ) = [idfun (Delay A)]ₛ) := by
  grewrite (Delay.map_eq_ext A A) [idfun A]ₛ
  grewrite ← (Delay.ext_unique_pointfree A (Delay A)) [Delay.step A]ₛ
    (([comp A A (Delay A)]ₛ [Delay.ret A]ₛ) [idfun A]ₛ) [idfun (Delay A)]ₛ
  · gintro a
    gunfold comp
    gunfold idfun
    gsimpl
    grfl
  · gintro w
    gunfold idfun
    gsimpl
    grewrite (Delay.delay_eta A) w
    grfl
  grfl

gtheorem Delay.bind_assoc_free (A B C : TYPE) :
    ∀ k : (A → [Delay B]). ∀ g : (B → [Delay C]).
      ((([comp (Delay A) (Delay B) (Delay C)]ₛ ([Delay.bind B C]ₛ g)) ([Delay.bind A B]ₛ k))
        = [Delay.bind A C]ₛ (([comp A (Delay B) (Delay C)]ₛ ([Delay.bind B C]ₛ g)) k)) := by
  gintro k g
  grewrite (Delay.bind_eq_ext A C) (([comp A (Delay B) (Delay C)]ₛ ([Delay.bind B C]ₛ g)) k)
  gapply (Delay.ext_unique_pointfree _ _) [Delay.step C]ₛ
    (([comp A (Delay B) (Delay C)]ₛ ([Delay.bind B C]ₛ g)) k)
    (([comp (Delay A) (Delay B) (Delay C)]ₛ ([Delay.bind B C]ₛ g)) ([Delay.bind A B]ₛ k))
  · gintro a
    gunfold comp
    gsimpl
    grewrite (Delay.bind_ret_l A B) k a
    grfl
  · gintro w
    gunfold comp
    gsimpl
    grewrite (Delay.step_mk A) w
    grewrite (Delay.bind_step A B)
    grewrite (Delay.bind_step B C)
    grewrite (Delay.step_mk C)
    grfl

gtheorem Delay.map_comp_free (A B C : TYPE) :
    ∀ f : (A → B). ∀ g : (B → C).
      ((([comp (Delay A) (Delay B) (Delay C)]ₛ ([Delay.map B C]ₛ g)) ([Delay.map A B]ₛ f))
        = [Delay.map A C]ₛ (([comp A B C]ₛ g) f)) := by
  gintro f g
  grewrite (Delay.map_eq_ext A C) (([comp A B C]ₛ g) f)
  gapply (Delay.ext_unique_pointfree _ _) [Delay.step C]ₛ
    (([comp A C (Delay C)]ₛ [Delay.ret C]ₛ) (([comp A B C]ₛ g) f))
    (([comp (Delay A) (Delay B) (Delay C)]ₛ ([Delay.map B C]ₛ g)) ([Delay.map A B]ₛ f))
  · gintro a
    gunfold comp
    gsimpl
    grewrite (Delay.ret_mk A) a
    grewrite (Delay.map_ret A B)
    grewrite (Delay.map_ret B C)
    grewrite (Delay.ret_mk C)
    grfl
  · gintro w
    gunfold comp
    gsimpl
    grewrite (Delay.step_mk A) w
    grewrite (Delay.map_step A B)
    grewrite (Delay.map_step B C)
    grewrite (Delay.step_mk C)
    grfl

end derived_monad

end
