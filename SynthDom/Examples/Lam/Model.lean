module

public import SynthDom
public import SynthDom.Examples.Utils.Funext
@[expose] public section

section dom
open CategoryTheory

gtype Dom := ν X. Δ Nat ⊕ Δ Unit ⊕ ▸X ⊕ ▸(X → X)

gdef Dom.num (n : Nat) : Dom :=
  [Dom.MK]ₛ (inl δ(n : Nat))

gdef Dom.error : Dom :=
  [Dom.MK]ₛ (inr (inl δ(() : Unit)))

gdef Dom.thunk : ▸ Dom → Dom :=
  λ w. [Dom.MK]ₛ (inr (inr (inl w)))

gdef Dom.lam : ▸ (Dom → Dom) → Dom :=
  λ g. [Dom.MK]ₛ (inr (inr (inr g)))

gdef Dom.apply : Dom → Dom → Dom :=
  fix ap. λ f. λ x.
    case ([Dom.PROJ]ₛ f)
      (λ n. [Dom.error]ₛ)
      (λ r. case r
        (λ u. [Dom.error]ₛ)
        (λ r2. case r2
          (λ w. [Dom.MK]ₛ (inr (inr (inl (delay (((adv 1 ap) (adv 1 w)) x))))))
          (λ g. [Dom.MK]ₛ (inr (inr (inl (delay ((adv 1 g) x))))))))

gdef Dom.succ : Dom → Dom :=
  λ x. case ([Dom.PROJ]ₛ x)
    (λ n. [Dom.MK]ₛ (inl (δ(Nat.succ) ⊙ n)))
    (λ r. [Dom.error]ₛ)

gdef Dom.add : Dom → Dom → Dom :=
  λ x. λ y.
    case ([Dom.PROJ]ₛ x)
      (λ n. case ([Dom.PROJ]ₛ y)
        (λ m. [Dom.MK]ₛ (inl ((δ(Nat.add) ⊙ n) ⊙ m)))
        (λ r. [Dom.error]ₛ))
      (λ r. [Dom.error]ₛ)

gdef Dom.fixp : Dom → Dom :=
  fix F. λ g. ([Dom.apply]ₛ g) ([Dom.thunk]ₛ (delay ((adv 1 F) g)))

gdef Dom.plus : Dom → Dom → Dom :=
  fix a. λ x. λ y.
    case ([Dom.PROJ]ₛ x)
      (λ n. y)
      (λ r. case r
        (λ u. [Dom.error]ₛ)
        (λ r2. case r2
          (λ w. [Dom.thunk]ₛ (delay (((adv 1 a) (adv 1 w)) y)))
          (λ g. [Dom.error]ₛ)))

gdef Dom.mult : Dom → Dom → Dom :=
  fix m. λ x. λ y.
    case ([Dom.PROJ]ₛ x)
      (λ n. [Dom.num 0]ₛ)
      (λ r. case r
        (λ u. [Dom.error]ₛ)
        (λ r2. case r2
          (λ w. ([Dom.plus]ₛ y) ([Dom.thunk]ₛ (delay (((adv 1 m) (adv 1 w)) y))))
          (λ g. [Dom.error]ₛ)))

section dom_laws

gtheorem Dom.succ_num (n : Nat) :
    (([Dom.succ]ₛ ([Dom.num n]ₛ)) = [Dom.num (n + 1)]ₛ) := by
  gunfold Dom.succ
  gunfold Dom.num
  gsimpl
  grewrite (Dom.PROJ_MK)
  gsimpl
  grfl

gtheorem Dom.add_num (n m : Nat) :
    ((([Dom.add]ₛ ([Dom.num n]ₛ)) ([Dom.num m]ₛ)) = [Dom.num (n + m)]ₛ) := by
  gunfold Dom.add
  gunfold Dom.num
  gsimpl
  grewrite (Dom.PROJ_MK)
  gsimpl
  grewrite (Dom.PROJ_MK)
  gsimpl
  grfl

gtheorem Dom.apply_num (n : Nat) :
    ∀ x : Dom. ((([Dom.apply]ₛ ([Dom.num n]ₛ)) x) = [Dom.error]ₛ) := by
  gintro x
  gunfold Dom.apply
  gfix
  gunfold Dom.num
  grewrite (Dom.PROJ_MK)
  gsimpl
  grfl

gtheorem Dom.apply_lam :
    ∀ g : ▸ (Dom → Dom). ∀ x : Dom.
      ((([Dom.apply]ₛ ([Dom.lam]ₛ g)) x)
        = [Dom.thunk]ₛ (delay ((adv 1 g) x))) := by
  gintro g x
  gunfold Dom.apply
  gfix
  gunfold Dom.lam
  gsimpl
  grewrite (Dom.PROJ_MK)
  gsimpl
  gunfold Dom.thunk
  gsimpl
  grfl

gtheorem Dom.apply_thunk :
    ∀ w : ▸ Dom. ∀ x : Dom.
      ((([Dom.apply]ₛ ([Dom.thunk]ₛ w)) x)
        = [Dom.thunk]ₛ (delay ((([Dom.apply]ₛ (adv 1 w)) x)))) := by
  gintro w x
  gunfold Dom.apply
  gfix
  gunfold Dom.thunk
  gsimpl
  grewrite (Dom.PROJ_MK)
  gsimpl
  grfl

gtheorem Dom.apply_cong :
    ∀ f : Dom. ∀ f' : Dom. ∀ x : Dom. ∀ x' : Dom.
      ((f = f') → ((x = x') → ((([Dom.apply]ₛ f) x) = (([Dom.apply]ₛ f') x')))) := by
  gintro f f' x x' h1 h2
  grewrite h1
  grewrite h2
  grfl

gtheorem Dom.lam_delay_cong_fn :
    ∀ f : (Dom → Dom). ∀ f' : (Dom → Dom).
      ((f = f') → (([Dom.lam]ₛ (delay f)) = ([Dom.lam]ₛ (delay f')))) := by
  gintro f f' h
  gcong
  gnext
  gexact h

gtheorem Dom.thunk_delay_cong_tm :
    ∀ x : Dom. ∀ x' : Dom.
      ((x = x') → (([Dom.thunk]ₛ (delay x)) = ([Dom.thunk]ₛ (delay x')))) := by
  gintro x x' h
  gcong
  gnext
  gexact h

gtheorem Dom.thunk_delay_cong_tm_later :
    ∀ x : Dom. ∀ x' : Dom.
      ((lift (delay (x = x'))) → (([Dom.thunk]ₛ (delay x)) = ([Dom.thunk]ₛ (delay x')))) := by
  gintro x x' h
  gcong
  gmono h as h'
  gexact h'

gtheorem Dom.fixp_unfold :
    ∀ g : Dom.
      (([Dom.fixp]ₛ g)
        = ([Dom.apply]ₛ g) ([Dom.thunk]ₛ (delay ([Dom.fixp]ₛ g)))) := by
  gintro g
  gunfold Dom.fixp
  gfix
  grfl

gtheorem Dom.plus_zero :
    ∀ y : Dom. ((([Dom.plus]ₛ ([Dom.num 0]ₛ)) y) = y) := by
  gintro y
  gunfold Dom.plus
  gfix
  gunfold Dom.num
  grewrite (Dom.PROJ_MK)
  gsimpl
  grfl

gtheorem Dom.plus_succ :
    ∀ w : ▸ Dom. ∀ y : Dom.
      ((([Dom.plus]ₛ ([Dom.thunk]ₛ w)) y)
        = [Dom.thunk]ₛ (delay (([Dom.plus]ₛ (adv 1 w)) y))) := by
  gintro w y
  gunfold Dom.plus
  gfix
  gunfold Dom.thunk
  gsimpl
  grewrite (Dom.PROJ_MK)
  gsimpl
  grfl

gtheorem Dom.mult_zero :
    ∀ y : Dom. ((([Dom.mult]ₛ ([Dom.num 0]ₛ)) y) = [Dom.num 0]ₛ) := by
  gintro y
  gunfold Dom.mult
  gfix
  gunfold Dom.num
  grewrite (Dom.PROJ_MK)
  gsimpl
  grfl

gtheorem Dom.mult_succ :
    ∀ w : ▸ Dom. ∀ y : Dom.
      ((([Dom.mult]ₛ ([Dom.thunk]ₛ w)) y)
        = ([Dom.plus]ₛ y) ([Dom.thunk]ₛ (delay (([Dom.mult]ₛ (adv 1 w)) y)))) := by
  gintro w y
  gunfold Dom.mult
  gfix
  gunfold Dom.thunk
  gsimpl
  grewrite (Dom.PROJ_MK)
  gsimpl
  grfl

end dom_laws

gtheorem Dom.apply_num' (n : Nat) :
    (([Dom.apply]ₛ ([Dom.num n]ₛ)) = (λ x. [Dom.error]ₛ)) := by
  gapply (gfunext _ _)
  gintro x
  gapply (Dom.apply_num n)

end dom

end
