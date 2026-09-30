module

public import SynthDom
public import SynthDom.Examples.Utils.Funext
@[expose] public section

section dom
open CategoryTheory

gdef Dom.code : UNIV :=
  fix X. [UNIV.SUM]ₛ ⟨[UNIV.DISCRETE (ULift Nat)]ₛ,
    [UNIV.SUM]ₛ ⟨[UNIV.DISCRETE (ULift Unit)]ₛ, [UNIV.SUM]ₛ ⟨[UNIV.LATER]ₛ X,
      [UNIV.LATER]ₛ (delay ([UNIV.ARR]ₛ ⟨adv 1 X, adv 1 X⟩))⟩⟩⟩

def Dom : TYPE := El (Dom.code)

gtheorem Dom.unfold_code :
    ([Dom.code]ₛ = [UNIV.sum (UNIV.DISCRETE (ULift Nat)) (UNIV.sum (UNIV.DISCRETE (ULift Unit))
      (UNIV.sum (UNIV.later Dom.code) (UNIV.later (UNIV.arr Dom.code Dom.code))))]ₛ) := by
  gunfold Dom.code
  gfix
  grfl

theorem Dom.eq : ⟦Dom⟧ₜ = ⟦⦃Δ Nat ⊕ Δ Unit ⊕ ▸ Dom ⊕ ▸ (Dom → Dom)⦄⟧ₜ :=
  DECODES_of_goal (Dom.unfold_code)
    (DECODES_sum (DECODES_DISCRETE _) (DECODES_sum (DECODES_DISCRETE _)
      (DECODES_sum (DECODES_later (DECODES_refl _))
        (DECODES_later (DECODES_arr (DECODES_refl _) (DECODES_refl _))))))

def Dom.fold := GTY.fold (Dom.eq)
def Dom.unfold := GTY.unfold (Dom.eq)

theorem Dom.fold_unfold :
    ⊢ᵍ ⟪∀ x : Dom. ([Dom.fold]ₛ ([Dom.unfold]ₛ x)) = x⟫ :=
  GTY.fold_unfold (Dom.eq)
theorem Dom.unfold_fold :
    ⊢ᵍ ⟪∀ x : (Δ Nat ⊕ Δ Unit ⊕ ▸ Dom ⊕ ▸ (Dom → Dom)). ([Dom.unfold]ₛ ([Dom.fold]ₛ x)) = x⟫ :=
  GTY.unfold_fold (Dom.eq)

attribute [irreducible] Dom

gdef Dom.num (n : Nat) : Dom :=
  [Dom.fold]ₛ (inl δ(n : Nat))

gdef Dom.error : Dom :=
  [Dom.fold]ₛ (inr (inl δ(() : Unit)))

gdef Dom.thunk : ▸ Dom → Dom :=
  λ w. [Dom.fold]ₛ (inr (inr (inl w)))

gdef Dom.lam : ▸ (Dom → Dom) → Dom :=
  λ g. [Dom.fold]ₛ (inr (inr (inr g)))

gdef Dom.apply : Dom → Dom → Dom :=
  fix ap. λ f. λ x.
    case ([Dom.unfold]ₛ f)
      (λ n. [Dom.error]ₛ)
      (λ r. case r
        (λ u. [Dom.error]ₛ)
        (λ r2. case r2
          (λ w. [Dom.fold]ₛ (inr (inr (inl (delay (((adv 1 ap) (adv 1 w)) x))))))
          (λ g. [Dom.fold]ₛ (inr (inr (inl (delay ((adv 1 g) x))))))))

gdef Dom.succ : Dom → Dom :=
  λ x. case ([Dom.unfold]ₛ x)
    (λ n. [Dom.fold]ₛ (inl (δ(Nat.succ) ⊙ n)))
    (λ r. [Dom.error]ₛ)

gdef Dom.add : Dom → Dom → Dom :=
  λ x. λ y.
    case ([Dom.unfold]ₛ x)
      (λ n. case ([Dom.unfold]ₛ y)
        (λ m. [Dom.fold]ₛ (inl ((δ(Nat.add) ⊙ n) ⊙ m)))
        (λ r. [Dom.error]ₛ))
      (λ r. [Dom.error]ₛ)

gdef Dom.fixp : Dom → Dom :=
  fix F. λ g. ([Dom.apply]ₛ g) ([Dom.thunk]ₛ (delay ((adv 1 F) g)))

gdef Dom.plus : Dom → Dom → Dom :=
  fix a. λ x. λ y.
    case ([Dom.unfold]ₛ x)
      (λ n. y)
      (λ r. case r
        (λ u. [Dom.error]ₛ)
        (λ r2. case r2
          (λ w. [Dom.thunk]ₛ (delay (((adv 1 a) (adv 1 w)) y)))
          (λ g. [Dom.error]ₛ)))

gdef Dom.mult : Dom → Dom → Dom :=
  fix m. λ x. λ y.
    case ([Dom.unfold]ₛ x)
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
  grewrite (Dom.unfold_fold)
  gsimpl
  grfl

gtheorem Dom.add_num (n m : Nat) :
    ((([Dom.add]ₛ ([Dom.num n]ₛ)) ([Dom.num m]ₛ)) = [Dom.num (n + m)]ₛ) := by
  gunfold Dom.add
  gunfold Dom.num
  gsimpl
  grewrite (Dom.unfold_fold)
  gsimpl
  grewrite (Dom.unfold_fold)
  gsimpl
  grfl

gtheorem Dom.apply_num (n : Nat) :
    ∀ x : Dom. ((([Dom.apply]ₛ ([Dom.num n]ₛ)) x) = [Dom.error]ₛ) := by
  gintro x
  gunfold Dom.apply
  gfix
  gunfold Dom.num
  grewrite (Dom.unfold_fold)
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
  grewrite (Dom.unfold_fold)
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
  grewrite (Dom.unfold_fold)
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
  grewrite (Dom.unfold_fold)
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
  grewrite (Dom.unfold_fold)
  gsimpl
  grfl

gtheorem Dom.mult_zero :
    ∀ y : Dom. ((([Dom.mult]ₛ ([Dom.num 0]ₛ)) y) = [Dom.num 0]ₛ) := by
  gintro y
  gunfold Dom.mult
  gfix
  gunfold Dom.num
  grewrite (Dom.unfold_fold)
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
  grewrite (Dom.unfold_fold)
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
