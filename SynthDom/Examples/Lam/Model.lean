module

public import SynthDom
public import SynthDom.Examples.Utils.Funext
@[expose] public section

section dom
open CategoryTheory

gtype Dom := ν X. Δ Unit ⊕ Δ Unit ⊕ ▸X ⊕ ▸(X → X)

gdef Dom.unit : Dom :=
  [Dom.MK]ₛ (inl δ(() : Unit))

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

section dom_laws

gtheorem Dom.apply_unit :
    ∀ x : Dom. ((([Dom.apply]ₛ [Dom.unit]ₛ) x) = [Dom.error]ₛ) := by
  gintro x
  gunfold Dom.apply
  gfix
  gunfold Dom.unit
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
  gnext
  gadv h as h'
  gexact h'

end dom_laws

gtheorem Dom.apply_unit' :
    (([Dom.apply]ₛ [Dom.unit]ₛ) = (λ x. [Dom.error]ₛ)) := by
  gapply (gfunext _ _)
  gintro x
  gapply (Dom.apply_unit)

end dom

end
