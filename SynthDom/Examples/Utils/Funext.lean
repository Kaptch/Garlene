module

public import SynthDom
@[expose] public section

gtheorem gfunext (A B : TYPE) :
    ∀ f : (A → B). ∀ g : (A → B). ((∀ x : A. ((f x) = (g x))) → (f = g)) :=
  funext_sem.funext A B

gtheorem eta_pointfree (A B : TYPE) : ∀ f : (A → B). ((λ x : A. f x) = f) := by
  gintro f
  gapply (gfunext _ _) (λ x : A. f x) f
  gintro x
  grfl

gdef idfun (A : TYPE) : A → A := λ x. x

gdef comp (A B C : TYPE) : (B → C) → (A → B) → A → C :=
  λ g. λ f. λ x. g (f x)

gtheorem idfun_app (A : TYPE) : ∀ x : A. (([idfun A]ₛ x) = x) := by
  gintro x
  gunfold idfun
  gsimpl
  grfl

gtheorem comp_app (A B C : TYPE) : ∀ g : (B → C). ∀ f : (A → B). ∀ x : A.
    (((([comp A B C]ₛ g) f) x) = g (f x)) := by
  gintro g f x
  gunfold comp
  gsimpl
  grfl

end
