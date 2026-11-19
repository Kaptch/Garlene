module

public import SynthDom
public import SynthDom.Examples.Delay.Base
public import SynthDom.Examples.Utils.Funext
public import SynthDom.Examples.Delay.Algebra
public import SynthDom.Examples.Stream.Commute
public import SynthDom.Examples.Utils.Denotation
@[expose] public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Logic

universe u

section delay_programs

gdef Delay.mapProg (A B : TYPE) (F : SYNT ⦃A → B⦄) : [Delay A] → [Delay B] :=
  [Delay.map A B]ₛ [F]ₛ

gdef Delay.join (A : TYPE) : [Delay (Delay A)] → [Delay A] :=
  [Delay.bind (Delay A) A]ₛ [idfun (Delay A)]ₛ

end delay_programs

section functor_laws

gtheorem Delay.mapProg_ofHom_id (X : ℐ.{u}) :
    ([Delay.mapProg (TYPE.ax X) (TYPE.ax X) (SYNT.ofHom (TYPE.ax X) (TYPE.ax X) (𝟙 X))]ₛ
      = [idfun (Delay (TYPE.ax X))]ₛ) := by
  gunfold Delay.mapProg
  grewrite (SYNT.eq_of_denoteHom (TYPE.ax X) (TYPE.ax X) (SYNT.ofHom (TYPE.ax X) (TYPE.ax X) (𝟙 X)) (idfun (TYPE.ax X))
    (by rw [denoteHom_ofHom, denoteHom_idfun]; rfl))
  gapply (Delay.map_id' (TYPE.ax X))

gtheorem Delay.mapProg_ofHom_comp (X Y Z : ℐ.{u}) (f : X ⟶ Y) (g : Y ⟶ Z) :
    ([SYNT.comp (Delay (TYPE.ax X)) (Delay (TYPE.ax Y)) (Delay (TYPE.ax Z))
        (Delay.mapProg (TYPE.ax X) (TYPE.ax Y) (SYNT.ofHom (TYPE.ax X) (TYPE.ax Y) f))
        (Delay.mapProg (TYPE.ax Y) (TYPE.ax Z) (SYNT.ofHom (TYPE.ax Y) (TYPE.ax Z) g))]ₛ
      = [Delay.mapProg (TYPE.ax X) (TYPE.ax Z) (SYNT.ofHom (TYPE.ax X) (TYPE.ax Z) (f ≫ g))]ₛ) := by
  gapply (gfunext _ _)
    [SYNT.comp (Delay (TYPE.ax X)) (Delay (TYPE.ax Y)) (Delay (TYPE.ax Z))
      (Delay.mapProg (TYPE.ax X) (TYPE.ax Y) (SYNT.ofHom (TYPE.ax X) (TYPE.ax Y) f))
      (Delay.mapProg (TYPE.ax Y) (TYPE.ax Z) (SYNT.ofHom (TYPE.ax Y) (TYPE.ax Z) g))]ₛ
    [Delay.mapProg (TYPE.ax X) (TYPE.ax Z) (SYNT.ofHom (TYPE.ax X) (TYPE.ax Z) (f ≫ g))]ₛ
  gintro x
  gunfold SYNT.comp
  gsimpl
  gunfold Delay.mapProg
  grewrite (Delay.map_comp (TYPE.ax X) (TYPE.ax Y) (TYPE.ax Z)) [SYNT.ofHom (TYPE.ax X) (TYPE.ax Y) f]ₛ [SYNT.ofHom (TYPE.ax Y) (TYPE.ax Z) g]ₛ x
  gpose (SYNT.eq_of_denoteHom (TYPE.ax X) (TYPE.ax Z)
    (SYNT.comp (TYPE.ax X) (TYPE.ax Y) (TYPE.ax Z) (SYNT.ofHom (TYPE.ax X) (TYPE.ax Y) f) (SYNT.ofHom (TYPE.ax Y) (TYPE.ax Z) g))
    (SYNT.ofHom (TYPE.ax X) (TYPE.ax Z) (f ≫ g))
    (by rw [denoteHom_comp, denoteHom_ofHom, denoteHom_ofHom, denoteHom_ofHom])) as HC
  gunfold SYNT.comp at HC
  grewrite HC
  grfl

end functor_laws

section monad_laws

gtheorem Delay.ret_ofHom_natural (X Y : ℐ.{u}) (f : X ⟶ Y) :
    ([SYNT.comp (TYPE.ax X) (TYPE.ax Y) (Delay (TYPE.ax Y))
        (SYNT.ofHom (TYPE.ax X) (TYPE.ax Y) f) (Delay.ret (TYPE.ax Y))]ₛ
      = [SYNT.comp (TYPE.ax X) (Delay (TYPE.ax X)) (Delay (TYPE.ax Y))
          (Delay.ret (TYPE.ax X)) (Delay.mapProg (TYPE.ax X) (TYPE.ax Y) (SYNT.ofHom (TYPE.ax X) (TYPE.ax Y) f))]ₛ) := by
  gapply (gfunext _ _)
    [SYNT.comp (TYPE.ax X) (TYPE.ax Y) (Delay (TYPE.ax Y))
      (SYNT.ofHom (TYPE.ax X) (TYPE.ax Y) f) (Delay.ret (TYPE.ax Y))]ₛ
    [SYNT.comp (TYPE.ax X) (Delay (TYPE.ax X)) (Delay (TYPE.ax Y))
      (Delay.ret (TYPE.ax X)) (Delay.mapProg (TYPE.ax X) (TYPE.ax Y) (SYNT.ofHom (TYPE.ax X) (TYPE.ax Y) f))]ₛ
  gintro x
  gunfold SYNT.comp
  gsimpl
  gunfold Delay.mapProg
  grewrite (Delay.ret_mk (TYPE.ax X)) x
  grewrite (Delay.map_ret (TYPE.ax X) (TYPE.ax Y))
  grewrite (Delay.ret_mk (TYPE.ax Y))
  grfl

gtheorem Delay.join_natural (X Y : ℐ.{u}) (f : X ⟶ Y) :
    ([SYNT.comp (Delay (Delay (TYPE.ax X))) (Delay (Delay (TYPE.ax Y))) (Delay (TYPE.ax Y))
        (Delay.mapProg (Delay (TYPE.ax X)) (Delay (TYPE.ax Y))
          (Delay.mapProg (TYPE.ax X) (TYPE.ax Y) (SYNT.ofHom (TYPE.ax X) (TYPE.ax Y) f)))
        (Delay.join (TYPE.ax Y))]ₛ
      = [SYNT.comp (Delay (Delay (TYPE.ax X))) (Delay (TYPE.ax X)) (Delay (TYPE.ax Y))
          (Delay.join (TYPE.ax X))
          (Delay.mapProg (TYPE.ax X) (TYPE.ax Y) (SYNT.ofHom (TYPE.ax X) (TYPE.ax Y) f))]ₛ) := by
  gapply (gfunext _ _)
    [SYNT.comp (Delay (Delay (TYPE.ax X))) (Delay (Delay (TYPE.ax Y))) (Delay (TYPE.ax Y))
      (Delay.mapProg (Delay (TYPE.ax X)) (Delay (TYPE.ax Y))
        (Delay.mapProg (TYPE.ax X) (TYPE.ax Y) (SYNT.ofHom (TYPE.ax X) (TYPE.ax Y) f)))
      (Delay.join (TYPE.ax Y))]ₛ
    [SYNT.comp (Delay (Delay (TYPE.ax X))) (Delay (TYPE.ax X)) (Delay (TYPE.ax Y))
      (Delay.join (TYPE.ax X))
      (Delay.mapProg (TYPE.ax X) (TYPE.ax Y) (SYNT.ofHom (TYPE.ax X) (TYPE.ax Y) f))]ₛ
  gintro x
  gunfold SYNT.comp
  gsimpl
  gunfold Delay.mapProg
  gunfold Delay.join
  grewrite (Delay.bind_map (Delay (TYPE.ax X)) (Delay (TYPE.ax Y)) (TYPE.ax Y))
    ([Delay.map (TYPE.ax X) (TYPE.ax Y)]ₛ [SYNT.ofHom (TYPE.ax X) (TYPE.ax Y) f]ₛ)
    [idfun (Delay (TYPE.ax Y))]ₛ x
  grewrite (Delay.map_bind (Delay (TYPE.ax X)) (TYPE.ax X) (TYPE.ax Y))
    [idfun (Delay (TYPE.ax X))]ₛ [SYNT.ofHom (TYPE.ax X) (TYPE.ax Y) f]ₛ x
  gassert HFN of ((λ x : [Delay (TYPE.ax X)]. [idfun (Delay (TYPE.ax Y))]ₛ
        (([Delay.map (TYPE.ax X) (TYPE.ax Y)]ₛ [SYNT.ofHom (TYPE.ax X) (TYPE.ax Y) f]ₛ) x))
      = (λ x : [Delay (TYPE.ax X)]. ([Delay.map (TYPE.ax X) (TYPE.ax Y)]ₛ
          [SYNT.ofHom (TYPE.ax X) (TYPE.ax Y) f]ₛ) ([idfun (Delay (TYPE.ax X))]ₛ x)))
  · gapply (gfunext _ _)
      (λ x : [Delay (TYPE.ax X)]. [idfun (Delay (TYPE.ax Y))]ₛ
        (([Delay.map (TYPE.ax X) (TYPE.ax Y)]ₛ [SYNT.ofHom (TYPE.ax X) (TYPE.ax Y) f]ₛ) x))
      (λ x : [Delay (TYPE.ax X)]. ([Delay.map (TYPE.ax X) (TYPE.ax Y)]ₛ
        [SYNT.ofHom (TYPE.ax X) (TYPE.ax Y) f]ₛ) ([idfun (Delay (TYPE.ax X))]ₛ x))
    gintro x
    gunfold idfun
    gsimpl
    grfl
  grewrite HFN
  grfl

gtheorem Delay.join_ret (A : TYPE) :
    ([SYNT.comp (Delay A) (Delay (Delay A)) (Delay A)
        (Delay.ret (Delay A)) (Delay.join A)]ₛ = [idfun (Delay A)]ₛ) := by
  gapply (gfunext _ _)
    [SYNT.comp (Delay A) (Delay (Delay A)) (Delay A) (Delay.ret (Delay A)) (Delay.join A)]ₛ
    [idfun (Delay A)]ₛ
  gintro x
  gunfold SYNT.comp
  gsimpl
  gunfold Delay.join
  grewrite (Delay.bind_ret_l (Delay A) A) [idfun (Delay A)]ₛ x
  grfl

gtheorem Delay.join_map_ret (A : TYPE) :
    ([SYNT.comp (Delay A) (Delay (Delay A)) (Delay A)
        (Delay.mapProg A (Delay A) (Delay.ret A)) (Delay.join A)]ₛ
      = [idfun (Delay A)]ₛ) := by
  gapply (gfunext _ _)
    [SYNT.comp (Delay A) (Delay (Delay A)) (Delay A)
      (Delay.mapProg A (Delay A) (Delay.ret A)) (Delay.join A)]ₛ
    [idfun (Delay A)]ₛ
  gintro x
  gunfold SYNT.comp
  gsimpl
  gunfold Delay.join
  gunfold Delay.mapProg
  grewrite (Delay.bind_map A (Delay A) A) [Delay.ret A]ₛ [idfun (Delay A)]ₛ x
  gassert HFN of ((λ x : A. [idfun (Delay A)]ₛ ([Delay.ret A]ₛ x)) = [Delay.ret A]ₛ)
  · gapply (gfunext _ _)
      (λ x : A. [idfun (Delay A)]ₛ ([Delay.ret A]ₛ x)) [Delay.ret A]ₛ
    gintro x
    gunfold idfun
    gsimpl
    grfl
  grewrite HFN
  grewrite (Delay.bind_ret_r' A)
  grfl

gtheorem Delay.join_assoc (A : TYPE) :
    ([SYNT.comp (Delay (Delay (Delay A))) (Delay (Delay A)) (Delay A)
        (Delay.mapProg (Delay (Delay A)) (Delay A) (Delay.join A)) (Delay.join A)]ₛ
      = [SYNT.comp (Delay (Delay (Delay A))) (Delay (Delay A)) (Delay A)
          (Delay.join (Delay A)) (Delay.join A)]ₛ) := by
  gapply (gfunext _ _)
    [SYNT.comp (Delay (Delay (Delay A))) (Delay (Delay A)) (Delay A)
      (Delay.mapProg (Delay (Delay A)) (Delay A) (Delay.join A)) (Delay.join A)]ₛ
    [SYNT.comp (Delay (Delay (Delay A))) (Delay (Delay A)) (Delay A)
      (Delay.join (Delay A)) (Delay.join A)]ₛ
  gintro x
  gunfold SYNT.comp
  gsimpl
  gunfold Delay.mapProg
  gunfold Delay.join
  grewrite (Delay.bind_map (Delay (Delay A)) (Delay A) A)
    ([Delay.bind (Delay A) A]ₛ [idfun (Delay A)]ₛ) [idfun (Delay A)]ₛ x
  grewrite (Delay.bind_assoc (Delay (Delay A)) (Delay A) A)
    [idfun (Delay (Delay A))]ₛ [idfun (Delay A)]ₛ x
  gassert HFN1 of ((λ x : [Delay (Delay A)].
        [idfun (Delay A)]ₛ (([Delay.bind (Delay A) A]ₛ [idfun (Delay A)]ₛ) x))
      = ([Delay.bind (Delay A) A]ₛ [idfun (Delay A)]ₛ))
  · gapply (gfunext _ _)
      (λ x : [Delay (Delay A)].
        [idfun (Delay A)]ₛ (([Delay.bind (Delay A) A]ₛ [idfun (Delay A)]ₛ) x))
      ([Delay.bind (Delay A) A]ₛ [idfun (Delay A)]ₛ)
    gintro x
    gunfold idfun
    gsimpl
    grfl
  gassert HFN2 of ((λ a : [Delay (Delay A)].
        ([Delay.bind (Delay A) A]ₛ [idfun (Delay A)]ₛ) ([idfun (Delay (Delay A))]ₛ a))
      = ([Delay.bind (Delay A) A]ₛ [idfun (Delay A)]ₛ))
  · gapply (gfunext _ _)
      (λ a : [Delay (Delay A)].
        ([Delay.bind (Delay A) A]ₛ [idfun (Delay A)]ₛ) ([idfun (Delay (Delay A))]ₛ a))
      ([Delay.bind (Delay A) A]ₛ [idfun (Delay A)]ₛ)
    gintro a
    gunfold idfun
    gsimpl
    grfl
  grewrite HFN1
  grewrite HFN2
  grfl

end monad_laws

section monad_in_presheaves

unseal Delay.mapProg in
theorem Delay.denoteHom_mapProg_congr {σ τ : TYPE.{u}} {P Q : SYNT ⦃σ → τ⦄}
    (h : denoteHom P = denoteHom Q) :
    denoteHom (Delay.mapProg σ τ P) = denoteHom (Delay.mapProg σ τ Q) :=
  congrArg MonoidalClosed.uncurry' (globalElt_app_congr (Delay.map σ τ)
    (globalElt_eq_of_denoteHom h))

unseal Delay Delay.code in
def DELAY.monad : CategoryTheory.Monad ℐ.{u} where
  obj X := (⟦Delay (TYPE.ax X)⟧ₜ : ℐ.{u})
  map {X Y} f :=
    denoteHom (Delay.mapProg (TYPE.ax X) (TYPE.ax Y) (SYNT.ofHom (TYPE.ax X) (TYPE.ax Y) f))
  map_id X := (denoteHom_of_goal (Delay.mapProg_ofHom_id X)).trans (denoteHom_idfun _)
  map_comp {X Y Z} f g := by
    have h := denoteHom_of_goal (Delay.mapProg_ofHom_comp X Y Z f g)
    rw [denoteHom_comp] at h
    exact h.symm
  η :=
    { app := fun X => denoteHom (Delay.ret (TYPE.ax X))
      naturality := fun X Y f => by
        have h := denoteHom_of_goal (Delay.ret_ofHom_natural X Y f)
        rw [denoteHom_comp, denoteHom_comp, denoteHom_ofHom] at h
        exact h }
  μ :=
    { app := fun X => denoteHom (Delay.join (TYPE.ax X))
      naturality := fun X Y f => by
        have h := denoteHom_of_goal (Delay.join_natural X Y f)
        rw [denoteHom_comp, denoteHom_comp] at h
        exact (congrArg (· ≫ denoteHom (Delay.join (TYPE.ax Y)))
          (Delay.denoteHom_mapProg_congr (denoteHom_ofHom _))).trans h }
  left_unit X := by
    have h := denoteHom_of_goal (Delay.join_ret (TYPE.ax X))
    rw [denoteHom_comp] at h
    exact h.trans (denoteHom_idfun _)
  right_unit X := by
    have h := denoteHom_of_goal (Delay.join_map_ret (TYPE.ax X))
    rw [denoteHom_comp] at h
    exact ((congrArg (· ≫ denoteHom (Delay.join (TYPE.ax X)))
      (Delay.denoteHom_mapProg_congr (denoteHom_ofHom _))).trans h).trans (denoteHom_idfun _)
  assoc X := by
    have h := denoteHom_of_goal (Delay.join_assoc (TYPE.ax X))
    rw [denoteHom_comp, denoteHom_comp] at h
    exact (congrArg (· ≫ denoteHom (Delay.join (TYPE.ax X)))
      (Delay.denoteHom_mapProg_congr (denoteHom_ofHom _))).trans h

def DELAY : ℐ.{u} ⥤ ℐ.{u} := DELAY.monad.toFunctor

end monad_in_presheaves

section unfolding

gtheorem Delay.mk_proj' (A : TYPE) :
    ([SYNT.comp (Delay A) (TYPE.sum A (TYPE.later (Delay A))) (Delay A)
        (Delay.PROJ A) (Delay.MK A)]ₛ = [idfun (Delay A)]ₛ) := by
  gapply (gfunext _ _)
    [SYNT.comp (Delay A) (TYPE.sum A (TYPE.later (Delay A))) (Delay A)
      (Delay.PROJ A) (Delay.MK A)]ₛ
    [idfun (Delay A)]ₛ
  gintro x
  gunfold SYNT.comp
  gsimpl
  gunfold idfun
  gsimpl
  gapply (Delay.MK_PROJ A)

gtheorem Delay.proj_mk' (A : TYPE) :
    ([SYNT.comp (TYPE.sum A (TYPE.later (Delay A))) (Delay A)
        (TYPE.sum A (TYPE.later (Delay A))) (Delay.MK A) (Delay.PROJ A)]ₛ
      = [idfun (TYPE.sum A (TYPE.later (Delay A)))]ₛ) := by
  gapply (gfunext _ _)
    [SYNT.comp (TYPE.sum A (TYPE.later (Delay A))) (Delay A)
      (TYPE.sum A (TYPE.later (Delay A))) (Delay.MK A) (Delay.PROJ A)]ₛ
    [idfun (TYPE.sum A (TYPE.later (Delay A)))]ₛ
  gintro x
  gunfold SYNT.comp
  gsimpl
  gunfold idfun
  gsimpl
  gapply (Delay.PROJ_MK A)

def DELAY.unfoldIso (X : ℐ.{u}) :
    DELAY.obj X ≅ ℐ.psum X (later.obj (DELAY.obj X)) where
  hom := denoteHom (Delay.PROJ (TYPE.ax X))
  inv := denoteHom (Delay.MK (TYPE.ax X))
  hom_inv_id := by
    have h := denoteHom_of_goal (Delay.mk_proj' (TYPE.ax X))
    rw [denoteHom_comp] at h
    exact h.trans (denoteHom_idfun _)
  inv_hom_id := by
    have h := denoteHom_of_goal (Delay.proj_mk' (TYPE.ax X))
    rw [denoteHom_comp] at h
    exact h.trans (denoteHom_idfun _)

end unfolding

end
