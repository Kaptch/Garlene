module

public import SynthDom
public import SynthDom.Examples.Stream.Base
public import SynthDom.Examples.Utils.Funext
public import SynthDom.Examples.Utils.Denotation
@[expose] public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Logic

universe u

gdef Str.mapProg (A B : TYPE) (F : SYNT ⦃A → B⦄) : [Str A] → [Str B] :=
  [Str.map A B]ₛ [F]ₛ

section internal_laws

gtheorem Str.map_dup (A B : TYPE) :
    ∀ f : (A → B). ∀ s : [Str A].
      (([Str.dup B]ₛ (([Str.map A B]ₛ f) s))
        = ([Str.map (Str A) (Str B)]ₛ ([Str.map A B]ₛ f)) (([Str.dup A]ₛ s))) := by
  glöb IH
  gintro f s
  grewrite (Str.dup_cons B)
  grewrite (Str.map_tl A B)
  gsimpl
  grewrite (Str.dup_cons A)
  grewrite (Str.map_cons (Str A) (Str B))
  grewrite (Str.PROJ_MK (Str A))
  gsimpl
  gcong
  gmono IH as G
  gapply G

gtheorem Str.mapProg_ofHom_id (X : ℐ.{u}) :
    ([Str.mapProg (TYPE.ax X) (TYPE.ax X) (SYNT.ofHom (TYPE.ax X) (TYPE.ax X) (𝟙 X))]ₛ
      = [idfun (Str (TYPE.ax X))]ₛ) := by
  gunfold Str.mapProg
  grewrite (SYNT.eq_of_denoteHom (TYPE.ax X) (TYPE.ax X)
    (SYNT.ofHom (TYPE.ax X) (TYPE.ax X) (𝟙 X)) (idfun (TYPE.ax X))
    (by rw [denoteHom_ofHom, denoteHom_idfun]; rfl))
  gapply (Str.map_id' (TYPE.ax X))

gtheorem Str.mapProg_ofHom_comp (X Y Z : ℐ.{u}) (f : X ⟶ Y) (g : Y ⟶ Z) :
    ([SYNT.comp (Str (TYPE.ax X)) (Str (TYPE.ax Y)) (Str (TYPE.ax Z))
        (Str.mapProg (TYPE.ax X) (TYPE.ax Y) (SYNT.ofHom (TYPE.ax X) (TYPE.ax Y) f))
        (Str.mapProg (TYPE.ax Y) (TYPE.ax Z) (SYNT.ofHom (TYPE.ax Y) (TYPE.ax Z) g))]ₛ
      = [Str.mapProg (TYPE.ax X) (TYPE.ax Z) (SYNT.ofHom (TYPE.ax X) (TYPE.ax Z) (f ≫ g))]ₛ) := by
  gapply (gfunext _ _)
    [SYNT.comp (Str (TYPE.ax X)) (Str (TYPE.ax Y)) (Str (TYPE.ax Z))
      (Str.mapProg (TYPE.ax X) (TYPE.ax Y) (SYNT.ofHom (TYPE.ax X) (TYPE.ax Y) f))
      (Str.mapProg (TYPE.ax Y) (TYPE.ax Z) (SYNT.ofHom (TYPE.ax Y) (TYPE.ax Z) g))]ₛ
    [Str.mapProg (TYPE.ax X) (TYPE.ax Z) (SYNT.ofHom (TYPE.ax X) (TYPE.ax Z) (f ≫ g))]ₛ
  gintro x
  gunfold SYNT.comp
  gsimpl
  gunfold Str.mapProg
  grewrite (Str.map_comp (TYPE.ax X) (TYPE.ax Y) (TYPE.ax Z))
    [SYNT.ofHom (TYPE.ax X) (TYPE.ax Y) f]ₛ [SYNT.ofHom (TYPE.ax Y) (TYPE.ax Z) g]ₛ x
  gpose (SYNT.eq_of_denoteHom (TYPE.ax X) (TYPE.ax Z)
    (SYNT.comp (TYPE.ax X) (TYPE.ax Y) (TYPE.ax Z)
      (SYNT.ofHom (TYPE.ax X) (TYPE.ax Y) f) (SYNT.ofHom (TYPE.ax Y) (TYPE.ax Z) g))
    (SYNT.ofHom (TYPE.ax X) (TYPE.ax Z) (f ≫ g))
    (by rw [denoteHom_comp, denoteHom_ofHom, denoteHom_ofHom, denoteHom_ofHom])) as HC
  gunfold SYNT.comp at HC
  grewrite HC
  grfl

gtheorem Str.hd_ofHom_natural (X Y : ℐ.{u}) (f : X ⟶ Y) :
    ([SYNT.comp (Str (TYPE.ax X)) (Str (TYPE.ax Y)) (TYPE.ax Y)
        (Str.mapProg (TYPE.ax X) (TYPE.ax Y) (SYNT.ofHom (TYPE.ax X) (TYPE.ax Y) f))
        (Str.hd (TYPE.ax Y))]ₛ
      = [SYNT.comp (Str (TYPE.ax X)) (TYPE.ax X) (TYPE.ax Y)
          (Str.hd (TYPE.ax X)) (SYNT.ofHom (TYPE.ax X) (TYPE.ax Y) f)]ₛ) := by
  gapply (gfunext _ _)
    [SYNT.comp (Str (TYPE.ax X)) (Str (TYPE.ax Y)) (TYPE.ax Y)
      (Str.mapProg (TYPE.ax X) (TYPE.ax Y) (SYNT.ofHom (TYPE.ax X) (TYPE.ax Y) f))
      (Str.hd (TYPE.ax Y))]ₛ
    [SYNT.comp (Str (TYPE.ax X)) (TYPE.ax X) (TYPE.ax Y)
      (Str.hd (TYPE.ax X)) (SYNT.ofHom (TYPE.ax X) (TYPE.ax Y) f)]ₛ
  gintro x
  gunfold SYNT.comp
  gsimpl
  gunfold Str.mapProg
  gunfold Str.hd
  gsimpl
  gapply (Str.map_hd _ _) [SYNT.ofHom (TYPE.ax X) (TYPE.ax Y) f]ₛ x

gtheorem Str.dup_ofHom_natural (X Y : ℐ.{u}) (f : X ⟶ Y) :
    ([SYNT.comp (Str (TYPE.ax X)) (Str (TYPE.ax Y)) (Str (Str (TYPE.ax Y)))
        (Str.mapProg (TYPE.ax X) (TYPE.ax Y) (SYNT.ofHom (TYPE.ax X) (TYPE.ax Y) f))
        (Str.dup (TYPE.ax Y))]ₛ
      = [SYNT.comp (Str (TYPE.ax X)) (Str (Str (TYPE.ax X))) (Str (Str (TYPE.ax Y)))
          (Str.dup (TYPE.ax X))
          (Str.mapProg (Str (TYPE.ax X)) (Str (TYPE.ax Y))
            (Str.mapProg (TYPE.ax X) (TYPE.ax Y) (SYNT.ofHom (TYPE.ax X) (TYPE.ax Y) f)))]ₛ) := by
  gapply (gfunext _ _)
    [SYNT.comp (Str (TYPE.ax X)) (Str (TYPE.ax Y)) (Str (Str (TYPE.ax Y)))
      (Str.mapProg (TYPE.ax X) (TYPE.ax Y) (SYNT.ofHom (TYPE.ax X) (TYPE.ax Y) f))
      (Str.dup (TYPE.ax Y))]ₛ
    [SYNT.comp (Str (TYPE.ax X)) (Str (Str (TYPE.ax X))) (Str (Str (TYPE.ax Y)))
      (Str.dup (TYPE.ax X))
      (Str.mapProg (Str (TYPE.ax X)) (Str (TYPE.ax Y))
        (Str.mapProg (TYPE.ax X) (TYPE.ax Y) (SYNT.ofHom (TYPE.ax X) (TYPE.ax Y) f)))]ₛ
  gintro x
  gunfold SYNT.comp
  gsimpl
  gunfold Str.mapProg
  gapply (Str.map_dup _ _) [SYNT.ofHom (TYPE.ax X) (TYPE.ax Y) f]ₛ x

gtheorem Str.dup_hd (A : TYPE) :
    ([SYNT.comp (Str A) (Str (Str A)) (Str A) (Str.dup A) (Str.hd (Str A))]ₛ
      = [idfun (Str A)]ₛ) := by
  gapply (gfunext _ _)
    [SYNT.comp (Str A) (Str (Str A)) (Str A) (Str.dup A) (Str.hd (Str A))]ₛ
    [idfun (Str A)]ₛ
  gintro x
  gunfold SYNT.comp
  gsimpl
  gunfold Str.hd
  gunfold idfun
  gsimpl
  gapply (Str.extract_dup A) x

gtheorem Str.dup_map_hd (A : TYPE) :
    ([SYNT.comp (Str A) (Str (Str A)) (Str A)
        (Str.dup A) (Str.mapProg (Str A) A (Str.hd A))]ₛ = [idfun (Str A)]ₛ) := by
  gapply (gfunext _ _)
    [SYNT.comp (Str A) (Str (Str A)) (Str A)
      (Str.dup A) (Str.mapProg (Str A) A (Str.hd A))]ₛ
    [idfun (Str A)]ₛ
  gintro x
  gunfold SYNT.comp
  gsimpl
  gunfold Str.mapProg
  gunfold Str.hd
  gunfold idfun
  gsimpl
  gapply (Str.map_extract_dup A) x

gtheorem Str.dup_coassoc' (A : TYPE) :
    ([SYNT.comp (Str A) (Str (Str A)) (Str (Str (Str A)))
        (Str.dup A) (Str.mapProg (Str A) (Str (Str A)) (Str.dup A))]ₛ
      = [SYNT.comp (Str A) (Str (Str A)) (Str (Str (Str A)))
          (Str.dup A) (Str.dup (Str A))]ₛ) := by
  gapply (gfunext _ _)
    [SYNT.comp (Str A) (Str (Str A)) (Str (Str (Str A)))
      (Str.dup A) (Str.mapProg (Str A) (Str (Str A)) (Str.dup A))]ₛ
    [SYNT.comp (Str A) (Str (Str A)) (Str (Str (Str A)))
      (Str.dup A) (Str.dup (Str A))]ₛ
  gintro x
  gunfold SYNT.comp
  gsimpl
  gunfold Str.mapProg
  gapply (Str.dup_coassoc A) x

end internal_laws

section comonad_in_presheaves

unseal Str.mapProg in
theorem Str.denoteHom_mapProg_congr {σ τ : TYPE.{u}} {P Q : SYNT ⦃σ → τ⦄}
    (h : denoteHom P = denoteHom Q) :
    denoteHom (Str.mapProg σ τ P) = denoteHom (Str.mapProg σ τ Q) :=
  congrArg MonoidalClosed.uncurry' (globalElt_app_congr (Str.map σ τ)
    (globalElt_eq_of_denoteHom h))

unseal Str Str.code in
def STR.comonad : CategoryTheory.Comonad ℐ.{u} :=
  CategoryTheory.Comonad.mk
    { obj := fun X => (⟦Str (TYPE.ax X)⟧ₜ : ℐ.{u})
      map := fun {X Y} f =>
        denoteHom (Str.mapProg (TYPE.ax X) (TYPE.ax Y) (SYNT.ofHom (TYPE.ax X) (TYPE.ax Y) f))
      map_id := fun X => (denoteHom_of_goal (Str.mapProg_ofHom_id X)).trans (denoteHom_idfun _)
      map_comp := fun {X Y Z} f g => by
        have h := denoteHom_of_goal (Str.mapProg_ofHom_comp X Y Z f g)
        rw [denoteHom_comp] at h
        exact h.symm }
    { app := fun X => denoteHom (Str.hd (TYPE.ax X))
      naturality := fun X Y f => by
        have h := denoteHom_of_goal (Str.hd_ofHom_natural X Y f)
        rw [denoteHom_comp, denoteHom_comp, denoteHom_ofHom] at h
        exact h }
    { app := fun X => denoteHom (Str.dup (TYPE.ax X))
      naturality := fun X Y f => by
        have h := denoteHom_of_goal (Str.dup_ofHom_natural X Y f)
        rw [denoteHom_comp, denoteHom_comp] at h
        exact h.trans (congrArg (denoteHom (Str.dup (TYPE.ax X)) ≫ ·)
          (Str.denoteHom_mapProg_congr (denoteHom_ofHom _)).symm) }
    (fun X => by
      have h := denoteHom_of_goal (Str.dup_coassoc' (TYPE.ax X))
      rw [denoteHom_comp, denoteHom_comp] at h
      exact (congrArg (denoteHom (Str.dup (TYPE.ax X)) ≫ ·)
        (Str.denoteHom_mapProg_congr (denoteHom_ofHom _))).trans h)
    (fun X => by
      have h := denoteHom_of_goal (Str.dup_hd (TYPE.ax X))
      rw [denoteHom_comp] at h
      exact h.trans (denoteHom_idfun _))
    (fun X => by
      have h := denoteHom_of_goal (Str.dup_map_hd (TYPE.ax X))
      rw [denoteHom_comp] at h
      exact ((congrArg (denoteHom (Str.dup (TYPE.ax X)) ≫ ·)
        (Str.denoteHom_mapProg_congr (denoteHom_ofHom _))).trans h).trans (denoteHom_idfun _))

def STR : ℐ.{u} ⥤ ℐ.{u} := STR.comonad.toFunctor

end comonad_in_presheaves

section unfolding

gtheorem Str.mk_proj' (A : TYPE) :
    ([SYNT.comp (Str A) (TYPE.prod A (TYPE.later (Str A))) (Str A)
        (Str.PROJ A) (Str.MK A)]ₛ = [idfun (Str A)]ₛ) := by
  gapply (gfunext _ _)
    [SYNT.comp (Str A) (TYPE.prod A (TYPE.later (Str A))) (Str A)
      (Str.PROJ A) (Str.MK A)]ₛ
    [idfun (Str A)]ₛ
  gintro x
  gunfold SYNT.comp
  gsimpl
  gunfold idfun
  gsimpl
  gapply (Str.MK_PROJ A)

gtheorem Str.proj_mk' (A : TYPE) :
    ([SYNT.comp (TYPE.prod A (TYPE.later (Str A))) (Str A)
        (TYPE.prod A (TYPE.later (Str A))) (Str.MK A) (Str.PROJ A)]ₛ
      = [idfun (TYPE.prod A (TYPE.later (Str A)))]ₛ) := by
  gapply (gfunext _ _)
    [SYNT.comp (TYPE.prod A (TYPE.later (Str A))) (Str A)
      (TYPE.prod A (TYPE.later (Str A))) (Str.MK A) (Str.PROJ A)]ₛ
    [idfun (TYPE.prod A (TYPE.later (Str A)))]ₛ
  gintro x
  gunfold SYNT.comp
  gsimpl
  gunfold idfun
  gsimpl
  gapply (Str.PROJ_MK A)

def STR.unfoldIso (X : ℐ.{u}) :
    STR.obj X ≅ X ⊗ later.obj (STR.obj X) where
  hom := denoteHom (Str.PROJ (TYPE.ax X))
  inv := denoteHom (Str.MK (TYPE.ax X))
  hom_inv_id := by
    have h := denoteHom_of_goal (Str.mk_proj' (TYPE.ax X))
    rw [denoteHom_comp] at h
    exact h.trans (denoteHom_idfun _)
  inv_hom_id := by
    have h := denoteHom_of_goal (Str.proj_mk' (TYPE.ax X))
    rw [denoteHom_comp] at h
    exact h.trans (denoteHom_idfun _)

end unfolding

end
