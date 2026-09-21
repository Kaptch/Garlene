module

public import SynthDom.Semantics.Fixpoint
public import SynthDom.Semantics.Logic
public import SynthDom.Syntax.Ty.Core

@[expose] public section

section ty
  open Logic
  open CategoryTheory
  open Opposite
  open Functor
  open CartesianMonoidalCategory
  open MonoidalCategory

  @[implicit_reducible]
  def interp_ty (τ : TYPE.{i}) : ℐ.{i} :=
    match τ with
    | TYPE.later τ => later.obj (interp_ty τ)
    | TYPE.arr τ₁ τ₂ => (ihom (interp_ty τ₁)).obj (interp_ty τ₂)
    | TYPE.prod τ₁ τ₂ => interp_ty τ₁ ⊗ interp_ty τ₂
    | TYPE.sum τ₁ τ₂ => ℐ.psum (interp_ty τ₁) (interp_ty τ₂)
    | TYPE.embed (A : Type (imax i 0)) => discrete.obj (ULift A)
    | TYPE.prop => subobject_classifier_psh.{i}
    | TYPE.ax t => t

  notation:max "⟦" e "⟧ₜ" => interp_ty e

end ty

section ctx
  open CategoryTheory
  open Opposite
  open Functor
  open CartesianMonoidalCategory
  open MonoidalCategory

  @[implicit_reducible]
  def interp_octx (Γ : OCTX.{i}) : ℐ.{i} :=
    match Γ with
    | .nil => 𝟙_ (ℐ.{i})
    | .cons τ Γ => interp_ty τ ⊗ interp_octx Γ

  notation:max "⟦" e "⟧ₒ" => interp_octx e

  @[implicit_reducible]
  def interp_ctx (Γs : CTX.{i}) : ℐ.{i} :=
    match Γs with
    | .nil => 𝟙_ (ℐ.{i})
    | .cons Γ Γs => interp_octx Γ ⊗ earlier.obj (interp_ctx Γs)

  notation:max "⟦" e "⟧ₛ" => interp_ctx e

end ctx
end
