module

public import Lean
public import SynthDom.Syntax
public import SynthDom.Interp.GuardedType
@[expose] public meta section

/-!
`gtype N bs := ν X. F` declares the guarded recursive type `N` with `N ≅ F[N]`.
It expands into ordinary declarations:

- `N.code : SYNT ⦃UNIV⦄`, the code `fix X. F̂` (a `gdef`),
- `N : TYPE`, the type decoded from `N.code`,
- `N.unfold_code`, the unfolding of the code (a `gtheorem`),
- `N.eq : ⟦N⟧ₜ = ⟦F[N]⟧ₜ`,
- `N.MK`, `N.PROJ` and the inverse laws `N.MK_PROJ`, `N.PROJ_MK`.

The body uses `[τ]`, `Δ T`, `×`, `⊕`, `→` and `▸`; `X` may occur only under `▸`.
-/

open Lean Elab Command

syntax "gtype " ident (ppSpace bracketedBinder)* " := " "ν " ident ". " type_lang : command

namespace GuardedType

/-- The translations of a type body. -/
structure Out where
  /-- the code, with the recursion variable bound by `fix` -/
  code : TSyntax `term_lang
  /-- the unfolded code, as a closed `SYNT ⦃UNIV⦄` -/
  nf : Term
  /-- `DECODES nf F[N]` -/
  dec : Term
  /-- the unfolded type `F[N]` -/
  ty : TSyntax `type_lang

/-- Translate the body; `codeN` and `tyN` stand for `N.code` and `N`, and `guarded` records
whether we are under `▸`. -/
partial def translate (X : Name) (codeN tyN : Term) (guarded : Bool) :
    TSyntax `type_lang → CommandElabM Out
  | `(type_lang| ($b)) => translate X codeN tyN guarded b
  | `(type_lang| $x:ident) =>
    if x.getId != X then leaf x
    else if guarded then
      return ⟨← `(term_lang| adv 1 $x:ident), codeN, ← `(DECODES_refl _), ← `(type_lang| [$tyN])⟩
    else throwErrorAt x "the recursion variable {x} must occur under ▸"
  | `(type_lang| [$t]) => leaf t
  | `(type_lang| Δ $t) => return ⟨← `(term_lang| [UNIV.DISCRETE (ULift $t)]ₛ),
      ← `(UNIV.DISCRETE (ULift $t)), ← `(DECODES_DISCRETE _), ← `(type_lang| Δ $t)⟩
  | `(type_lang| ▸ $b) => do
    let b ← translate X codeN tyN true b
    return ⟨← `(term_lang| [UNIV.LATER]ₛ (delay $(b.code))), ← `(UNIV.later $(b.nf)),
      ← `(DECODES_later $(b.dec)), ← `(type_lang| ▸ $(b.ty))⟩
  | `(type_lang| $a × $b) => do
    let (a, b) ← both a b
    binary (← `(UNIV.PROD)) (← `(UNIV.prod)) (← `(DECODES_prod)) a b
      (← `(type_lang| ($(a.ty) × $(b.ty))))
  | `(type_lang| $a ⊕ $b) => do
    let (a, b) ← both a b
    binary (← `(UNIV.SUM)) (← `(UNIV.sum)) (← `(DECODES_sum)) a b
      (← `(type_lang| ($(a.ty) ⊕ $(b.ty))))
  | `(type_lang| $a → $b) => do
    let (a, b) ← both a b
    binary (← `(UNIV.ARR)) (← `(UNIV.arr)) (← `(DECODES_arr)) a b
      (← `(type_lang| ($(a.ty) → $(b.ty))))
  | stx => throwErrorAt stx "unsupported former in a guarded type body"
where
  leaf (t : Term) : CommandElabM Out := do
    return ⟨← `(term_lang| [UNIV.CODE $t]ₛ), ← `(UNIV.CODE $t), ← `(DECODES_CODE $t),
      ← `(type_lang| [$t])⟩
  both (a b : TSyntax `type_lang) : CommandElabM (Out × Out) :=
    return (← translate X codeN tyN guarded a, ← translate X codeN tyN guarded b)
  binary (C c d : Term) (a b : Out) (ty : TSyntax `type_lang) : CommandElabM Out := do
    return ⟨← `(term_lang| [$C]ₛ ⟨$(a.code), $(b.code)⟩), ← `($c $(a.nf) $(b.nf)),
      ← `($d $(a.dec) $(b.dec)), ty⟩

elab_rules : command
  | `(gtype $N $bs:bracketedBinder* := ν $X . $body) => do
    let args := (← bs.flatMapM getBracketedBinderIds).map mkIdent
    let name (s : Name) := mkIdent (N.getId ++ s)
    let app (s : Name) : CommandElabM Term := `(@$(name s) $args*)
    let tyN ← `(@$N $args*)
    let out ← translate X.getId (← app `code) tyN false body
    let x := mkIdent `x
    for cmd in #[
      ← `(gdef $(name `code) $bs* : UNIV := fix $X. $(out.code)),
      ← `(def $N $bs* : TYPE := El $(← app `code)),
      ← `(gtheorem $(name `unfold_code) $bs* : ([$(← app `code)]ₛ = [$(out.nf)]ₛ) :=
            by gunfold $(name `code); gfix; grfl),
      ← `(theorem $(name `eq) $bs* : ⟦$tyN⟧ₜ = ⟦⦃$(out.ty)⦄⟧ₜ :=
            DECODES_of_goal $(← app `unfold_code) $(out.dec)),
      ← `(def $(name `MK) $bs* := GTY.fold $(← app `eq)),
      ← `(def $(name `PROJ) $bs* := GTY.unfold $(← app `eq)),
      ← `(theorem $(name `MK_PROJ) $bs* :
            ⊢ᵍ ⟪∀ $x : [$tyN]. ([$(← app `MK)]ₛ ([$(← app `PROJ)]ₛ $x:ident)) = $x:ident⟫ :=
            GTY.fold_unfold $(← app `eq)),
      ← `(theorem $(name `PROJ_MK) $bs* :
            ⊢ᵍ ⟪∀ $x : $(out.ty). ([$(← app `PROJ)]ₛ ([$(← app `MK)]ₛ $x:ident)) = $x:ident⟫ :=
            GTY.unfold_fold $(← app `eq)),
      ← `(attribute [irreducible] $N)] do
      elabCommand cmd

end GuardedType

end
