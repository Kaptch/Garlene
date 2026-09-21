module

public import Lean
public import SynthDom.Interp.Univ
public import SynthDom.Interp.GuardedType
public import SynthDom.Config.Attr
@[expose] public meta section

open Lean Elab Command CategoryTheory

section syntax_cat

syntax "gtype" ident (ppSpace bracketedBinder)* " := " "ν" ident "." type_lang : command

end syntax_cat

namespace GuardedType

mutual
  inductive Body where
    | code (type : Term)
    | discrete (type : Term)
    | prod (left right : Body)
    | sum (left right : Body)
    | laterRec
    | laterArr (domain codomain : Side)

  inductive Side where
    | recursive
    | nested (body : Body)
end

partial def parseBody (recVar : Name) :
    TSyntax `type_lang → CommandElabM Body
  | `(type_lang| [$t]) => pure (.code t)
  | `(type_lang| Δ $t) => pure (.discrete t)
  | `(type_lang| $a × $b) =>
      return .prod (← parseBody recVar a) (← parseBody recVar b)
  | `(type_lang| $a ⊕ $b) =>
      return .sum (← parseBody recVar a) (← parseBody recVar b)
  | `(type_lang| ▸ $x:ident) =>
      if x.getId == recVar then pure .laterRec
      else throwErrorAt x "▸ of a non-recursion variable is not yet supported"
  | `(type_lang| ▸ ($a → $b)) =>
      return .laterArr (← parseSide recVar a) (← parseSide recVar b)
  | `(type_lang| ▸ $t) =>
      throwErrorAt t "▸ of a non-recursion variable is not yet supported"
  | `(type_lang| ($body)) => parseBody recVar body
  | `(type_lang| $a → $_) =>
      throwErrorAt a "unguarded function types are not supported; guard the arrow as ▸(· → ·)"
  | `(type_lang| $x:ident) =>
      throwErrorAt x "a bare recursion variable is only valid as a side of ▸(·→·)"
  | stx => throwErrorAt stx "unsupported guarded-type former"
where
  parseSide (recVar : Name) : TSyntax `type_lang → CommandElabM Side
    | `(type_lang| $x:ident) =>
        if x.getId == recVar then pure .recursive
        else throwErrorAt x "only the recursion variable may appear bare under ▸(·→·)"
    | body => return .nested (← parseBody recVar body)

partial def translateGty (recOcc : TSyntax `term_lang) :
    Body → CommandElabM (TSyntax `term_lang)
  | .code type => `(term_lang| [UNIV.CODE $type]ₛ)
  | .discrete type => `(term_lang| [UNIV.DISCRETE (ULift $type)]ₛ)
  | .prod left right => do
      let left ← translateGty recOcc left
      let right ← translateGty recOcc right
      `(term_lang| [UNIV.PROD]ₛ ⟨$left, $right⟩)
  | .sum left right => do
      let left ← translateGty recOcc left
      let right ← translateGty recOcc right
      `(term_lang| [UNIV.SUM]ₛ ⟨$left, $right⟩)
  | .laterRec => `(term_lang| [UNIV.LATER]ₛ $recOcc)
  | .laterArr domain codomain => do
      let domain ← translateSide domain
      let codomain ← translateSide codomain
      `(term_lang| [UNIV.LARR]ₛ ⟨$domain, $codomain⟩)
where
  translateSide : Side → CommandElabM (TSyntax `term_lang)
    | .recursive => pure recOcc
    | .nested body => do
        let body ← translateGty recOcc body
        `(term_lang| delay $body)

partial def decodeObj (pshApp : Term) : Body → CommandElabM Term
  | .code type => `(⟦($type)⟧ₜ)
  | .discrete type => `(discrete.obj (ULift $type))
  | .prod left right => do
      let left ← decodeObj pshApp left
      let right ← decodeObj pshApp right
      `(CategoryTheory.MonoidalCategoryStruct.tensorObj $left $right)
  | .sum left right => do
      let left ← decodeObj pshApp left
      let right ← decodeObj pshApp right
      `(ℐ.psum $left $right)
  | .laterRec => `(later.obj $pshApp)
  | .laterArr domain codomain => do
      let domain ← decodeSide domain
      let codomain ← decodeSide codomain
      `(later.obj (ℐ.parr $domain $codomain))
where
  decodeSide : Side → CommandElabM Term
    | .recursive => pure pshApp
    | .nested body => decodeObj pshApp body

partial def normalizeCode (codeApp : Term) : Body → CommandElabM Term
  | .code type => `(UNIV.CODE $type)
  | .discrete type => `(UNIV.DISCRETE (ULift $type))
  | .prod left right => do
      let left ← normalizeCode codeApp left
      let right ← normalizeCode codeApp right
      `(box([UNIV.PROD]ₛ ⟨[$left]ₛ, [$right]ₛ⟩))
  | .sum left right => do
      let left ← normalizeCode codeApp left
      let right ← normalizeCode codeApp right
      `(box([UNIV.SUM]ₛ ⟨[$left]ₛ, [$right]ₛ⟩))
  | .laterRec => `(box([UNIV.LATER]ₛ (delay [$codeApp]ₛ)))
  | .laterArr domain codomain => do
      let domain ← normalizeSide domain
      let codomain ← normalizeSide codomain
      `(box([UNIV.LARR]ₛ ⟨delay [$domain]ₛ, delay [$codomain]ₛ⟩))
where
  normalizeSide : Side → CommandElabM Term
    | .recursive => pure codeApp
    | .nested body => normalizeCode codeApp body

partial def decodeProof (leafProof : Term) : Body → CommandElabM Term
  | .code type => `(DECODES_CODE $type)
  | .discrete type => `(DECODES_DISCRETE (ULift $type))
  | .prod left right => do
      let left ← decodeProof leafProof left
      let right ← decodeProof leafProof right
      `(DECODES_PROD $left $right)
  | .sum left right => do
      let left ← decodeProof leafProof left
      let right ← decodeProof leafProof right
      `(DECODES_SUM $left $right)
  | .laterRec => `(DECODES_LATER $leafProof)
  | .laterArr domain codomain => do
      let domain ← decodeSide domain
      let codomain ← decodeSide codomain
      `(DECODES_LARR $domain $codomain)
where
  decodeSide : Side → CommandElabM Term
    | .recursive => pure leafProof
    | .nested body => decodeProof leafProof body

partial def structuredType (tApp : Term) :
    Body → CommandElabM (Option (TSyntax `type_lang))
  | .code type => return some (← `(type_lang| [$type]))
  | .discrete type => return some (← `(type_lang| Δ $type))
  | .prod left right => do
      let some left ← structuredType tApp left | pure none
      let some right ← structuredType tApp right | pure none
      return some (← `(type_lang| ($left × $right)))
  | .sum left right => do
      let some left ← structuredType tApp left | pure none
      let some right ← structuredType tApp right | pure none
      return some (← `(type_lang| ($left ⊕ $right)))
  | .laterRec => return some (← `(type_lang| ▸ [$tApp]))
  | .laterArr domain codomain => do
      let some domain ← structuredSide domain | pure none
      let some codomain ← structuredSide codomain | pure none
      return some (← `(type_lang| ▸ ($domain → $codomain)))
where
  structuredSide : Side → CommandElabM (Option (TSyntax `type_lang))
    | .recursive => return some (← `(type_lang| [$tApp]))
    | .nested body => structuredType tApp body

def guardedBinderArgs
    (binders : TSyntaxArray ``Lean.Parser.Term.bracketedBinder) : CommandElabM (Array Term) := do
  let names ← binders.flatMapM Command.getBracketedBinderIds
  names.mapM fun name => do
    if name.isAnonymous then
      throwError "gtype does not support anonymous binders"
    let ident := mkIdent name
    `($ident:ident)

elab_rules : command
  | `(gtype $id $bs:bracketedBinder* := ν $X . $body) => do
    let codeIdent := mkIdent (id.getId ++ `code)
    let eqnIdent := mkIdent (id.getId ++ `equation)
    let unfoldIdent := mkIdent (id.getId ++ `unfold)
    let args ← guardedBinderArgs bs
    let body ← parseBody X.getId body
    let fhat ← translateGty (← `(term_lang| $X:ident)) body
    Command.elabCommand (←
      `(command| def $codeIdent $bs:bracketedBinder* : SYNT ⦃UNIV⦄ :=
          box(fix $X . $fhat)))
    let codeApp ← `(@$codeIdent $args*)
    Command.elabCommand (←
      `(command| def $id $bs:bracketedBinder* : TYPE :=
          ⦃[classify.hom (Fam $codeApp)]ₘ⦄))
    let μ := mkIdent `μ
    let feq ← translateGty (← `(term_lang| [$μ]ₛ)) body
    Command.elabCommand (←
      `(command| def $eqnIdent $bs:bracketedBinder* ($μ : SYNT ⦃▸ UNIV⦄) : SYNT ⦃UNIV⦄ :=
          box($feq)))
    let eqnApp ← `(@$eqnIdent $args* (box(delay [$codeApp]ₛ)))
    Command.elabCommand (←
      `(command| lemma $unfoldIdent $bs:bracketedBinder* :
          synt_interp $codeApp = synt_interp $eqnApp := by
        simp only [synt_interp]
        congr 1
        apply eq_interp
        dsimp only [$codeIdent:ident, $eqnIdent:ident]
        unfold EXPR.fix
        refine EQ.tran (EQ.unfold' ?_) ?_
        · have h := ($codeApp).proof
          unfold $codeIdent:ident EXPR.fix at h
          exact (TYPED.fix'_inversion h).2
        · convert EQ.rfl (($eqnApp).proof) using 1 <;>
            simp [binds, quote_eq_expr, weaken_synt_expr, binds_synt_expr,
              $codeIdent:ident, $eqnIdent:ident, EXPR.fix]))
    let pshIdent := mkIdent (id.getId ++ `PSh)
    let eqIdent := mkIdent (id.getId ++ `eq)
    Command.elabCommand (←
      `(command| def $pshIdent $bs:bracketedBinder* : ℐ := classify.hom (Fam $codeApp)))
    let pshApp ← `(@$pshIdent $args*)
    let unfoldApp ← `(@$unfoldIdent $args*)
    let xF ← decodeObj pshApp body
    let normalized ← normalizeCode codeApp body
    let leafProof ← `(DECODES_refl $codeApp)
    let chain ← decodeProof leafProof body
    Command.elabCommand (←
      `(command| unseal UNIV in
        lemma $eqIdent $bs:bracketedBinder* : DECODES $codeApp $xF := by
          refine DECODES_of_Fam_eq (c' := $eqnApp) ?unfold ?dec
          case unfold =>
            show _root_.Fam $codeApp = _root_.Fam $eqnApp
            simp only [_root_.Fam, GlobalElt]
            exact congrArg
              (fun f => CategoryTheory.CategoryStruct.comp
                (CategoryTheory.CartesianMonoidalCategory.lift
                  (CategoryTheory.CategoryStruct.id _) earlier_terminal.inv) f) $unfoldApp
          case dec =>
            refine DECODES_congr (c' := $normalized) ?hexpr ?chain
            case hexpr =>
              simp only [$eqnIdent:ident, quote_eq_expr]
              erw [quote_eq_expr]
            case chain => exact $chain))
    let unfoldPrimeIdent := mkIdent (id.getId ++ `unfold')
    let foldIdent := mkIdent (id.getId ++ `fold)
    let eqApp ← `(@$eqIdent $args*)
    let typeApp ← `(@$id $args*)
    Command.elabCommand (←
      `(command| def $unfoldPrimeIdent $bs:bracketedBinder* :=
          GTY.unfold (τ := $typeApp) (σ := ⦃[$xF]ₘ⦄) $eqApp))
    Command.elabCommand (←
      `(command| def $foldIdent $bs:bracketedBinder* :=
          GTY.fold (τ := $typeApp) (σ := ⦃[$xF]ₘ⦄) $eqApp))
    if let some structured ← structuredType typeApp body then
      let mkIdent' := mkIdent (id.getId ++ `MK)
      let projIdent := mkIdent (id.getId ++ `PROJ)
      Command.elabCommand (←
        `(command| def $mkIdent' $bs:bracketedBinder* : SYNT ⦃$structured → [$typeApp]⦄ :=
            GTY.fold (τ := $typeApp) (σ := ⦃$structured⦄) (by exact $eqApp)))
      Command.elabCommand (←
        `(command| def $projIdent $bs:bracketedBinder* : SYNT ⦃[$typeApp] → $structured⦄ :=
            GTY.unfold (τ := $typeApp) (σ := ⦃$structured⦄) (by exact $eqApp)))
      guardedAttrExt.add mkIdent'.getId
      guardedAttrExt.add projIdent.getId
      let mkProjIdent := mkIdent (id.getId ++ `MK_PROJ)
      let projMkIdent := mkIdent (id.getId ++ `PROJ_MK)
      Command.elabCommand (←
        `(command| theorem $mkProjIdent $bs:bracketedBinder* :
            type_of% (GTY.fold_unfold (τ := $typeApp) (σ := ⦃$structured⦄)
              (by exact $eqApp)) :=
            GTY.fold_unfold (τ := $typeApp) (σ := ⦃$structured⦄) (by exact $eqApp)))
      Command.elabCommand (←
        `(command| theorem $projMkIdent $bs:bracketedBinder* :
            type_of% (GTY.unfold_fold (τ := $typeApp) (σ := ⦃$structured⦄)
              (by exact $eqApp)) :=
            GTY.unfold_fold (τ := $typeApp) (σ := ⦃$structured⦄) (by exact $eqApp)))
      guardedAttrExt.add mkProjIdent.getId
      guardedAttrExt.add projMkIdent.getId
    guardedAttrExt.add codeIdent.getId
    guardedAttrExt.add id.getId
    Command.elabCommand (←
      `(command| attribute [irreducible] $id $pshIdent $codeIdent))

end GuardedType

end
