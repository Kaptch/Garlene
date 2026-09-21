module

public meta import Lean
public meta import Qq

public meta import SynthDom.Syntax.Expr.Core
public import SynthDom.Syntax.Expr.Syntax
public meta import SynthDom.Config.Options
public meta import SynthDom.Syntax.Utils

public meta import SynthDom.Syntax.Ty.Elab

@[expose] public meta section

section expr

open Lean Elab Meta PrettyPrinter Delaborator SubExpr Qq
open CategoryTheory
open MonoidalCategory

partial def lift_type (i : Level) (τ : Q(ℐ.{i}))
  : MetaM Q(TYPE.{i}) :=
  match τ with
  | ~q(later.obj $τ') => do
    let t' ← lift_type _ τ'
    pure q(TYPE.later $t')
  | ~q($τ₁ ⟶[ℐ.{i}] $τ₂) => do
    let t₁ ← lift_type _ τ₁
    let t₂ ← lift_type _ τ₂
    pure q(TYPE.arr $t₁ $t₂)
  | ~q($τ₁ ⊗ $τ₂) => do
    let t₁ ← lift_type _ τ₁
    let t₂ ← lift_type _ τ₂
    pure q(TYPE.prod $t₁ $t₂)
  | ~q(discrete.obj (ULift.{i, 0} $τ')) => do
    pure q(TYPE.embed.{i} $τ')
  | ~q(Logic.subobject_classifier_psh.{i}) => do
    pure q(TYPE.prop)
  | τ' =>
    pure q(TYPE.ax $τ')

abbrev TmElabM := ReaderT Q(ElabCtx) TermElabM

def TmElabM.run (Γ : Q(ElabCtx))
  (x : TmElabM α) : TermElabM α :=
  ReaderT.run x Γ

def getTmCtx : TmElabM Q(ElabCtx) :=
  read

partial def elabTM (l : Level) : TSyntax `term_lang → TmElabM Q(EXPR.{l})
  | `(term_lang| ($t:term_lang)) =>
    elabTM l t
  | `(term_lang| _) =>

    Qq.mkFreshExprMVarQ q(EXPR.{l}) (userName := `ghole)
  | `(term_lang| ♯($n:num, $m:num)) => do
    let n : Nat := n.getNat
    let m : Nat := m.getNat
    pure q(@EXPR.var Name.anonymous $n $m)
  | `(term_lang| $id:ident) => do
    let id' := id.getId
    let Ψ ← getTmCtx
    let p := quoteName id'
    let f : Q(Option (Nat × Nat)) ← getIdxE Ψ p
    try
      match f with
      | ~q(Option.some ⟨$n, $m⟩) =>
        pure q(@EXPR.var $p $n $m)
      | _ =>
        throwError "Unbound identifier {id}."
    catch _ =>
      throwError "Unexpected identifier {id}."
  | `(term_lang| [ $id:term ]ₛ) => do
    let Ψ ← getTmCtx
    let k : Q(Nat) := q(($Ψ).length)
    let k' : Q(Option Nat) := q((($Ψ).getLast?.map List.length))
    let t ← Qq.mkFreshExprMVarQ (q(TYPE.{l}))
    let s ← elabTermEnsuringTypeQ id (expectedType := q(SYNT.{l} $t))
    pure q(EXPR.quote (τ := $t) $s $k $k')
  | `(term_lang| [ $id:term ]ₘ) => do
    let t ← Qq.mkFreshExprMVarQ q(ℐ.{l})
    let s ← elabTermEnsuringTypeQ id (expectedType := q((𝟙_ ℐ.{l} ⟶ $t)))
    let t' ← lift_type _ t
    let ⟨_⟩ ← assertDefEqQ t q(⟦$t'⟧ₜ)
    pure q(EXPR.ax $t' $s)
  | `(term_lang| λ $id:ident : $A:type_lang . $t:term_lang) => do
    let id := id.getId
    let p := quoteName id
    let m ← getTmCtx
    let A' ← (elabTYPE l A).run
    let e ← (elabTM l t).run q(($m).modify 0 (List.cons $p))
    pure q(EXPR.lam $p $A' $e)
  | `(term_lang| λ $id:ident . $t:term_lang) => do
    let id := id.getId
    let p := quoteName id
    let m ← getTmCtx
    let A' ← Qq.mkFreshExprMVarQ (q(TYPE.{l})) (userName := `β)
    let e ← (elabTM l t).run q(($m).modify 0 (List.cons $p))
    pure q(EXPR.lam $p $A' $e)
  | `(term_lang| λ _ : $A:type_lang . $t:term_lang) => do
    let m ← getTmCtx
    let A' ← (elabTYPE l A).run
    let e ← (elabTM l t).run q(($m).modify 0 (List.cons Name.anonymous))
    pure q(EXPR.lam Name.anonymous $A' $e)
  | `(term_lang| λ _ . $t:term_lang) => do
    let m ← getTmCtx
    let A' ← Qq.mkFreshExprMVarQ (q(TYPE.{l})) (userName := `β)
    let e ← (elabTM l t).run q(($m).modify 0 (List.cons Name.anonymous))
    pure q(EXPR.lam Name.anonymous $A' $e)
  | `(term_lang| $t:term_lang $e:term_lang) => do
    let a ← elabTM l t
    let b ← elabTM l e
    let A' ← Qq.mkFreshExprMVarQ (q(TYPE.{l})) (userName := `β)
    pure q(EXPR.app $A' $a $b)
  | `(term_lang| delay $t:term_lang) => do
    let m ← getTmCtx
    let t ← (elabTM l t).run q([] :: $m)
    pure q(EXPR.delay $t)
  | `(term_lang| adv $n:num $t:term_lang) => do
    let n : Nat := n.getNat
    let m ← getTmCtx
    let t ← (elabTM l t).run q(($m).drop $n)
    pure q(EXPR.adv $n $t)
  | `(term_lang| fix $id:ident . $t:term_lang) => do
    let id := id.getId
    let p := quoteName id
    let m ← getTmCtx
    let A' ← Qq.mkFreshExprMVarQ (q(TYPE.{l})) (userName := `β)
    let e ← (elabTM l t).run q(($m).modify 0 (List.cons $p))
    pure q(EXPR.fix $p $A' $e)
  | `(term_lang| fix $id:ident : $A:type_lang . $t:term_lang) => do
    let id := id.getId
    let p := quoteName id
    let m ← getTmCtx
    let A' ← (elabTYPE l A).run
    let e ← (elabTM l t).run q(($m).modify 0 (List.cons $p))
    pure q(EXPR.fix $p $A' $e)
  | `(term_lang| fix _ . $t:term_lang) => do
    let m ← getTmCtx
    let A' ← Qq.mkFreshExprMVarQ (q(TYPE.{l})) (userName := `β)
    let e ← (elabTM l t).run q(($m).modify 0 (List.cons Name.anonymous))
    pure q(EXPR.fix Name.anonymous $A' $e)
  | `(term_lang| fix _ : $A:type_lang . $t:term_lang) => do
    let m ← getTmCtx
    let A' ← (elabTYPE l A).run
    let e ← (elabTM l t).run q(($m).modify 0 (List.cons Name.anonymous))
    pure q(EXPR.fix Name.anonymous $A' $e)
  | `(term_lang| $e:term_lang : $t:type_lang) => do
    let e ← elabTM l e
    let t ← (elabTYPE l t).run
    pure q(EXPR.annot $e $t)
  | `(term_lang| δ( $x:term : $y:term )) => do
    let r : Q(Type (imax l 0)) ←
      elabTermEnsuringTypeQ y (expectedType := q(Type (imax l 0)))
    let t ← elabTermEnsuringTypeQ x (expectedType := r)
    pure q(EXPR.embed $r $t)
  | `(term_lang| δ( $x:term )) => do
    let x ← Term.elabTerm x none
    let ⟨u, α, e⟩ ← Qq.inferTypeQ x
    let ⟨_⟩ ← assertLevelDefEqQ u (Level.succ (Level.imax l 0))
    let e ← Qq.instantiateMVarsQ e
    pure q(EXPR.embed.{l} $α $e)
  | `(term_lang| $e1:term_lang ⊙{$B:term} $e2:term_lang) => do
    let e1 ← elabTM l e1
    let e2 ← elabTM l e2
    let A ← Qq.mkFreshExprMVarQ q(Type (imax l 0)) (userName := `β)
    let B ← elabTermEnsuringTypeQ B (expectedType := q(Type (imax l 0)))
    pure q(EXPR.embed_apply $A $B $e1 $e2)
  | `(term_lang| $e1:term_lang ⊙ $e2:term_lang) => do
    let e1 ← elabTM l e1
    let e2 ← elabTM l e2
    let A ← mkFreshExprMVarQ (ty := q(Type (imax l 0)))
    let B ← mkFreshExprMVarQ (ty := q(Type (imax l 0)))
    pure q(EXPR.embed_apply $A $B $e1 $e2)
  | `(term_lang| ⌜ $e:term_lang ⌝) => do
    let e ← elabTM l e
    pure q(EXPR.pure $e)
  | `(term_lang| ⟨ $e1:term_lang, $e2:term_lang⟩) => do
    let e1 ← elabTM l e1
    let e2 ← elabTM l e2
    pure q(EXPR.pair $e1 $e2)
  | `(term_lang| π₁ $e:term_lang) => do
    let e ← elabTM l e
    let A ← Qq.mkFreshExprMVarQ (q(TYPE.{l})) (userName := `β)
    pure q(EXPR.proj $A $e DIR.L)
  | `(term_lang| π₂ $e:term_lang) => do
    let e ← elabTM l e
    let A ← Qq.mkFreshExprMVarQ (q(TYPE.{l})) (userName := `β)
    pure q(EXPR.proj $A $e DIR.R)
  | `(term_lang| inl $e:term_lang) => do
    let e ← elabTM l e
    let B ← Qq.mkFreshExprMVarQ (q(TYPE.{l})) (userName := `β)
    pure q(EXPR.inl $B $e)
  | `(term_lang| inr $e:term_lang) => do
    let e ← elabTM l e
    let A ← Qq.mkFreshExprMVarQ (q(TYPE.{l})) (userName := `α)
    pure q(EXPR.inr $A $e)
  | `(term_lang| case $e:term_lang $f:term_lang $g:term_lang) => do
    let e ← elabTM l e
    let f ← elabTM l f
    let g ← elabTM l g
    let A ← Qq.mkFreshExprMVarQ (q(TYPE.{l})) (userName := `α)
    let B ← Qq.mkFreshExprMVarQ (q(TYPE.{l})) (userName := `β)
    pure q(EXPR.case $A $B $e $f $g)
  | `(term_lang| $e1:term_lang ∨ $e2:term_lang) => do
    let e1 ← elabTM l e1
    let e2 ← elabTM l e2
    pure q(EXPR.or $e1 $e2)
  | `(term_lang| $e1:term_lang ∧ $e2:term_lang) => do
    let e1 ← elabTM l e1
    let e2 ← elabTM l e2
    pure q(EXPR.and $e1 $e2)
  | `(term_lang| $e1:term_lang → $e2:term_lang) => do
    let e1 ← elabTM l e1
    let e2 ← elabTM l e2
    pure q(EXPR.impl $e1 $e2)
  | `(term_lang| ∀ $id:ident : $A:type_lang . $t:term_lang) => do
    let id := id.getId
    let p := quoteName id
    let m ← getTmCtx
    let A' ← (elabTYPE l A).run
    let e ← (elabTM l t).run q(($m).modify 0 (List.cons $p))
    pure q(EXPR.forall $p $A' $e)
  | `(term_lang| ∀ $id:ident . $t:term_lang) => do
    let id := id.getId
    let p := quoteName id
    let m ← getTmCtx
    let A' ← Qq.mkFreshExprMVarQ (q(TYPE.{l})) (userName := `β)
    let e ← (elabTM l t).run q(($m).modify 0 (List.cons $p))
    pure q(EXPR.forall $p $A' $e)
  | `(term_lang| ∀ _ : $A:type_lang . $t:term_lang) => do
    let m ← getTmCtx
    let A' ← (elabTYPE l A).run
    let e ← (elabTM l t).run q(($m).modify 0 (List.cons Name.anonymous))
    pure q(EXPR.forall Name.anonymous $A' $e)
  | `(term_lang| ∀ _ . $t:term_lang) => do
    let m ← getTmCtx
    let A' ← Qq.mkFreshExprMVarQ (q(TYPE.{l})) (userName := `β)
    let e ← (elabTM l t).run q(($m).modify 0 (List.cons Name.anonymous))
    pure q(EXPR.forall Name.anonymous $A' $e)
  | `(term_lang| ∃ $id:ident : $A:type_lang . $t:term_lang) => do
    let id := id.getId
    let p := quoteName id
    let m ← getTmCtx
    let A' ← (elabTYPE l A).run
    let e ← (elabTM l t).run q(($m).modify 0 (List.cons $p))
    pure q(EXPR.exists $p $A' $e)
  | `(term_lang| ∃ $id:ident . $t:term_lang) => do
    let id := id.getId
    let p := quoteName id
    let m ← getTmCtx
    let A' ← Qq.mkFreshExprMVarQ (q(TYPE.{l})) (userName := `β)
    let e ← (elabTM l t).run q(($m).modify 0 (List.cons $p))
    pure q(EXPR.exists $p $A' $e)
  | `(term_lang| ∃ _ : $A:type_lang . $t:term_lang) => do
    let m ← getTmCtx
    let A' ← (elabTYPE l A).run
    let e ← (elabTM l t).run q(($m).modify 0 (List.cons Name.anonymous))
    pure q(EXPR.exists Name.anonymous $A' $e)
  | `(term_lang| ∃ _ . $t:term_lang) => do
    let m ← getTmCtx
    let A' ← Qq.mkFreshExprMVarQ (q(TYPE.{l})) (userName := `β)
    let e ← (elabTM l t).run q(($m).modify 0 (List.cons Name.anonymous))
    pure q(EXPR.exists Name.anonymous $A' $e)
  | `(term_lang| lift $t:term_lang) => do
    let e ← elabTM l t
    pure q(EXPR.lift $e)
  | `(term_lang| ⊤) => do
    pure q(EXPR.true)
  | `(term_lang| ⊥) => do
    pure q(EXPR.false)
  | `(term_lang| $e1:term_lang = $e2:term_lang) => do
    let e1 ← elabTM l e1
    let e2 ← elabTM l e2
    let A ← Qq.mkFreshExprMVarQ (q(TYPE.{l})) (userName := `β)
    pure q(EXPR.eq $A $e1 $e2)
  | _ => throwUnsupportedSyntax

end expr
