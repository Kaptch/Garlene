module

public import Lean
public import Qq

@[expose] public section

open Lean Qq

def quoteName (name : Name) : Q(Name) := q($name)

abbrev ElabCtx := List (List Name)

def getIdx! (ctx : ElabCtx) (name : Name) : Option (Nat × Nat) :=
  match ctx with
  | [] => none
  | frame :: rest =>
    match frame.findIdx? (· = name) with
    | some j => some (0, j)
    | none => (getIdx! rest name).map fun (i, j) => (i + 1, j)

partial def nameOfExpr? (e : Expr) : Option Name := do
  match e.getAppFnArgs with
  | (``Lean.Name.anonymous, #[]) => pure .anonymous
  | (``Lean.Name.str, #[n, .lit (.strVal s)]) => pure (.str (← nameOfExpr? n) s)
  | (``Lean.Name.num, #[n, .lit (.natVal i)]) => pure (.num (← nameOfExpr? n) i)
  | (``Lean.Name.mkStr1, #[.lit (.strVal s)]) => pure (Name.mkStr1 s)
  | (``Lean.Name.mkStr2, #[.lit (.strVal s1), .lit (.strVal s2)]) => pure (Name.mkStr2 s1 s2)
  | (``Lean.Name.mkSimple, #[.lit (.strVal s)]) => pure (Name.mkSimple s)
  | _ => none

def listOfExpr? (e : Expr) (dec : Expr → Option α) : Option (List α) := do
  let (_, xs) ← e.listLit?
  xs.mapM dec

def elabCtxOfExpr? (e : Expr) : Option ElabCtx :=
  listOfExpr? e (listOfExpr? · nameOfExpr?)

def getIdxE (ctx : Q(ElabCtx)) (name : Q(Name)) : Lean.MetaM Q(Option (Nat × Nat)) := do
  let ctxR ← Meta.reduce (← instantiateMVars ctx)
  let nameR ← Meta.reduce (← instantiateMVars name)
  let some ctxV := elabCtxOfExpr? ctxR
    | throwError "getIdxE: context did not reduce to a literal{indentExpr ctxR}"
  let some nameV := nameOfExpr? nameR
    | throwError "getIdxE: name did not reduce to a literal{indentExpr nameR}"
  pure (toExpr (getIdx! ctxV nameV))
