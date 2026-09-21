module

public import Lean

@[expose] public section

open Lean Meta

register_simp_attr expr_simp

syntax (name := guarded) "guarded " ident (str)? : attr

initialize guardedAttrExt : SimpleScopedEnvExtension Name NameSet ←
  registerSimpleScopedEnvExtension {
    name := by exact decl_name%
    initial := {}
    addEntry := fun set name => set.insert name
  }

def isGuarded (name : Name) : CoreM Bool := do
  let a := guardedAttrExt.getState (← getEnv)
  return a.contains name

initialize registerBuiltinAttribute {
  name := `guarded
  descr := "Register a guarded theorem or definition"
  applicationTime := AttributeApplicationTime.afterCompilation
  add := λ decl _stx attrKind => guardedAttrExt.add decl attrKind
  erase := fun decl => do
      unless ← isGuarded decl do
        throwError s!"{decl} is not guarded."
      modifyEnv fun env =>
        guardedAttrExt.modifyState env fun s =>
          s.erase decl
}
