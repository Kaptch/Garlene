module

public import Lean

@[expose] public section

register_option pp.type : Bool := {
  defValue := true
  descr := "(pretty printing) display types"
}

register_option pp.expr : Bool := {
  defValue := true
  descr := "(pretty printing) display expressions"
}

register_option pp.var : Bool := {
  defValue := true
  descr := "(pretty printing) display variables"
}

register_option pp.ident_type : Bool := {
  defValue := false
  descr := "(pretty printing) display identifier types"
}

register_option pp.proof : Bool := {
  defValue := true
  descr := "(pretty printing) display proof state"
}

register_option gtactic.debug : Bool := {
  defValue := false
  descr := "(guarded tactics) log wall-clock execution time of each g-tactic at its position"
}
