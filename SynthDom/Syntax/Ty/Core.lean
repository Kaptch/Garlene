module

public import SynthDom.Semantics.Base

@[expose] public section

inductive TYPE.{i} : Type (i + 1) where
| embed : Type (imax i 0) → TYPE
| prod : TYPE → TYPE → TYPE
| sum : TYPE → TYPE → TYPE
| arr : TYPE → TYPE → TYPE
| later : TYPE → TYPE
| prop : TYPE
| ax : ℐ.{i} → TYPE

abbrev OCTX.{i} := List TYPE.{i}
abbrev CTX.{i} := List OCTX.{i}
end
