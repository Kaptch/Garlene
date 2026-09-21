# Artifact: Garlene -- Guarded Recursion in Lean

## 1. Building the artifact

### Option A: Docker (recommended)

Install [docker](https://docs.docker.com/engine/)

```sh
docker build -t garlene .
docker run --rm -p 8080:8080 garlene
```

Then open <http://localhost:8080> in a browser. 
You get a VS Code instance with the Lean 4 extension and the project already compiled.
`docker build` runs `lake exe cache get`, `lake build`, and `lake build Examples`. 
The build can take a while, it downloads the Lean toolchain and the cached Mathlib.

To inspect proofs interactively, open any file, wait for the Lean server to load, and place the cursor inside a `by`-block to see the goal state.

### Option B: local Lean toolchain

Requirements: [`elan`](https://github.com/leanprover/elan) (the Lean version manager)
and, for interactive use, VS Code/Codium with the `leanprover.lean4` extension.

```sh
lake exe cache get     # fetch the Mathlib build cache
lake build             # calculus, logic, model, proof mode
lake build Examples    # the case studies 
```
The toolchain (`leanprover/lean4:v4.33.1`) is pinned in `lean-toolchain`.

### Checks
We don't include separate checks, `#print axioms Lam.adequacy` after def/lemma can be used to see used axioms (in our case, PE, choice, Quot.sound, FE, as standard in Lean). 
Some commands in the project emit new names.
gtheorem/gdef preserve their given names. 
gtype (gtype N := N. F[N]) generates a few things:
- `N` : `TYPE` -- guarded type 
- `N.code` : `SYNT UNIV` -- element of the embedded universe 
- `N.equation` : `SYNT UNIV` -> `SYNT UNIV` -- the body of the equation 
- `N.unfold` : `synt_interp N.code` = `synt_interp (N.equation (delay N.code))` -- equation at the interpretation level
- `N.PSh` -- the corresponding presheaf object 
- `N.eq` : `DECODES N.code d` -- decoding witness, where `d` is an output type.
- `N.unfold'`, `N.fold` -- raw fold/unfold maps 
- `N.MK`, `N.PROJ` -- core language fold/unfold maps 
- `N.MK_PROJ`, `N.PROJ_MK` -- core language iso witnesses  

## 2. Paper-to-code correspondence

### Section 3

| Paper | Mechanization | Location |
|---|---|---|
| Fig. 1: `gtype Delay` | `gtype Delay` | [Examples/Delay/Base.lean#L10](SynthDom/Examples/Delay/Base.lean#L10) |
| Fig. 1: `Delay.map` | `gdef Delay.map` | [Examples/Delay/Base.lean#L18](SynthDom/Examples/Delay/Base.lean#L18) |
| Fig. 2 / sec. 3.3: functor identity law | `gtheorem Delay.map_id` | [Examples/Delay/Base.lean#L83](SynthDom/Examples/Delay/Base.lean#L83) |
| §3.4: exported denotation theorem | `Delay.map_id_denotation` | [Examples/Utils/Denotation.lean#L84](SynthDom/Examples/Utils/Denotation.lean#L84) |
| sec. 3.4: `denoteHom` | `denoteHom` | [Examples/Utils/Denotation.lean#L54](SynthDom/Examples/Utils/Denotation.lean#L54) |
| sec. 3.4: monad on the topos of trees | `DELAY.monad : CategoryTheory.Monad ℐ` | [Examples/Delay/Monad.lean#L218](SynthDom/Examples/Delay/Monad.lean#L218) |

### Section 4

| Paper | Mechanization | Location |
|---|---|---|
| sec. 4: grammar of types | `inductive TYPE` | [Syntax/Ty/Core.lean#L7](SynthDom/Syntax/Ty/Core.lean#L7) |
| sec. 4.1: frames and stacks of frames | `OCTX`, `CTX` | [Syntax/Ty/Core.lean#L16](SynthDom/Syntax/Ty/Core.lean#L16) |
| sec. 4: grammar of expressions e, Φ | `inductive EXPR` | [Syntax/Expr/Core.lean#L18](SynthDom/Syntax/Expr/Core.lean#L18) |
| Fig. 3: typing rules | `inductive TYPED` | [Syntax/Expr/Core.lean#L52](SynthDom/Syntax/Expr/Core.lean#L52) |
| sec. 4.2: typechecking | `typecheck` | [SynthDom/Syntax/Expr/Typecheck.lean#58](SynthDom/Syntax/Expr/Typecheck.lean#58) |
| sec. 4.2: renamings | `inductive REN` | [Syntax/Expr/Core.lean#L44](SynthDom/Syntax/Expr/Core.lean#L44) |
| sec. 4.2: renaming action | `weaken` | [Syntax/Expr/Core.lean#L1246](SynthDom/Syntax/Expr/Core.lean#L1246) |
| sec. 4.2: frame substitutions | `inductive SUBST` | [Syntax/Expr/Core.lean#L1455](SynthDom/Syntax/Expr/Core.lean#L1455) |
| sec. 4.2 / Fig. 4: stacked substitutions and their typing | `SSUBST`, `TSSUBST` | [Syntax/Expr/Core.lean#L1512](SynthDom/Syntax/Expr/Core.lean#L1512) |
| sec. 4.2: substitution action (variable case) | `subst_var` | [Syntax/Expr/Core.lean#L1907](SynthDom/Syntax/Expr/Core.lean#L1907) |
| sec. 4.2: offset and cut | `offset_ssubst`, `cut_ssubst` | [Syntax/Expr/Core.lean#L1561](SynthDom/Syntax/Expr/Core.lean#L1561), [#L1665](SynthDom/Syntax/Expr/Core.lean#L1665) |
| sec. 4.2: preservation of typing under weakening/substitution | proof files | [Syntax/Prf/Weaken/](SynthDom/Syntax/Prf/Weaken) |
| sec. 4.2: packaged typed terms `SYNT τ` | `structure SYNT` | [Syntax/Expr/Core.lean#L883](SynthDom/Syntax/Expr/Core.lean#L883) |
| sec. 3.2/sec. 4.2: the `gdef` command | `syntax "gdef"` | [Syntax/Expr/Typecheck.lean#L343](SynthDom/Syntax/Expr/Typecheck.lean#L343) |
| sec. 4.2: quotation with re-indexing | `EXPR.quote` | [Syntax/Expr/Core.lean#L2355](SynthDom/Syntax/Expr/Core.lean#L2355) |
| sec. 4.3: the `gtype` command | `syntax "gtype"` | [Meta/GuardedType.lean#L13](SynthDom/Meta/GuardedType.lean#L13) |
| sec. 4.3: internal universe `UNIV` | `def UNIV` | [Interp/Univ.lean#L12](SynthDom/Interp/Univ.lean#L12) |
| Fig. 5: code formers | `UNIV.DISCRETE`, `UNIV.LARR`, `UNIV.CODE` | [Interp/Univ.lean#L13](SynthDom/Interp/Univ.lean#L13)–[#L55](SynthDom/Interp/Univ.lean#L55) |
| sec. 4.3: decoding relation | `DECODES` | [Interp/Univ.lean#L106](SynthDom/Interp/Univ.lean#L106) |
| sec. 4.3: Hofmann-Streicher universe | `U` | [Semantics/Univ/Core.lean#L16](SynthDom/Semantics/Univ/Core.lean#L16) |
| sec. 4.3: semantic code formers | `U_discrete`, `U_prod`, `U_sum` / `U_arr` / `U_later`, `U_larr` | [Semantics/Univ/Polynomial.lean#L21](SynthDom/Semantics/Univ/Polynomial.lean#L21), [Exponential.lean#L38](SynthDom/Semantics/Univ/Exponential.lean#L38), [Temporal.lean#L124](SynthDom/Semantics/Univ/Temporal.lean#L124) |
| sec. 4.4: topos of trees | `abbrev ℐ := ℕᵒᵖ ⥤ Type u` | [Semantics/Base.lean#L43](SynthDom/Semantics/Base.lean#L43) |
| sec. 4.4: later functor | `later` | [Semantics/Base.lean#L287](SynthDom/Semantics/Base.lean#L287) |
| sec. 4.4: earlier functor | `earlier` | [Semantics/Base.lean#L220](SynthDom/Semantics/Base.lean#L220) |
| sec. 4.4: adjunction earlier-later | `earlier_later_adj` | [Semantics/Base.lean#L371](SynthDom/Semantics/Base.lean#L371) |
| sec. 4.4: interpretation of fix | `fixpoint` | [Semantics/Fixpoint.lean#L61](SynthDom/Semantics/Fixpoint.lean#L61) |
| sec. 4.4: interpretation of types and contexts | `interp_ty`, `interp_ctx` | [Interp/Base.lean#L18](synth-dom/SynthDom/Interp/Base.lean#L18), [#L48](SynthDom/Interp/Base.lean#L48) |
| sec. 4.4: partial interpretation of terms | `expr_interp` | [Interp/Tm.lean#L1719](SynthDom/Interp/Tm.lean#L1719) |

### Section 5 

| Paper | Mechanization | Location |
|---|---|---|
| sec. 5.1, Fig. 6 / Fig. 9 (App. A): provability rules | `inductive PROVES` | [Syntax/Prf/Core.lean#L236](SynthDom/Syntax/Prf/Core.lean#L236) |
| sec. 5.1, Fig. 7 / Fig. 10 (App. A): equational judgment | `inductive EQ` | [Syntax/Prf/Core.lean#L84](SynthDom/Syntax/Prf/Core.lean#L84) |
| sec. 5.1: the `gtheorem` command | `syntax "gtheorem" ...` | [Syntax/Prf/Elab.lean#L19](SynthDom/Syntax/Prf/Elab.lean#L19) |
| sec. 5.2: internal entailment of the topos of trees | `entails` | [Semantics/Logic.lean#L46](SynthDom/Semantics/Logic.lean#L46) |
| sec. 5.2: soundness of the logic | `theorem soundness` | [Interp/Soundness.lean#L1830](SynthDom/Interp/Soundness.lean#L1830) |
| sec. 5.2: consistency corollary | `theorem consistency` | [Interp/Soundness.lean#L1900](SynthDom/Interp/Soundness.lean#L1900) |
| sec. 5.2: semantic validity `Valid P` | `def Valid` | [Examples/Utils/Extract.lean#L17](SynthDom/Examples/Utils/Extract.lean#L17) |
| sec. 5.2: rules of-goal / pure / later | `valid_of_goal`, `valid_pure`, `valid_later` | [Examples/Utils/Extract.lean#L33](SynthDom/Examples/Utils/Extract.lean#L33), [#L55](SynthDom/Examples/Utils/Extract.lean#L55), [#L89](SynthDom/Examples/Utils/Extract.lean#L89) |
| sec. 5.1: function extensionality (via ax) | `gtheorem gfunext` (model side: `funext`) | [Examples/Utils/Funext.lean#L6](SynthDom/Examples/Utils/Funext.lean#L6), [Interp/Funext.lean#L238](SynthDom/Interp/Funext.lean#L238) |
| sec. 5.2: export/import between Garlene and Lean | `SYNT.app_ext`, `SYNT.eq_of_denoteHom` | [Examples/Utils/Denotation.lean#L222](SynthDom/Examples/Utils/Denotation.lean#L222), [#L237](SynthDom/Examples/Utils/Denotation.lean#L237) |
| sec. 5.3: proof-mode tactics (syntax and docs) | `gintro`, `glöb`, `gmono`, ... | [Syntax/Prf/Tactics/Syntax.lean#L8](SynthDom/Syntax/Prf/Tactics/Syntax.lean#L8) |
| sec. 5.3 (implementation): named-goal wrapper around `PROVES` | `structure GOAL` | [Syntax/Prf/Wrappers.lean#L62](SynthDom/Syntax/Prf/Wrappers.lean#L62) |
| sec. 5.3: simplification / canonical form | `expr_simp`-normalization | [Syntax/Prf/Tactics/Normalize.lean#L95](SynthDom/Syntax/Prf/Tactics/Normalize.lean#L95) |
| sec. 5.3: rewriting with motive inference | `grewrite` implementation | [Syntax/Prf/Tactics/Rewrite.lean#L158](SynthDom/Syntax/Prf/Tactics/Rewrite.lean#L158) |
| sec. 5.3: logical tactics for the later modality | `gmono` implementation | [Syntax/Prf/Tactics/Monotonicity.lean#L19](SynthDom/Syntax/Prf/Tactics/Monotonicity.lean#L19) |
| sec. 5.3: comparing quotations by offset | quotation matcher | [Syntax/Prf/Tactics/Matcher.lean#L22](SynthDom/Syntax/Prf/Tactics/Matcher.lean#L22) |

### Section 6 

| Paper | Mechanization | Location |
|---|---|---|
| sec. 6.1: `ret`, `step`, `bind` | `gdef Delay.ret/step/bind` | [Examples/Delay/Base.lean#L12](SynthDom/Examples/Delay/Base.lean#L12), [#L15](SynthDom/Examples/Delay/Base.lean#L15), [#L24](SynthDom/Examples/Delay/Base.lean#L24) |
| sec. 6.1: functor and monad laws | `Delay.bind_ret`, `Delay.map_id`, `Delay.map_comp`, `Delay.bind_assoc` | [Examples/Delay/Base.lean#L60](SynthDom/Examples/Delay/Base.lean#L60), [#L83](SynthDom/Examples/Delay/Base.lean#L83), [#L139](SynthDom/Examples/Delay/Base.lean#L139), [#L165](SynthDom/Examples/Delay/Base.lean#L165) |
| sec. 6.1: join and monad laws in join form | `Delay.join`, `join_ret`, `join_map_ret`, `join_assoc` | [Examples/Delay/Monad.lean#L20](SynthDom/Examples/Delay/Monad.lean#L20), [#L123](SynthDom/Examples/Delay/Monad.lean#L123)–[#L161](SynthDom/Examples/Delay/Monad.lean#L161) |
| sec. 6.1: Mathlib monad instance on the topos of trees | `DELAY.monad` | [Examples/Delay/Monad.lean#L218](SynthDom/Examples/Delay/Monad.lean#L218) |
| sec. 6.2: extension `ext s f` and its equations | `Delay.ext`, `ext_ret`, `ext_step` | [Examples/Delay/Algebra.lean#L11](SynthDom/Examples/Delay/Algebra.lean#L11), [#L31](SynthDom/Examples/Delay/Algebra.lean#L31), [#L43](SynthDom/Examples/Delay/Algebra.lean#L43) |
| sec. 6.2: uniqueness (freeness) | `Delay.ext_unique` | [Examples/Delay/Algebra.lean#L56](SynthDom/Examples/Delay/Algebra.lean#L56) |
| sec. 6.2: monad laws re-derived via freeness | `Delay.bind_eq_ext` ... `Delay.map_comp_free` | [Examples/Delay/Algebra.lean#L100](SynthDom/Examples/Delay/Algebra.lean#L100)–[#L196](SynthDom/Examples/Delay/Algebra.lean#L196) |
| Eq. (1) / sec. 4.3 / sec. 6.3: guarded domain D | `gtype Dom` | [Examples/Lam/Model.lean#L10](SynthDom/Examples/Lam/Model.lean#L10) |
| sec. 6.3: lambda_fix syntax, typing, operational semantics | `Lam`, `Ty`, `Typing`, `Step`, `Steps` | [Examples/Lam/Language.lean#L7](SynthDom/Examples/Lam/Language.lean#L7), [#L105](SynthDom/Examples/Lam/Language.lean#L105), [#L113](SynthDom/Examples/Lam/Language.lean#L113), [#L65](SynthDom/Examples/Lam/Language.lean#L65), [#L75](SynthDom/Examples/Lam/Language.lean#L75) |
| sec. 6.3: interpretation interp_n | `interp` | [Examples/Lam/Language.lean#L25](SynthDom/Examples/Lam/Language.lean#L25) |
| sec. 6.3: application in the model | `gdef Dom.apply` | [Examples/Lam/Model.lean#L24](SynthDom/Examples/Lam/Model.lean#L24) |
| sec. 6.3: soundness (one step = one thunk) | `interp_step` | [Examples/Lam/Soundness.lean#L324](SynthDom/Examples/Lam/Soundness.lean#L324) |
| sec. 6.3: weakest precondition wp | `gdef Dom.wp` | [Examples/Lam/Adequacy.lean#L33](SynthDom/Examples/Lam/Adequacy.lean#L33) |
| sec. 6.3: relations Exp and Val | `Dom.Exp`, `Dom.Val` | [Examples/Lam/Adequacy.lean#L247](SynthDom/Examples/Lam/Adequacy.lean#L247), [#L258](SynthDom/Examples/Lam/Adequacy.lean#L258) |
| sec. 6.3: `SubstOk` | `SubstOk` | [Examples/Lam/Adequacy.lean#L387](SynthDom/Examples/Lam/Adequacy.lean#L387) |
| **Lemma 6.1** (Fundamental lemma) | `theorem fundamental` | [Examples/Lam/Adequacy.lean#L608](SynthDom/Examples/Lam/Adequacy.lean#L608) |
| sec. 6.3: `denote` and `Runs` | `denote`, `Runs` | [Examples/Lam/Adequacy.lean#L655](SynthDom/Examples/Lam/Adequacy.lean#L655), [#L714](SynthDom/Examples/Lam/Adequacy.lean#L714) |
| **Theorem 6.2** (Adequacy) | `theorem adequacy` | [Examples/Lam/Adequacy.lean#L739](SynthDom/Examples/Lam/Adequacy.lean#L739) |
| sec. 6.3: sanity check (S K K () terminates) | `skkUnit_adequacy` | [Examples/Lam/Adequacy.lean#L811](SynthDom/Examples/Lam/Adequacy.lean#L811) |

### Additional material not described in the paper

- [`SynthDom/Examples/Stream/`](SynthDom/Examples/Stream): guarded streams examples.

## 3. Layout 

| Directory | Contents |
|---|---|
| `SynthDom/Syntax/` | deep embedding: types, expressions, typing, weakening/substitution, the `PROVES`/`EQ` judgments, elaborators, and the proof-mode tactics (sec. 4-5) |
| `SynthDom/Semantics/` | the topos of trees, later/earlier, the guarded fixpoint, the internal logic, the semantic universe (sec. 4.4) |
| `SynthDom/Interp/` | interpretation of syntax into the model, soundness, guarded-type infra (sec. 4.4, 5.2) |
| `SynthDom/Meta/` | the `gtype` command (sec. 4.3) |
| `SynthDom/Config/` | attributes (not used in this version, included for completeness) |
| `SynthDom/Examples/` | the case studies (sec. 6) and the export interface (`Valid`, `denoteHom`) |

## 4. Notes 

In [Semantics/Base.lean#L197](SynthDom/Semantics/Base.lean#L197) we override the automatically inserted Mathlib instance of the exponential for the topos of trees with a hand-written definition.
Ours is propositionally equal to Mathlib's, but defined directly.

## 5. Tactics

| Tactic | Description |
|---|---|
| `gintro x ...` | introduce `∀` and `→` |
| `gsplit` | split a `∧` goal |
| `gleft`, `gright` | choose a disjunct to prove |
| `gexists a` | give a witness for an `∃` goal |
| `gexfalso` | replace the goal by `⊥` |
| `gtrivial` | close a `⊤` goal |
| `gexact H` | close the goal with `H` |
| `gassumption` | close the goal with any matching hypothesis |
| `gcases e with pat` | destruct a hypothesis (`∧`, `∃`, `∨`) or a sum-typed term; each sum branch gets an equation |
| `gassert H of φ` | assert `φ` as `H`, with `φ` as a side goal |
| `gpose (t) as H` | add a Lean proof `t` as hypothesis `H` |
| `gspecialize H a... [as K]` | instantiate the `∀`-prefix of `H` |
| `grename hypothesis H to K` | rename a hypothesis |
| `gclear hypothesis H` | drop a hypothesis |
| `gapply H a...`, `gapply (t) a...` | apply a hypothesis or a Lean lemma, instantiating `∀` and `→` |
| `glöb IH` | Loeb induction: assume the goal one tick later as `IH` |
| `gnext` | enter the next frame (`lift-intro`) |
| `gmono H... as K...` | enter the next frame with `▷`-hypotheses `H...` unboxed as `K...` (`later-mono`) |
| `gfix` | unroll the exposed fixpoint once |
| `gunfold f [at H]` | unfold the quoted definition `f` in the goal or in `H` |
| `gsimpl` | normalise: `β`, projections, `case`, `adv`/`delay` cancellation |
| `grfl` | close `e = e` up to normalisation |
| `grewrite [←] H a... [at K]`, `grewrite [←] (t) a... [at K]` | rewrite with an equation, also under `delay`/`adv`; omitted arguments are inferred by matching |
| `gcong` | change `f a = f b` to `a = b` |
| `ginjection H as K` | constructor injectivity on an equation `H`; closes the goal if the constructors differ |
| `gembed` | reduce a `pure` goal to the Lean proposition (`pure-intro`) |
| `gpoints x` | introduce a Lean variable `x` for a `∀` over an embedded type `Δ T` (`forall-intro-points`) |

`gnext` and `gmono` first turn a goal `delay e₁ = delay e₂` into `▷(e₁ = e₂)` (`delay-eq`).

