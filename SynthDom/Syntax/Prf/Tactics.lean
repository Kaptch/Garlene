module

public meta import Lean
public meta import Qq

public import SynthDom.Syntax.Prf.Tactics.Syntax
public meta import SynthDom.Syntax.Prf.Tactics.Structural
public meta import SynthDom.Syntax.Prf.Tactics.Simplify
public meta import SynthDom.Syntax.Prf.Tactics.Assertions
public meta import SynthDom.Syntax.Prf.Tactics.Cases
public meta import SynthDom.Syntax.Prf.Tactics.Rules
public meta import SynthDom.Syntax.Prf.Tactics.Rewrite
public meta import SynthDom.Syntax.Prf.Tactics.Monotonicity
public meta import SynthDom.Syntax.Prf.Tactics.Temporal

@[expose] public meta section

section prf

open Lean Meta Elab PrettyPrinter Delaborator Tactic SubExpr Qq Syntax

def withGTiming (k : TacticM Unit) : TacticM Unit := do
  unless (← getBoolOption `gtactic.debug) do
    k
    return
  let ref ← getRef
  let src := (ref.reprint.getD "").trimAscii
  let t0 ← IO.monoNanosNow
  k
  let t1 ← IO.monoNanosNow
  let ms := (t1 - t0).toFloat / 1000000.0
  logInfo m!"[gtactic] {src} — {ms}ms"

def runGT (t : TacticM Unit) : TacticM Unit :=
  withGTiming (withMainContext t)

def clearScratchHyp (name : Name) : TacticM Unit := do
  let goals ← getGoals
  let mut result : Array MVarId := #[]
  for goal in goals do
    setGoals [goal]
    discard <| observing? (withMainContext (clearHyp "gclear" name))
    result := result ++ (← getGoals).toArray
  setGoals result.toList

def withPosedRule (term : TSyntax `term) (action : Ident → TacticM Unit) : TacticM Unit := focus do
  let scratch := mkIdent (← mkFreshUserName `_gsp)
  withMainContext (pose_core term scratch)
  withMainContext (action scratch)
  clearScratchHyp scratch.getId

def grwLemma (dir : RwDir) (t : TSyntax `term)
    (ts : Array (TSyntax `term_lang))
    (tgt : Option Ident := none) : TacticM Unit := do
  withPosedRule t fun scratch =>
    grwLemmaCore dir scratch.getId ts (tgt.map (·.getId))

def grwHyp (dir : RwDir) (h : TSyntax `ident)
    (ts : Array (TSyntax `term_lang))
    (tgt : Option Ident := none) : TacticM Unit := do
  withMainContext (grwLemmaCore dir h.getId ts (tgt.map (·.getId)))

elab_rules : tactic
| `(tactic| gintro $xs:ident*) => do
  withGTiming do for x in xs do withMainContext (intro_core x)
| `(tactic| gsplit) => do runGT split_core
| `(tactic| gleft) => do runGT left_core
| `(tactic| gright) => do runGT right_core
| `(tactic| gexfalso) => do runGT exfalso_core
| `(tactic| gcases $e:term_lang with $pat:gcases_pat) => do
  withGTiming do
    match e with
    | `(term_lang| $h:ident) => gcasesGo h.getId pat ""
    | _ => gcasesTerm e pat
| `(tactic| gapply $h:ident $ts:term_lang*) => do
  runGT (apply_core h ts)
| `(tactic| gapply ($t:term) $ts:term_lang*) => do
  withGTiming (withPosedRule t fun scratch => apply_core scratch ts)
| `(tactic| glöb $h:ident) => do runGT (loeb_core h)
| `(tactic| gsimpl) => do runGT simpl_core
| `(tactic| gnext) => do runGT do peelDelayEq; next_core
| `(tactic| gunfold $h:ident at $t:ident) => do
  withGTiming (withMainContext (unfold_at_hyp_impl h t))
| `(tactic| gunfold $h:ident) => do runGT (unfold_core h)
| `(tactic| gembed) => do runGT embed_core
| `(tactic| gpoints $x:ident) => do runGT (points_core x.getId)
| `(tactic| gtrivial) => do runGT trivial_core
| `(tactic| grfl) => do runGT rfl_core
| `(tactic| gfix) => do runGT fix_core
| `(tactic| grename hypothesis $i:ident to $j:ident) => do
  runGT (renameHyp "grename" i.getId j.getId)
| `(tactic| gclear hypothesis $i:ident) => do
  runGT (clearHyp "gclear" i.getId)
| `(tactic| gspecialize $i:ident $ts:term_lang* as $j:ident) => do
  runGT (specialize_core i ts (some j.getId))
| `(tactic| gspecialize $i:ident $ts:term_lang*) => do
  runGT (specialize_core i ts none)
| `(tactic| gexact $h:ident) => do runGT (exact_core h)
| `(tactic| gassumption) => do runGT assumption_core
| `(tactic| gexists $t:term_lang) => do runGT (exists_core t)
| `(tactic| ginjection $h:ident as $g:ident) => do
  runGT (injection_core h g)
| `(tactic| grewrite $h:ident $ts:term_lang* $[ at $tgt:ident]?) => do
  withGTiming (grwHyp .ltr h ts tgt)
| `(tactic| grewrite ← $h:ident $ts:term_lang* $[ at $tgt:ident]?) => do
  withGTiming (grwHyp .rtl h ts tgt)
| `(tactic| gassert $h:ident of $e:term_lang) => do
  runGT (assert_core h e)
| `(tactic| gmono $hs:ident* as $js:ident*) => do
  withGTiming do
    peelDelayEq
    withMainContext (mono_core hs js)
| `(tactic| grewrite ($t:term) $ts:term_lang* $[ at $tgt:ident]?) => do
  withGTiming (grwLemma .ltr t ts tgt)
| `(tactic| grewrite ← ($t:term) $ts:term_lang* $[ at $tgt:ident]?) => do
  withGTiming (grwLemma .rtl t ts tgt)
| `(tactic| gpose $t:term as $j:ident) => do
  runGT (pose_core t j)
| `(tactic| gcong) => do
  withGTiming (withMainContext congr_core)

end prf
