/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness
import AxiomAudit.Core
import AxiomAudit.Fixture.Root
import AxiomAudit.Fixture.Outside
import AxiomAudit.Fixture.Clean

/-!
# Axiom audit regressions

Negative and positive cases for `AxiomAudit.audit` and its acceptance check
`AxiomAudit.Report.violations`, which the production driver uses unchanged. Each block throws on an
unmet expectation. The file declares nothing, so every audit here also checks that no constant
lacks a defining module; the case where one does lives in `scripts/AxiomAuditUnknown.lean`.

Run from the repo root, after a build, with `lake env lean scripts/AxiomAuditRegression.lean`.
-/

open Lean Elab Command AxiomAudit

/-! ## The leaky closure: every name-based blind spot is selected and rejected -/

run_cmd liftCoreM do
  let env ← getEnv
  let r ← audit `AxiomAudit.Fixture.Root
  let expectModules :=
    #[`AxiomAudit.Fixture.Axiom, `AxiomAudit.Fixture.Leaky, `AxiomAudit.Fixture.Root].qsort Name.lt
  unless r.modules == expectModules do
    throwError "leaky closure: modules {r.modules}, expected {expectModules}"
  let control := `AxiomAuditFixture.controlLeak
  let rootLevel := `rootLeak
  let priv := mkPrivateNameCore `AxiomAudit.Fixture.Leaky `AxiomAuditFixture.privateLeak
  let gen := `AxiomAuditFixture.generatedLeak._proof_1
  -- the fixture really contains the kinds of declaration it is meant to
  for n in [control, rootLevel, priv, gen, `AxiomAuditFixture.generatedLeak] do
    unless env.contains n do throwError "leaky fixture: {n} is not in the environment"
  unless isPrivateName priv do throwError "leaky fixture: {priv} is not private"
  unless gen.isInternal && !isPrivateName gen do
    throwError "leaky fixture: {gen} is not a generated, non-private declaration"
  -- the old namespace predicate sees the control and misses the other three
  let oldSelects (n : Name) : Bool := (`AxiomAuditFixture).isPrefixOf n && !n.isInternal
  unless oldSelects control do throwError "control: the namespace predicate misses {control}"
  for n in [rootLevel, priv, gen] do
    if oldSelects n then throwError "blind spot: the namespace predicate selects {n}"
  -- the module selection sees all of them, and rejects exactly the forbidden dependencies
  let leaks := #[`AxiomAuditFixture.forbidden, control, rootLevel, priv,
    `AxiomAuditFixture.generatedLeak, gen]
  for n in leaks do
    unless r.checked.contains n do throwError "leaky closure: {n} is not selected"
  let expectOffenders := (leaks.map (·, `AxiomAuditFixture.forbidden)).qsort
    fun p q ↦ Name.lt p.1 q.1
  unless r.offenders == expectOffenders do
    throwError "leaky closure: offenders {r.offenders}, expected {expectOffenders}"
  unless r.violations.size == leaks.size && r.unknown.isEmpty do
    throwError "leaky closure: violations {r.violations}"
  -- a declaration outside the closure is not selected, although it is in the environment
  let outside := `AxiomAuditFixture.outsideLeak
  unless env.contains outside do throwError "outside fixture: {outside} is not in the environment"
  if r.checked.contains outside then throwError "leaky closure: {outside} is selected"
  -- and the production entry point enforces the same verdict
  let threw ← try run `AxiomAudit.Fixture.Root; pure false catch _ => pure true
  unless threw do throwError "leaky closure: `run` accepted it"
  logInfo m!"leaky closure: {r.offenders.size} offender(s) rejected, outside closure ignored"

/-! ## The clean closure passes -/

run_cmd liftCoreM do
  let r ← audit `AxiomAudit.Fixture.Clean
  unless r.violations.isEmpty do throwError "clean closure rejected: {r.violations}"
  unless r.checked.contains `AxiomAuditFixture.cleanUsesPropext do
    throwError "clean closure: cleanUsesPropext is not selected"
  logInfo m!"clean closure: accepted"

/-! ## Errors that leave no report -/

run_cmd liftCoreM do
  let throws (label : String) (x : CoreM Report) : CoreM Unit := do
    let threw ← try discard x; pure false catch _ => pure true
    unless threw do throwError "{label}: expected the audit to fail"
  throws "missing root" (audit `AxiomAudit.Fixture.Missing)
  throws "root without a source file in the workspace" (audit `Lean.Elab.Command)
  throws "failing closure script" (audit `AxiomAudit.Fixture.Clean (cmd := ("false", #[])))
  throws "empty closure output" (audit `AxiomAudit.Fixture.Clean (cmd := ("true", #[])))
  throws "malformed closure output"
    (audit `AxiomAudit.Fixture.Clean (cmd := ("echo", #["not a module"])))
  logInfo m!"errors: all five rejected"

/-! ## A closure mismatch is rejected and reported from both sides -/

run_cmd liftCoreM do
  let r ← audit `AxiomAudit.Fixture.Clean (cmd := ("echo", #["AxiomAudit.Fixture.Axiom"]))
  unless r.sourceOnly == #[`AxiomAudit.Fixture.Axiom] &&
      r.compiledOnly == #[`AxiomAudit.Fixture.Clean] do
    throwError "mismatch: source only {r.sourceOnly}, compiled only {r.compiledOnly}"
  unless r.violations.size == 1 do throwError "mismatch: violations {r.violations}"
  logInfo m!"mismatch: {r.violations[0]!}"

/-! ## The production closure covers the declaration the namespace audit missed -/

run_cmd liftCoreM do
  let r ← audit `AlgorithmicRandomness
  unless r.violations.isEmpty do throwError "production closure rejected: {r.violations}"
  unless r.checked.contains `Computable.list_foldl do
    throwError "production closure: Computable.list_foldl is not selected"
  if (`AlgorithmicRandomness).isPrefixOf `Computable.list_foldl then
    throwError "production closure: Computable.list_foldl is not a namespace blind spot"
  logInfo m!"production closure: {r.checked.size} declaration(s), Computable.list_foldl included"
