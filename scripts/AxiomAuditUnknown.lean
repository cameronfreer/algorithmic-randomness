/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AxiomAudit.Core
import AxiomAudit.Fixture.Clean

/-!
# Axiom audit regression: a constant with no defining module

Kept apart from `scripts/AxiomAuditRegression.lean`: once this file declares a constant, every
later audit in the same file reports it. Such a constant must fail the acceptance check even
though the audited closure itself is clean.

Run from the repo root, after a build, with `lake env lean scripts/AxiomAuditUnknown.lean`.
-/

open Lean Elab Command AxiomAudit

/-- Declared here, so it has no defining module. -/
theorem axiomAuditLocal : True := trivial

run_cmd liftCoreM do
  let r ← audit `AxiomAudit.Fixture.Clean
  unless r.unknown == #[`axiomAuditLocal] do throwError "unknown: {r.unknown}"
  unless r.offenders.isEmpty && r.sourceOnly.isEmpty && r.compiledOnly.isEmpty do
    throwError "unknown: the closure itself should be clean"
  unless r.violations.size == 1 do throwError "unknown: violations {r.violations}"
  logInfo m!"unknown: rejected ({r.violations[0]!})"
