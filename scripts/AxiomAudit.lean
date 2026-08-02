/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness
import Lean

/-!
# Axiom audit

Every declaration owned by the `AlgorithmicRandomness` namespace must depend only on the
standard axioms `propext`, `Classical.choice`, and `Quot.sound`. This sweeps the environment
rather than a hand-curated list, so a new declaration cannot silently introduce an axiom by
being forgotten.

Run with `lake env lean scripts/AxiomAudit.lean`; it exits nonzero on any violation.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut offenders : Array (Name × Name) := #[]
  let mut checked : Nat := 0
  for (n, _) in env.constants.toList do
    if (`AlgorithmicRandomness).isPrefixOf n && !n.isInternal then
      checked := checked + 1
      let axs ← liftCoreM <| collectAxioms n
      for a in axs do
        unless allowed.contains a do
          offenders := offenders.push (n, a)
  if offenders.isEmpty then
    logInfo s!"axiom audit: {checked} declaration(s) use only propext, Classical.choice, Quot.sound"
  else
    throwError "axiom audit failed: {offenders}"
