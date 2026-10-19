/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AlgorithmicRandomness
import AxiomAudit.Core

/-!
# Axiom audit

Every kernel declaration defined in a module of the root import spine — public, private, or
generated, in any namespace — must depend only on the standard axioms `propext`,
`Classical.choice`, and `Quot.sound`. Declarations are selected by their defining module, not by
name, over the same module closure `scripts/check_sorry_boundary.py` checks for sorries; the two
closures are cross-checked. See `AxiomAudit.Core` for the rules.

Run from the repo root, after a build, with `lake env lean scripts/AxiomAudit.lean`; it exits
nonzero on any violation. This file declares nothing: a local constant would have no defining
module and would fail the audit.
-/

run_cmd Lean.Elab.Command.liftCoreM <| AxiomAudit.run `AlgorithmicRandomness
