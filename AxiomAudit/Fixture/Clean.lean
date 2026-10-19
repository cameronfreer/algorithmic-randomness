/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# Axiom-audit fixture: a clean root

A closure using only the standard axioms, which the audit must accept.
-/

namespace AxiomAuditFixture

/-- Uses `propext`, which is allowed. -/
theorem cleanUsesPropext (p : Prop) (h : p) : p = True := propext ⟨fun _ ↦ trivial, fun _ ↦ h⟩

end AxiomAuditFixture
