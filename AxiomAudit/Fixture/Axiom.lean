/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# Axiom-audit fixture: the forbidden axiom

A deliberately forbidden axiom, for the negative tests of the axiom audit only. Nothing outside
`AxiomAudit/Fixture/` may import this.
-/

namespace AxiomAuditFixture

/-- An axiom the audit must reject. It is true, so it is harmless as well as forbidden. -/
axiom forbidden : True

end AxiomAuditFixture
