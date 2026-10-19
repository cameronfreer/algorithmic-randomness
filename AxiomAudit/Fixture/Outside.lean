/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AxiomAudit.Fixture.Axiom

/-!
# Axiom-audit fixture: outside the closure

Uses the forbidden axiom but is not imported by `AxiomAudit.Fixture.Root`, so an audit of that
root must not report it even when it is present in the environment.
-/

namespace AxiomAuditFixture

/-- Present in the environment, outside the audited closure. -/
theorem outsideLeak : True := forbidden

end AxiomAuditFixture
