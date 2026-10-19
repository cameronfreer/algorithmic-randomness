/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import AxiomAudit.Fixture.Axiom

/-!
# Axiom-audit fixture: declarations that depend on the forbidden axiom

One ordinary namespaced control, which a namespace filter would select, and three declarations
such a filter misses: one at the root namespace, one private, and a definition whose use of the
axiom sits in a compiler-generated auxiliary declaration.
-/

namespace AxiomAuditFixture

/-- The control: a namespace filter sees this one. -/
theorem controlLeak : True := forbidden

/-- Outside the namespace. -/
theorem _root_.rootLeak : True := forbidden

/-- Private: its kernel name carries the `_private` prefix. -/
private theorem privateLeak : True := forbidden

/-- The proof component is abstracted into the generated auxiliary declaration
`AxiomAuditFixture.generatedLeak._proof_1`. It has to be compound: on the pinned toolchain an
atomic proof such as `⟨0, forbidden⟩` is left in place and generates nothing. -/
def generatedLeak : Subtype fun _ : Nat ↦ True := ⟨0, (And.intro forbidden trivial).1⟩

end AxiomAuditFixture
