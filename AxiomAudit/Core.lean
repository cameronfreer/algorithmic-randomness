/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Lean

/-!
# A module-based axiom audit

Selects every kernel declaration *defined in* the repo-local import closure of a root module,
and checks that each depends, transitively, only on an allowed set of axioms.

Selection is by defining module, never by name. Private declarations, generated declarations,
and declarations outside the root namespace are therefore covered exactly like public ones. The
private and generated counts are reported, but they are only information: no classification
affects what is selected. The audit covers kernel declarations present in the environment,
generated ones included; it is not an audit of compiler-only IR helpers.

Three rules keep the audit from passing for the wrong reason.

*Locality is decided by artifact location.* A module is repo-local when its `.olean`, resolved
through the Lean search path, lies under this workspace's `.lake/build`. Both paths are
canonicalized and compared by path components. A module whose artifact cannot be resolved is an
error: it is neither classified as non-local nor classified by its name.

*The closure is cross-checked against the source closure.* `scripts/check_sorry_boundary.py
--print-closure` computes the root's closure from source text. The two sets must agree, and a
difference is reported from both sides. This compares module names only; it establishes neither
the freshness nor the origin of the artifacts, so the audit must run after a build.

*Reporting is separate from enforcement.* `audit` returns a `Report`; `Report.violations` is the
single acceptance check that both the production driver and the regression suite use. Errors
that leave no meaningful report — a root missing from the environment or the source tree, an
unresolvable module, failed or malformed script output — are thrown by `audit` itself.
-/

open Lean

namespace AxiomAudit

/-- The axioms every audited declaration may depend on. -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Where a constant was defined. -/
inductive Provenance where
  /-- Defined in the named imported module. -/
  | module (name : Name)
  /-- Not from any imported module: declared in the file running the audit. -/
  | unknown
  deriving BEq, Repr

/-- The defining module of a constant. A module index outside the header is an error. -/
def provenance (env : Environment) (n : Name) : Except String Provenance :=
  match env.getModuleIdxFor? n with
  | none => .ok .unknown
  | some i =>
    match env.header.moduleNames[i.toNat]? with
    | some m => .ok (.module m)
    | none => .error s!"constant {n} has module index {i.toNat}, which the header does not name"

/-- The workspace this audit runs in: the current directory, which must hold the lakefile. -/
def workspaceRoot : IO System.FilePath := do
  let cwd ← IO.currentDir
  unless ← (cwd / "lakefile.toml").pathExists do
    throw <| IO.userError s!"axiom audit: no lakefile.toml in {cwd}; run from the repo root"
  return cwd

/-- The canonical build directory of the workspace. -/
def buildDir (ws : System.FilePath) : IO System.FilePath := do
  let d := ws / ".lake" / "build"
  unless ← d.isDir do
    throw <| IO.userError s!"axiom audit: no build directory {d}; build before auditing"
  realPathNormalized d

/-- Whether a module's artifact lies under the build directory. An unresolvable artifact is an
error, not a verdict. -/
def isLocalModule (build : System.FilePath) (m : Name) : IO Bool := do
  let sp ← searchPathRef.get
  let some p ← sp.findModuleWithExt "olean" m
    | throw <| IO.userError s!"axiom audit: cannot resolve the .olean of {m} on the search path"
  let p ← realPathNormalized p
  return build.components.isPrefixOf p.components

/-- The repo-local import closure of `root`, read from the compiled module headers. The root must
be imported, repo-local, and present as a source file. -/
def localClosure (env : Environment) (ws : System.FilePath) (root : Name) :
    IO (Array Name) := do
  let build ← buildDir ws
  let idx : Std.HashMap Name Nat :=
    env.header.moduleNames.foldl (init := {}) fun acc m ↦ acc.insert m acc.size
  unless idx.contains root do
    throw <| IO.userError s!"axiom audit: root {root} is not in the imported environment"
  unless ← (modToFilePath ws root "lean").pathExists do
    throw <| IO.userError s!"axiom audit: root {root} has no source file in {ws}"
  unless ← isLocalModule build root do
    throw <| IO.userError s!"axiom audit: root {root} is not a module of this workspace"
  let mut seen : Std.HashSet Name := {}
  let mut stack : Array Name := #[root]
  while h : stack.size > 0 do
    let m := stack[stack.size - 1]
    stack := stack.pop
    if seen.contains m then continue
    seen := seen.insert m
    let some i := idx[m]?
      | throw <| IO.userError s!"axiom audit: imported module {m} is missing from the header"
    let some data := env.header.moduleData[i]?
      | throw <| IO.userError s!"axiom audit: no module data for {m}"
    for imp in data.imports do
      if !seen.contains imp.module && (← isLocalModule build imp.module) then
        stack := stack.push imp.module
  return seen.toArray.qsort Name.lt

/-- The command producing the source closure: the sorry-boundary script, one module per line. -/
def sourceClosureCmd (root : Name) : String × Array String :=
  ("python3", #["scripts/check_sorry_boundary.py", "--print-closure", "--root", root.toString])

/-- Run the source-closure command and parse its output. Failure and malformed output are
errors. -/
def sourceClosure (ws : System.FilePath) (cmd : String × Array String) : IO (Array Name) := do
  let out ← IO.Process.output { cmd := cmd.1, args := cmd.2, cwd := ws }
  unless out.exitCode == 0 do
    throw <| IO.userError
      s!"axiom audit: `{cmd.1}` exited with {out.exitCode}:\n{out.stderr}"
  let mut mods : Array Name := #[]
  for line in out.stdout.splitOn "\n" do
    if line.isEmpty then continue
    let n := line.toName
    if n.isAnonymous || n.toString != line then
      throw <| IO.userError s!"axiom audit: malformed module name in source closure: {repr line}"
    mods := mods.push n
  if mods.isEmpty then
    throw <| IO.userError "axiom audit: the source closure is empty"
  return mods.qsort Name.lt

/-- What an audit found. Every array is sorted. -/
structure Report where
  root : Name
  modules : Array Name
  /-- Modules in the source closure only. -/
  sourceOnly : Array Name
  /-- Modules in the compiled closure only. -/
  compiledOnly : Array Name
  /-- Every declaration selected by its defining module. -/
  checked : Array Name
  privateCount : Nat
  internalCount : Nat
  /-- Selected constants that the module index attributes to a module outside the closure. -/
  sharedCount : Nat
  /-- Declaration and forbidden axiom. -/
  offenders : Array (Name × Name)
  /-- Constants with no defining module. -/
  unknown : Array Name

/-- Every constant recorded by one of `modules`, read from the module headers: selection by
defining module, with no filtering on name, privacy, or internality, and without duplicates.

A declaration realized on demand, such as an equation lemma, can be recorded by several modules,
and the environment's module index keeps only one of them. Such a declaration is selected when
any module of the closure records it. The index is still checked: every selected constant must
resolve to a module, in the closure or not, whose header records it. Also returned is how many
selected constants resolve to a module other than one recording them in the closure. -/
def selectByModule (env : Environment) (modules : Array Name) :
    Except String (Array Name × Nat) := do
  let idx : Std.HashMap Name Nat :=
    env.header.moduleNames.foldl (init := {}) fun acc m ↦ acc.insert m acc.size
  let mut seen : Std.HashSet Name := {}
  let mut out : Array Name := #[]
  let mut shared := 0
  for m in modules do
    let some i := idx[m]? | throw s!"module {m} is missing from the header"
    let some data := env.header.moduleData[i]? | throw s!"no module data for {m}"
    for n in data.constNames do
      if seen.contains n then continue
      seen := seen.insert n
      match provenance env n with
      | .ok (.module m') =>
        unless m' == m do
          let recorded := (do
            let i' ← idx[m']?
            let data' ← env.header.moduleData[i']?
            pure (data'.constNames.contains n)).getD false
          unless recorded do
            throw s!"constant {n} of module {m} resolves to {m'}, which does not record it"
          unless modules.contains m' do shared := shared + 1
      | .ok .unknown => throw s!"constant {n} of module {m} has no module index"
      | .error e => throw e
      out := out.push n
  return (out, shared)

/-- Every constant with no defining module: the local stage of the environment, each checked to
resolve to `unknown`. -/
def unknownConstants (env : Environment) : Except String (Array Name) := do
  let local_ := env.constants.foldStage2 (fun acc n _ ↦ acc.push n) #[]
  for n in local_ do
    match provenance env n with
    | .ok .unknown => pure ()
    | .ok (.module m) => throw s!"local constant {n} resolves to the imported module {m}"
    | .error e => throw e
  return local_

/-- Audit the closure of `root`. -/
def audit (root : Name) (allowed : List Name := standardAxioms)
    (cmd : String × Array String := sourceClosureCmd root) : CoreM Report := do
  let env ← getEnv
  let ws ← workspaceRoot
  let modules ← localClosure env ws root
  let source ← sourceClosure ws cmd
  let modSet := Std.HashSet.ofArray modules
  let srcSet := Std.HashSet.ofArray source
  let (checked, sharedCount) ← match selectByModule env modules with
    | .ok c => pure c
    | .error e => throwError "axiom audit: {e}"
  let unknown ← match unknownConstants env with
    | .ok u => pure u
    | .error e => throwError "axiom audit: {e}"
  let mut privateCount := 0
  let mut internalCount := 0
  let mut offenders : Array (Name × Name) := #[]
  for n in checked do
    if isPrivateName n then privateCount := privateCount + 1
    else if n.isInternal then internalCount := internalCount + 1
    for a in ← collectAxioms n do
      unless allowed.contains a do
        offenders := offenders.push (n, a)
  return {
    root, modules
    sourceOnly := source.filter (!modSet.contains ·)
    compiledOnly := modules.filter (!srcSet.contains ·)
    checked := checked.qsort Name.lt
    privateCount, internalCount, sharedCount
    offenders := offenders.qsort fun p q ↦ Name.lt p.1 q.1 || (p.1 == q.1 && Name.lt p.2 q.2)
    unknown := unknown.qsort Name.lt }

/-- **The acceptance check.** Every reason to reject a report; empty exactly when it passes. -/
def Report.violations (r : Report) : Array String := Id.run do
  let mut v : Array String := #[]
  unless r.sourceOnly.isEmpty && r.compiledOnly.isEmpty do
    v := v.push s!"closure mismatch for {r.root}: source only {r.sourceOnly.toList}, \
      compiled only {r.compiledOnly.toList}"
  for (n, a) in r.offenders do
    v := v.push s!"{n} depends on the forbidden axiom {a}"
  for n in r.unknown do
    v := v.push s!"{n} has no defining module"
  return v

/-- The one-line inventory. -/
def Report.summary (r : Report) : String :=
  s!"axiom audit of {r.root}: {r.modules.size} module(s), {r.checked.size} declaration(s) \
    ({r.privateCount} private, {r.internalCount} other generated, {r.sharedCount} indexed \
    outside the closure) use only allowed axioms"

/-- Audit and enforce: throw on any violation, otherwise log the inventory. -/
def run (root : Name) (allowed : List Name := standardAxioms) : CoreM Unit := do
  let r ← audit root allowed
  let v := r.violations
  unless v.isEmpty do
    throwError "axiom audit failed:\n{"\n".intercalate v.toList}"
  logInfo r.summary

end AxiomAudit
