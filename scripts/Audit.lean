/-
Copyright (c) 2026 TauCeti contributors and SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TauCeti contributors, SphereCeti contributors
-/
import Mathlib.Init
import Mathlib.Tactic.SetNotationForOrder
import Mathlib.Tactic.Linter.TextBased

/-!
# Compiled SphereCeti audits

Adapted from TauCetiProject/TauCeti@b743b607ce3e9742b18026ad79082e5d15badff5:
`scripts/Axioms.lean`, `scripts/ModuleSystem.lean`, `scripts/HeaderStyle.lean`, and
`scripts/lint-env.sh` (Apache-2.0). See `docs/infrastructure/compiled-audits.md`.

This legacy driver deliberately loads the private olean level, including private declarations,
proof bodies, and docstrings. It returns structured findings rather than parsing `#lint` prose.
The approved Python caller owns inventory and exception policy. No candidate helper is imported.
-/

open Lean Meta Batteries.Tactic.Lint

structure Source where
  name : String
  path : String
  kind : String
  deriving FromJson, ToJson

structure DeclarationRecord where
  moduleName : String
  name : String
  axioms : Array String
  deriving ToJson

structure Finding where
  moduleName : String
  name : String
  linter : String
  message : String
  deriving ToJson

structure ModuleRecord where
  name : String
  isModule : Bool
  imports : Array String
  deriving ToJson

structure Report where
  schema_version : Nat := 1
  modules : Array ModuleRecord
  declarations : Array DeclarationRecord
  linters : Array String
  findings : Array Finding
  nolints : Array Finding
  deriving ToJson

/-- Deep-copy import strings as well as flags before freeing the mmap. `Name.toString` alone
may return a string still backed by that region; TauCeti's Boolean-only audit does not need this. -/
@[noinline] def copyModuleInfo (name : String) (data : ModuleData) : BaseIO ModuleRecord :=
  pure {
    name, isModule := data.isModule
    imports := data.imports.map (fun i => String.ofList i.module.toString.toList) }

/-- Inspect actual compiled metadata; absent or unreadable artifacts are fatal. -/
def moduleInfo (name : String) : IO ModuleRecord := do
  let olean ← findOLean name.toName
  let (data, region) ← readModuleData olean
  let result ← copyModuleInfo name data
  unsafe region.free
  return result

/-- Match TauCeti's module-system-reliable replacement for docBlame. -/
def needsDoc (name : Name) : MetaM Bool := do
  if (← getEnv).isPrivateOrAutoDecl name then return false
  if ← isInstance name then return false
  if let .str parent part := name then
    if ← isInstance parent then return false
    if ["parenthesizer", "formatter", "delaborator", "quot"].contains part then return false
  match ← getConstInfo name with
  | .axiomInfo .. | .opaqueInfo .. | .inductInfo .. => return true
  | .defnInfo info => return !(← isProjectionFn name) || !(← isProp info.type)
  | _ => return false

/-- Audit by defining module, never by declaration namespace or theorem-only filtering. -/
def inspect (sources : Array Source) : CoreM Report := do
  let env ← getEnv
  let names := env.allImportedModuleNames
  let owner (name : Name) : Option Source := do
    let idx ← env.getModuleIdxFor? name
    let mod ← names[idx.toNat]?
    sources.find? (·.name == mod.toString)
  let all := env.constants.fold (init := #[]) fun acc name _ =>
    if (owner name).isSome then acc.push name else acc
  let all := all.qsort Name.quickLt
  let mut declarations : Array DeclarationRecord := #[]
  let mut findings : Array Finding := #[]
  for name in all do
    let some source := owner name | throwError "missing declaration owner: {name}"
    -- Stock collection follows types AND values, including definitions and private declarations.
    -- No shared Boolean memo sentinel: exact dependency sets are required for the roadmap ledger.
    let axioms ← collectAxioms name
    declarations := declarations.push {
      moduleName := source.name
      name := name.toString
      axioms := (axioms.map Name.toString).qsort (· < ·) }
    if source.kind == "library" && (← (needsDoc name).run') then
      if (← findDocString? env name).isNone then
        findings := findings.push {
          moduleName := source.name
          name := name.toString
          linter := "docString", message := "missing documentation string" }
  -- Check docstring visibility independently of the current (possibly empty) library.
  if (← findDocString? env ``Nat).isNone || (← findDocString? env ``List).isNone then
    throwError "docstring calibration failed at the private import level"
  let linters ← getChecks true none none
  let linters := linters.filter (·.name != `docBlame)
  let libraryDecls := all.filter fun name =>
    (owner name).any (·.kind == "library") && !env.isAutoDecl name
  for (linter, messages) in ← lintCore libraryDecls linters do
    for (name, message) in messages.toArray do
      let some source := owner name | throwError "linter returned a foreign declaration: {name}"
      findings := findings.push {
        moduleName := source.name
        name := name.toString
        linter := linter.name.toString, message := ← message.toString }
  -- Read every persistent nolint application, including multi-name/multi-linter forms.
  let mut nolints : Array Finding := #[]
  let mut importedNolints := 0
  for idx in [:names.size] do
    let entries := nolintAttr.ext.getModuleEntries env idx
    importedNolints := importedNolints + entries.size
    if let some source := sources.find? (·.name == names[idx]!.toString) then
      if source.kind == "library" then
        for (name, linters) in entries do
          for linter in linters do
            nolints := nolints.push {
              moduleName := source.name
              name := name.toString
              linter := linter.toString, message := "explicit nolint application" }
  if importedNolints == 0 then
    throwError "nolint calibration failed: no imported persistent entries visible"
  let modules ← sources.mapM fun source => moduleInfo source.name
  return {
    modules, declarations, findings, nolints
    linters := (linters.map (·.name.toString)).qsort (· < ·) }

/-- Apply Mathlib's source linters directly to the complete validated source list. -/
def sourceStyle (sources : Array Source) : IO (Array Finding) := do
  let mut findings : Array Finding := #[]
  for source in sources do
    let text ← IO.FS.readFile source.path
    for (_, message) in Mathlib.Linter.copyrightHeaderChecks text
        Mathlib.Linter.linter.style.header.license.defValue do
      findings := findings.push {
        moduleName := source.name
        name := source.path
        linter := "header", message }
    let options : Lean.Linter.LinterOptions := { toOptions := {}, linterSets := {} }
    let modules := #[source.name.toName]
    let names ← Mathlib.Linter.TextBased.modulesNotUpperCamelCase options modules
    let paths ← Mathlib.Linter.TextBased.modulesOSForbidden options modules
    if names + paths != 0 then
      throw <| IO.userError s!"Mathlib module-name lint rejected {source.path}"
    let errors ← Mathlib.Linter.TextBased.lintModules options #[] modules .humanReadable false
    if errors != 0 then
      throw <| IO.userError s!"Mathlib source-style lint rejected {source.path}"
    if !text.endsWith "\n" then
      findings := findings.push {
        moduleName := source.name
        name := source.path
        linter := "finalNewline", message := "source must end with a newline" }
  return findings

/-- Return normally so Lean tears down runtime state in order. -/
unsafe def main (args : List String) : IO UInt32 := do
  let [request, output] := args | throw <| IO.userError "expected inventory JSON and report path"
  let parsed ← IO.ofExcept <| Json.parse (← IO.FS.readFile request)
  let sources : Array Source ← IO.ofExcept <| fromJson? parsed
  if sources.isEmpty then throw <| IO.userError "empty audit inventory"
  initSearchPath (← findSysroot)
  enableInitializersExecution
  -- Lint requires extensions; keep this environment until process exit rather than freeing
  -- mmap regions that loaded extension data may still reference. Axiom bodies use private data.
  let imports := #[`Mathlib.Init, `Mathlib.Tactic.SetNotationForOrder,
    `Mathlib.Tactic.Linter.TextBased] ++ sources.map (·.name.toName)
  let env ← importModules (imports.map fun module => { module }) {}
    (trustLevel := 1024) (loadExts := true) (leakEnv := true) (level := .private)
  let (report, _) ← Core.CoreM.toIO (inspect sources)
    { fileName := "<SphereCeti audit>", fileMap := default } { env }
  let report := { report with findings := report.findings ++ (← sourceStyle sources) }
  IO.FS.writeFile output ((toJson report).compress ++ "\n")
  return 0
