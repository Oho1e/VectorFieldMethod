/-
Copyright (c) 2026 VectorFieldMethod contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VectorFieldMethod contributors
-/
import VectorFieldMethod
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Axiom check

This script fails unless every Lean file of the library is imported by the root module, and every
declaration of the library depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`. CI runs it from the repository root after `lake build`:

```bash
lake env lean scripts/CheckAxioms.lean
```

On failure, the error lists each Lean file that is not imported, and each offending declaration
with the disallowed axioms it depends on. Typical causes of the latter are `sorry` (axiom
`sorryAx`), `native_decide` (which adds an auxiliary axiom such as
`<declaration>._native.native_decide.ax_1_1`) and `axiom` declarations. On success, the script
prints a one-line summary with the numbers of files and declarations checked.

## What is checked

* `VectorFieldMethod.lean` and every `.lean` file under `VectorFieldMethod/` must be a module of
  the environment, that is, be imported directly or indirectly by the root module
  `VectorFieldMethod`, which this file imports. A file that is not imported is neither built by
  `lake build` nor seen by the checks below. The files are located from the path of this file,
  which must therefore stay in `scripts/`.
* The declarations checked are all constants of the environment whose defining module is
  `VectorFieldMethod` or a module under it, including private declarations and declarations
  generated automatically (auxiliary proofs, matchers, equation lemmas, instances, ...).
* For each of them, `Lean.collectAxioms`, which also implements `#print axioms`, computes the
  axioms it depends on transitively. It uses the axiom lists that Lean computes from the full
  proofs when it writes the `.olean` files, and walks the proofs of the declarations without such
  a list (the private ones). Only `propext`, `Classical.choice` and `Quot.sound` are allowed.
* A constant of the library that is itself an axiom is a violation too, whether it was declared
  with `axiom` or generated (as `native_decide` does).

## Why this file is not a `module`

The library uses the module system: the public `.olean` of a module stores each theorem as an
axiom without its proof, and leaves out private declarations. A file that is not a `module`
imports every module at the private level (`.olean.private`), so that all declarations of the
library are visible here with their proofs. Keep this file a plain Lean file.
-/

open Lean Elab Command

namespace CheckAxioms

/-- The axioms that declarations of the library may depend on. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The root of the module names of the library. -/
def libraryRoot : Name := `VectorFieldMethod

/-- The `.lean` files under the directory `repoDir / dir`, as paths relative to `repoDir`. -/
partial def leanFilesUnder (repoDir dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut files := #[]
  for entry in (← (repoDir / dir).readDir) do
    let path := dir / entry.fileName
    if (← (repoDir / path).isDir) then
      files := files ++ (← leanFilesUnder repoDir path)
    else if path.extension == some "lean" then
      files := files.push path
  return files

/-- The name of the module whose source file is `path`, relative to the repository root. -/
def moduleNameOfPath (path : System.FilePath) : Name :=
  (path.withExtension "").components.foldl Name.mkStr .anonymous

/-- A declaration of the library that breaks the axiom policy. -/
structure Violation where
  /-- The declaration. -/
  declName : Name
  /-- The module that defines it. -/
  moduleName : Name
  /-- Whether the declaration is itself an axiom. -/
  isAxiom : Bool
  /-- The disallowed axioms it depends on, other than itself. -/
  axioms : Array Name

/-- Shows a private name as its user-facing name, marked as private. -/
def showName (n : Name) : MessageData :=
  match privateToUserName? n with
  | some userName => m!"{userName} (private)"
  | none => m!"{n}"

/-- The line of the failure report describing `v`. -/
def Violation.describe (v : Violation) : MessageData :=
  let deps := MessageData.joinSep (v.axioms.toList.map showName) ", "
  let problem :=
    if !v.isAxiom then m!"depends on {deps}"
    else if v.axioms.isEmpty then m!"is an axiom"
    else m!"is an axiom whose statement depends on {deps}"
  let visibility := if isPrivateName v.declName then "private, " else ""
  m!"{privateToUserName v.declName} ({visibility}module {v.moduleName}) {problem}"

/-- Runs the import check and the axiom check, as described in the module docstring. -/
def run : CommandElabM Unit := do
  let env ← getEnv
  if env.header.isModule then
    throwError "scripts/CheckAxioms.lean must not be a `module`: it has to import the library at \
      the private level, where the proofs of its theorems are visible"
  -- Import check: every Lean file of the library is a module of the environment.
  let some repoDir := (← IO.FS.realPath (← getFileName)).parent.bind (·.parent)
    | throwError "cannot locate the repository root from the path of this file"
  let rootFile : System.FilePath := s!"{libraryRoot}.lean"
  unless (← (repoDir / rootFile).pathExists) do
    throwError "{rootFile} not found in {repoDir}: this file must stay in scripts/"
  let files := #[rootFile] ++
    (← leanFilesUnder repoDir libraryRoot.toString).qsort (·.toString < ·.toString)
  let unimported := files.filter fun file =>
    !env.header.moduleNames.contains (moduleNameOfPath file)
  -- Axiom check: every declaration of the library depends only on the allowed axioms.
  let mut numModules := 0
  let mut numDecls := 0
  let mut violations : Array Violation := #[]
  for (moduleName, modIdx) in env.header.moduleNames.zipIdx do
    unless libraryRoot.isPrefixOf moduleName do continue
    numModules := numModules + 1
    let some data := env.header.moduleData[modIdx]?
      | throwError "no module data for {moduleName}"
    for declName in data.constNames do
      -- A constant stored in several modules is checked once, with the module it is assigned to.
      unless (env.getModuleIdxFor? declName).map (·.toNat) == some modIdx do continue
      let some info := env.find? declName
        | throwError "{declName} is listed in {moduleName} but missing from the environment"
      numDecls := numDecls + 1
      let bad := (← collectAxioms declName).filter fun ax =>
        ax != declName && !allowedAxioms.contains ax
      let isAxiom := info matches .axiomInfo _
      if isAxiom || !bad.isEmpty then
        violations := violations.push { declName, moduleName, isAxiom, axioms := bad }
  if numDecls == 0 then
    throwError "no declarations found in modules under {libraryRoot}"
  -- Report all problems of both checks together.
  let mut problems : Array MessageData := #[]
  unless unimported.isEmpty do
    let lines := unimported.toList.map fun file =>
      m!"\n  {file} (module {moduleNameOfPath file})"
    let verb := if unimported.size == 1 then "is" else "are"
    problems := problems.push m!"Import check failed: {unimported.size} of {files.size} Lean \
      files of the library {verb} not imported, directly or indirectly, by the root module \
      {libraryRoot}:{MessageData.joinSep lines ""}"
  unless violations.isEmpty do
    let sorted := violations.qsort fun v w =>
      (v.moduleName.cmp w.moduleName).then (v.declName.cmp w.declName) == .lt
    let lines := sorted.toList.map fun v => m!"\n  " ++ v.describe
    let verb := if violations.size == 1 then "breaks" else "break"
    problems := problems.push m!"Axiom check failed: {violations.size} of {numDecls} \
      declarations in {numModules} modules under {libraryRoot} {verb} the axiom policy (allowed \
      axioms: propext, Classical.choice, Quot.sound):{MessageData.joinSep lines ""}"
  unless problems.isEmpty do
    throwError (MessageData.joinSep problems.toList "\n")
  logInfo m!"Axiom check passed: all {files.size} Lean files of the library are imported by the \
    root module {libraryRoot}, and its {numDecls} declarations in {numModules} modules depend \
    only on propext, Classical.choice and Quot.sound."

end CheckAxioms

run_cmd CheckAxioms.run
