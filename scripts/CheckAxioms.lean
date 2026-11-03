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

This script fails unless every declaration of the library depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`. CI runs it from the repository root after `lake build`:

```bash
lake env lean scripts/CheckAxioms.lean
```

On failure, the error lists each offending declaration with the disallowed axioms it depends on.
Typical causes are `sorry` (axiom `sorryAx`), `native_decide` (which adds an auxiliary axiom such
as `<declaration>._native.native_decide.ax_1_1`) and `axiom` declarations. On success, the script
prints a one-line summary with the number of declarations checked.

## What is checked

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

/-- Checks every declaration of the library, as described in the module docstring. -/
def run : CommandElabM Unit := do
  let env ← getEnv
  if env.header.isModule then
    throwError "scripts/CheckAxioms.lean must not be a `module`: it has to import the library at \
      the private level, where the proofs of its theorems are visible"
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
  unless violations.isEmpty do
    let sorted := violations.qsort fun v w =>
      (v.moduleName.cmp w.moduleName).then (v.declName.cmp w.declName) == .lt
    let lines := sorted.toList.map fun v => m!"\n  " ++ v.describe
    throwError m!"Axiom check failed: {violations.size} of {numDecls} declarations in \
      {numModules} modules under {libraryRoot} break the axiom policy (allowed axioms: propext, \
      Classical.choice, Quot.sound):{MessageData.joinSep lines ""}"
  logInfo m!"Axiom check passed: {numDecls} declarations in {numModules} modules under \
    {libraryRoot} depend only on propext, Classical.choice and Quot.sound."

end CheckAxioms

run_cmd CheckAxioms.run
