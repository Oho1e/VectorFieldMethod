/-
Copyright (c) 2026 VectorFieldMethod contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VectorFieldMethod contributors
-/
module

public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Separation.Basic

/-!
# Compact support of slices

If `f : α × β → M` has compact support, then so do its slices `a ↦ f (a, b)` and `b ↦ f (a, b)`.
These results belong next to `HasCompactSupport.comp_isClosedEmbedding` in
`Mathlib.Topology.Algebra.Support`.

## Main statements

* `HasCompactSupport.comp_prodMkLeft`: compact support of `a ↦ f (a, b)`.
* `HasCompactSupport.comp_prodMkRight`: compact support of `b ↦ f (a, b)`.
-/

@[expose] public noncomputable section

variable {α β M : Type*} [TopologicalSpace α] [TopologicalSpace β] [Zero M]

namespace HasCompactSupport

/-- A slice `a ↦ f (a, b)` of a function with compact support has compact support. -/
theorem comp_prodMkLeft [T1Space β] {f : α × β → M} (hf : HasCompactSupport f) (b : β) :
    HasCompactSupport fun a ↦ f (a, b) :=
  hf.comp_isClosedEmbedding
    (.of_isEmbedding_isClosedMap (isEmbedding_prodMkLeft b) (isClosedMap_prodMk_right b))

/-- A slice `b ↦ f (a, b)` of a function with compact support has compact support. -/
theorem comp_prodMkRight [T1Space α] {f : α × β → M} (hf : HasCompactSupport f) (a : α) :
    HasCompactSupport fun b ↦ f (a, b) :=
  hf.comp_isClosedEmbedding
    (.of_isEmbedding_isClosedMap (isEmbedding_prodMkRight a) (isClosedMap_prodMk_left a))

end HasCompactSupport
