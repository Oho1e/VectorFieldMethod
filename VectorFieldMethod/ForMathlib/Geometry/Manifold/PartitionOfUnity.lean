/-
Copyright (c) 2026 VectorFieldMethod contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VectorFieldMethod contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Cutting off a function which is `C¹` on an open set

Let `G` be a finite-dimensional real normed space and `f : G → F` a function which is `C¹` on an
open set `U`. Multiplying `f` by a smooth function which equals `1` near a compact set `K ⊆ U` and
has compact support in `U` gives a compactly supported `C¹` function on `G` which coincides with
`f` near `K`, and near every point outside the support of `f`.

## Main statements

* `ContDiffOn.exists_contDiff_hasCompactSupport_eventuallyEq`: the cutoff construction.
-/

@[expose] public noncomputable section

open Set Filter Function Topology

variable {G F : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace ContDiffOn

/-- A function which is `C¹` on an open set `U` coincides, near every point of a compact set
`K ⊆ U` and near every point outside its support, with a compactly supported `C¹` function. -/
theorem exists_contDiff_hasCompactSupport_eventuallyEq {f : G → F} {U K : Set G}
    (hf : ContDiffOn ℝ 1 f U) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ g : G → F, ContDiff ℝ 1 g ∧ HasCompactSupport g ∧
      ∀ x, x ∈ K ∨ x ∉ tsupport f → g =ᶠ[𝓝 x] f := by
  obtain ⟨L, hLc, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨L', hL'c, hLL', hL'U⟩ := exists_compact_between hLc hU hLU
  obtain ⟨χ, hχd, -, hχs, hχ1⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := 1) isOpen_interior hLc.isClosed hLL'
  have hχt : tsupport χ ⊆ L' := closure_minimal (hχs ▸ interior_subset) hL'c.isClosed
  refine ⟨χ • f, contDiff_iff_contDiffAt.2 fun x ↦ ?_, ?_, ?_⟩
  · by_cases hx : x ∈ U
    · exact hχd.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds hx))
    · have h : χ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 fun h ↦ hx (hL'U (hχt h))
      exact (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
        (h.mono fun y hy ↦ by simp [hy])
  · exact HasCompactSupport.of_support_subset_isCompact hL'c
      ((support_smul_subset_left χ f).trans (subset_tsupport χ |>.trans hχt))
  · rintro x (hx | hx)
    · filter_upwards [isOpen_interior.mem_nhds (hKL hx)] with y hy
      simp [(hχ1 y).1 (interior_subset hy)]
    · filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx] with y hy
      simp [hy]

end ContDiffOn
