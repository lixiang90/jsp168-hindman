import Hindman168.AlignmentBoxMeans
import Mathlib.Algebra.Order.Floor.Ring

namespace Hindman168
open scoped Classical

theorem alignment_ceil_interval_mem (L U : ℝ) (z : ℤ) :
    z ∈ Finset.Ico ⌈L⌉ ⌈U⌉ ↔ L ≤ (z : ℝ) ∧ (z : ℝ) < U := by
  simp only [Finset.mem_Ico, Int.ceil_le, Int.lt_ceil]

theorem alignment_ceil_class_mem (L U : ℝ) (d r z : ℤ) :
    z ∈ alignmentIntervalClass ⌈L⌉ ⌈U⌉ d r ↔
      (L ≤ (z : ℝ) ∧ (z : ℝ) < U) ∧ Int.ModEq d r z := by
  simp only [alignmentIntervalClass, Finset.mem_filter, alignment_ceil_interval_mem]

theorem alignment_ceil_box_mem {ι : Type*} [Fintype ι]
    (L U : ι → ℝ) (d : ℤ) (r z : ι → ℤ) :
    z ∈ alignmentBoxClass (fun j => ⌈L j⌉) (fun j => ⌈U j⌉) r d ↔
      ∀ j, (L j ≤ (z j : ℝ) ∧ (z j : ℝ) < U j) ∧ Int.ModEq d (r j) (z j) := by
  simp only [alignmentBoxClass, Fintype.mem_piFinset, alignment_ceil_class_mem]

theorem alignment_ceil_endpoint_bound (L N C : ℝ) (hN : 1 ≤ N)
    (hL : |L| ≤ C * N) : |(⌈L⌉ : ℝ)| ≤ (C + 1) * N := by
  have hl := Int.le_ceil L
  have hu := Int.ceil_lt_add_one L
  have h := abs_le.mp hL
  rw [abs_le]
  constructor <;> nlinarith

theorem alignment_ceil_side_bounds (L U N c C : ℝ) (hN : 1 ≤ N)
    (hlarge : 2 ≤ c * N) (hlen : c * N ≤ U - L)
    (hL : -C * N ≤ L) (hU : U ≤ C * N) :
    (c / 2) * N ≤ (⌈U⌉ : ℝ) - (⌈L⌉ : ℝ) ∧
      (⌈U⌉ : ℝ) - (⌈L⌉ : ℝ) ≤ (2 * C + 1) * N := by
  have hl0 := Int.le_ceil L
  have hl1 := Int.ceil_lt_add_one L
  have hu0 := Int.le_ceil U
  have hu1 := Int.ceil_lt_add_one U
  constructor <;> nlinarith

end Hindman168
