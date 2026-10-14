import Hindman168.AlignmentRawPivotSplit
import Hindman168.MasterMultipliedBoundaryLimit
import Hindman168.AlignedSqrtMicrocellGrowth

namespace Hindman168

open FiniteMass Filter
open scoped BigOperators Topology Classical

theorem alignment_raw_block_boundary_tendsto
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (i : Fin n)
    (T : Finset (Fin n)) (hT : ∀ j ∈ T, j < i) :
    Tendsto (fun w => event (globalRawMass (F.cutoff w) (primorial w) n)
      (fun x => ¬ intervalInteriorRoot (F.gap w i.val)
        (3 * F.auxiliary w i.val * alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w))
        ((alignmentNaturalBlockProduct x T * x i : ℕ) : ℤ))) atTop (𝓝 0) := by
  have hh := master_multipliedBoundary_alignedSqrt_tendsto hF (fun _ => i)
    (fun w => F.auxiliary w i.val) (fun w => F.modulus w) 3
    (fun w => alignmentOutsideRawMass F w i)
    (fun _ x => alignmentNaturalBlockProduct (insertPivotCoordinate i x 1) T)
    (fun w _ => 3 * F.auxiliary w i.val * alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w))
    (Eventually.of_forall (fun _ => le_rfl)) (by
      filter_upwards [alignmentOutsideRawMass_geometry hF i] with w hw
      refine ⟨hw.1, hw.2.1, ?_⟩
      intro x hx
      have hg := hw.2.2 x hx
      refine ⟨Finset.prod_pos (fun j hj => (hg j (hT j hj)).1), ?_, ?_, le_rfl⟩
      · exact (alignmentNaturalBlockProduct_coprime _ T _
          (fun j hj => (hg j (hT j hj)).2.2)).symm
      · exact alignment_earlier_block_product_bound hF w i _
          (fun j hj => (hg j hj).2.1) T hT)
  have he (w : ℕ) := alignment_raw_pivot_event F w i
    (fun x => ¬ intervalInteriorRoot (F.gap w i.val)
      (3 * F.auxiliary w i.val * alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w))
      ((alignmentNaturalBlockProduct x T * x i : ℕ) : ℤ))
  simp_rw [alignment_block_insert_pivot i _ _ 1 T hT, insertPivotCoordinate_self] at he
  exact hh.congr' (Eventually.of_forall (fun w => (he w).symm))

theorem alignment_raw_finite_boundary_tendsto
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (i : Fin n)
    (S : Finset (Finset (Fin n))) (hS : ∀ T ∈ S, ∀ j ∈ T, j < i) :
    Tendsto (fun w => event (globalRawMass (F.cutoff w) (primorial w) n)
      (fun x => ∃ T ∈ S, ¬ intervalInteriorRoot (F.gap w i.val)
        (3 * F.auxiliary w i.val * alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w))
        ((alignmentNaturalBlockProduct x T * x i : ℕ) : ℤ))) atTop (𝓝 0) := by
  have hsum := tendsto_finsetSum S (fun T hT => alignment_raw_block_boundary_tendsto hF i T (hS T hT))
  simp only [Finset.sum_const_zero] at hsum
  have hn : ∀ᶠ w in atTop, ∀ x, 0 ≤ globalRawMass (F.cutoff w) (primorial w) n x := by
    filter_upwards [hF.raw_cutoffs_valid] with w hw
    exact piMass_nonneg _ (fun j p => by
      rw [rawMass_apply]
      exact harmonicWeight_nonneg (hw j.val (Finset.mem_range.mpr j.isLt)).2.2 p)
  apply squeeze_zero' _ _ hsum
  · filter_upwards [hn] with w hw
    exact event_nonneg _ _ hw
  · filter_upwards [hn] with w hw
    exact event_union_bound _ S _ hw

end Hindman168
