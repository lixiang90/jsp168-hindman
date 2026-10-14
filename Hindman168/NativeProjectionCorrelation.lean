import Hindman168.NativeHilbertClippedApproximation
import Hindman168.SubprobabilityHilbertBounds

/-! The correlation-to-projection step of the subgroup inverse argument,
on the actual native subspace and exact original weighted Hilbert law. -/
namespace Hindman168
open FiniteMass Filter
open scoped Topology
universe u

theorem subspace_inner_abs_le_projection_norm {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (V : Submodule ℝ E) [V.HasOrthogonalProjection] (h v : E)
    (hv : v ∈ V) (hn : ‖v‖ ≤ 1) : |inner ℝ h v| ≤ ‖V.starProjection h‖ := by
  have he := V.starProjection_inner_eq_zero h v hv
  rw [inner_sub_left, sub_eq_zero] at he
  rw [he]
  exact (abs_real_inner_le_norm _ _).trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hn (norm_nonneg (V.starProjection h)))

variable (s : ℕ) {N : ℕ} (F : MasterParameterFamily)
  (μ : ℕ → Mass ℤ) [∀ w, Fact (∀ y, 0 ≤ μ w y)] (U : Ultrafilter ℕ)
  (gap : ℕ → Fin N)

theorem nativeHilbert_correlation_bound (hprob : ∀ w, total (μ w) ≤ 1)
    (h v : boundedHilbertFamilies (fun w => FiniteMassL2 (μ w)))
    (hv : NativePieceRepresented.{u} s F gap (fun w y => v.val w y))
    (hb : ∀ w y, y ∈ (μ w).support → |v.val w y| ≤ 1) :
    |inner ℝ (hilbertFamilyToCompletion _ U h) (hilbertFamilyToCompletion _ U v)| ≤
      ‖(nativeNilHilbertSubspace.{u} s F μ U gap).starProjection (hilbertFamilyToCompletion _ U h)‖ := by
  apply subspace_inner_abs_le_projection_norm
  · exact nativeHilbertRepresentation_mem_closed s F μ U gap ⟨v, hv, rfl⟩
  · apply hilbertFamilyToCompletion_norm_le _ U v zero_le_one
    exact fun w => finiteMassL2_norm_le_subprob (μ w) (hprob w) (v.val w) zero_le_one (hb w)

theorem nativeHilbert_projection_lower_of_eventual_correlation
    (hprob : ∀ w, total (μ w) ≤ 1)
    (h v : boundedHilbertFamilies (fun w => FiniteMassL2 (μ w)))
    (hv : NativePieceRepresented.{u} s F gap (fun w y => v.val w y))
    (hb : ∀ w y, y ∈ (μ w).support → |v.val w y| ≤ 1)
    (c : ℝ) (err : ℕ → ℝ) (herr : Tendsto err (U : Filter ℕ) (𝓝 0))
    (hc : ∀ᶠ w in (U : Filter ℕ), c - err w ≤ expectation (μ w) (fun y => h.val w y * v.val w y)) :
    c ≤ ‖(nativeNilHilbertSubspace.{u} s F μ U gap).starProjection (hilbertFamilyToCompletion _ U h)‖ := by
  have ht : Tendsto (fun w => c - err w) (U : Filter ℕ) (𝓝 c) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub herr
  have hi := le_of_tendsto_of_tendsto ht (finiteMassHilbert_expectation_tendsto μ U h v) hc
  exact hi.trans ((le_abs_self _).trans (nativeHilbert_correlation_bound s F μ U gap hprob h v hv hb))

end Hindman168
