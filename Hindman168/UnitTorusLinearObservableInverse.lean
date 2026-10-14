import Hindman168.UnitTorusCompactObservableSelection
import Hindman168.UnitCircleGeometricMean
import Hindman168.TorusPolynomialCharacterProjection
import Hindman168.CompactUnitLipschitzObservables

/-! Actual original RANGE-N linear torus inverse for ALL unit observations,
with one fixed natural budget before all unbounded real frequencies and N. -/
namespace Hindman168
open MeasureTheory
open scoped BigOperators Classical

theorem unit_torus_linear_fourier_phase {ι : Type*} [Fintype ι]
    (k : ι → ℤ) (γ : ι → ℝ) (n : ℕ) :
    UnitAddTorus.mFourier k (fun i => (((n : ℝ)*γ i : ℝ) : UnitAddCircle)) =
      (AddCircle.toCircle (((n : ℝ)*(∑ i, (k i : ℝ)*γ i) : ℝ) : UnitAddCircle) : ℂ) := by
  rw [Finset.mul_sum,circle_phase_real_sum]
  change (∏ i, fourier (k i) (((n : ℝ)*γ i : ℝ) : UnitAddCircle)) = _
  simp_rw [fourier_apply,← AddCircle.coe_zsmul,zsmul_eq_mul]
  apply Finset.prod_congr rfl
  intro i _
  congr 3
  ring

theorem unit_torus_linear_observable_inverse (ι : Type*) [Fintype ι]
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ A : ℕ, 0 < A ∧ ∀ (γ : ι → ℝ) (N : ℕ), 0 < N →
      ∀ F ∈ unitLipschitzObservables (UnitAddTorus ι),
        δ ≤ ‖unitTorusFiniteDiscrepancy (Finset.range N)
          (fun n i => (((n : ℝ)*γ i : ℝ) : UnitAddCircle)) F‖ →
          ∃ k : ι → ℤ, k ≠ 0 ∧ (∑ i, (k i).natAbs) ≤ A ∧
            (N : ℝ)*‖((∑ i, (k i : ℝ)*γ i : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ) := by
  obtain ⟨η,hη,_,K,hK,hselect⟩ := unit_torus_compact_observable_phase_selection ι
    (unitLipschitzObservables (UnitAddTorus ι)) (unit_lipschitz_observables_compact _) δ hδ
  let A := K+⌈1/(2*η)⌉₊+1
  have hA : 0 < A := by dsimp only [A]; omega
  have hKA : K ≤ A := by dsimp only [A]; omega
  have hBA : 1/(2*η) ≤ (A : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (show ⌈1/(2*η)⌉₊ ≤ A by dsimp only [A]; omega))
  refine ⟨A,hA,?_⟩
  intro γ N hN F hF hbad
  obtain ⟨k,hk,hsize,hmean⟩ := hselect (Finset.range N)
    (Finset.nonempty_range_iff.mpr hN.ne')
    (fun n i => (((n : ℝ)*γ i : ℝ) : UnitAddCircle)) F hF hbad
  simp_rw [unit_torus_linear_fourier_phase] at hmean
  have hbound := unit_circle_large_linear_mean_inverse (∑ i, (k i : ℝ)*γ i) N hN η hη hmean
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have he : (N : ℝ)*(1/(2*η*(N : ℝ)))=1/(2*η) := by field_simp
  exact ⟨k,hk,hsize.trans hKA,(mul_le_mul_of_nonneg_left hbound hn.le).trans (he.le.trans hBA)⟩

end Hindman168
