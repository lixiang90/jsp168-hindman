import Hindman168.NativeNilmanifoldData
import Hindman168.NativeLatticeRationalCoordinates

/-! Actual integer values on ORIGINAL lattice imply rational values on
the ACTUAL rational log span, via PROVED positive powers and exact Log laws.
No additive-lattice property of the set Log(Gamma) is assumed. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_integral_functional_value {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (f : D.E →ₗ[ℝ] ℝ)
    (hInt : ∀ g ∈ D.Γ, ∃ z : ℤ, f (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g) = (z : ℝ))
    (v : D.E) (hv : v ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ) :
    ∃ q : ℚ, f v = (q : ℝ) := by
  obtain ⟨n,hn,hpow⟩ := (nativeSubgroupRationalLogSpan_mem_iff_positive_power (I := D.I) D.Γ v).mp hv
  obtain ⟨z,hz⟩ := hInt _ hpow
  rw [← nativeLieExponential_nat_smul (E := D.E) (I := D.I) (G := D.G) v n,
    nativeLieGlobalLogarithm_exponential,map_smul] at hz
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  refine ⟨(z : ℚ)/(n : ℚ),?_⟩
  rw [Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast]
  apply (eq_div_iff hn0).mpr
  exact (mul_comm _ _).trans hz

end Hindman168
