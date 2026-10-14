import Hindman168.NativeLieGlobalLogarithm
import Hindman168.LieExponentialContinuity

/-! Genuine natural powers and unique positive-degree roots in the
original nilpotent group, with their actual logarithms. These identities
do not assert that the roots of a specified subgroup form a subgroup. -/

namespace Hindman168
open Function
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

include I

omit [Group.IsNilpotent G] [FiniteDimensional ℝ E] [ConnectedSpace G]
  [SimplyConnectedSpace G] in
 theorem nativeLieExponential_nat_smul (v : E) (n : ℕ) :
    nativeLieExponential (I := I) (G := G) ((n : ℝ) • v) =
      (nativeLieExponential (I := I) (G := G) v) ^ n := by
  have ht := lieOneParameterCurve_nat_mul (I := I) (G := G) v n 1
  rw [mul_one] at ht
  exact (nativeLieExponential_smul (v : GroupLieAlgebra I G) (n : ℝ)).trans ht

 theorem nativeLieGlobalLogarithm_pow (g : G) (n : ℕ) :
    nativeLieGlobalLogarithm (E := E) (I := I) (G := G) (g ^ n) =
      (n : ℝ) • nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g := by
  rw [← nativeLieExponential_globalLogarithm (E := E) (I := I) g,
    ← nativeLieExponential_nat_smul, nativeLieGlobalLogarithm_exponential,
    nativeLieGlobalLogarithm_exponential]

 theorem nativeLie_pow_root (g : G) {n : ℕ} (hn : 0 < n) :
    (nativeLieExponential (I := I) (G := G)
      ((n : ℝ)⁻¹ • nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g)) ^ n = g := by
  rw [← nativeLieExponential_nat_smul, smul_smul,
    mul_inv_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hn)), one_smul,
    nativeLieExponential_globalLogarithm]

 theorem nativeLie_pow_injective {n : ℕ} (hn : 0 < n) :
    Injective (fun g : G => g ^ n) := by
  intro g h he
  have hl := congrArg (nativeLieGlobalLogarithm (E := E) (I := I) (G := G)) he
  rw [nativeLieGlobalLogarithm_pow, nativeLieGlobalLogarithm_pow] at hl
  have he' := (smul_right_injective (M := E)
    (show (n : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hn))) hl
  have he'' := congrArg (fun v : E => nativeLieExponential (I := I) (G := G) v) he'
  simpa only [nativeLieExponential_globalLogarithm] using he''

 theorem nativeLie_pow_bijective {n : ℕ} (hn : 0 < n) :
    Bijective (fun g : G => g ^ n) :=
  ⟨nativeLie_pow_injective (E := E) (I := I) hn,
    fun g => ⟨_, nativeLie_pow_root (E := E) (I := I) g hn⟩⟩

end Hindman168
