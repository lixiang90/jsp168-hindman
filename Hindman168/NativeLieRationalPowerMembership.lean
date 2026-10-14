import Hindman168.NativeLiePowerRoots
import Mathlib.Data.Rat.Cast.CharZero

/-! Actual integer exponential powers and rational denominator clearing
in the original group. A genuine positive-root-closed subgroup is
therefore closed under exponentials of rational multiples of its own
actual logarithms. -/

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]

attribute [local instance] lieGroup_smooth_min_three

omit [Module ℚ E] in
 theorem nativeLieExponential_int_smul (v : E) (z : ℤ) :
    nativeLieExponential (I := I) (G := G) ((z : ℝ) • v) =
      nativeLieExponential (I := I) (G := G) v ^ z := by
  cases z with
  | ofNat n =>
    simpa only [Int.ofNat_eq_natCast, Int.cast_natCast, zpow_natCast] using
      nativeLieExponential_nat_smul (I := I) (G := G) v n
  | negSucc n =>
    rw [Int.cast_negSucc, neg_smul]
    have he : nativeLieExponential (I := I) (G := G) (-((n + 1 : ℕ) : ℝ) • v) =
        (nativeLieExponential (I := I) (G := G) (((n + 1 : ℕ) : ℝ) • v))⁻¹ := by
      rw [neg_smul]
      exact nativeLieExponential_neg (I := I) (G := G) (((n + 1 : ℕ) : ℝ) • v)
    rw [← neg_smul, he, nativeLieExponential_nat_smul, zpow_negSucc]

 theorem nativeLieExponential_rat_power_den (v : E) (q : ℚ) :
    nativeLieExponential (I := I) (G := G) (q • v) ^ q.den =
      nativeLieExponential (I := I) (G := G) v ^ q.num := by
  rw [← nativeLieExponential_nat_smul, ← Rat.cast_smul_eq_qsmul ℝ, smul_smul]
  have hq : (q.den : ℚ) * q = (q.num : ℚ) := by
    calc
      _ = (q.den : ℚ) * ((q.num : ℚ) / (q.den : ℚ)) :=
        congrArg (fun r : ℚ => (q.den : ℚ) * r) q.num_div_den.symm
      _ = _ := by
        have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
        field_simp
  have hr : (q.den : ℝ) * (q : ℝ) = (q.num : ℝ) := by exact_mod_cast hq
  rw [hr, nativeLieExponential_int_smul]

 theorem nativeLieExponential_rat_smul_mem_root_closed
    (K : Subgroup G)
    (hroot : ∀ (g : G) (n : ℕ), 0 < n → g ^ n ∈ K → g ∈ K)
    {v : E} (hv : nativeLieExponential (I := I) (G := G) v ∈ K) (q : ℚ) :
    nativeLieExponential (I := I) (G := G) (q • v) ∈ K := by
  apply hroot _ q.den q.den_pos
  rw [nativeLieExponential_rat_power_den]
  exact K.zpow_mem hv q.num

end Hindman168
