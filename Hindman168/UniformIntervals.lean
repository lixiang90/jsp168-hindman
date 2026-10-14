import Hindman168.UniformFiniteMass
import Hindman168.IntervalResidueCount

/-!
# Actual uniform laws on arbitrary integer intervals

The location A is any integer, while T is the number of points in [A,A+T).
The genuine PMF and its residue pushforward are identified with the finite
real masses. The residue L1 bound is uniform in A and in the residue class.
-/

namespace Hindman168

open scoped BigOperators Classical

noncomputable def uniformIntervalMass (A : ℤ) (T : ℕ) : FiniteMass.Mass ℤ :=
  FiniteMass.uniformFinsetMass (integerWindow A T)

theorem uniformIntervalMass_apply (A : ℤ) (T : ℕ) (z : ℤ) :
    uniformIntervalMass A T z = if z ∈ integerWindow A T then (T : ℝ)⁻¹ else 0 := by
  rw [uniformIntervalMass, FiniteMass.uniformFinsetMass, FiniteMass.flatMass_apply,
    integerWindow_card]
  by_cases hz : z ∈ integerWindow A T
  · simp only [if_pos hz]
  · simp only [if_neg hz]

theorem uniformIntervalMass_nonneg (A : ℤ) (T : ℕ) (z : ℤ) :
    0 ≤ uniformIntervalMass A T z := FiniteMass.uniformFinsetMass_nonneg _ _

theorem uniformIntervalMass_total (A : ℤ) {T : ℕ} (hT : 0 < T) :
    FiniteMass.total (uniformIntervalMass A T) = 1 :=
  FiniteMass.uniformFinsetMass_total _ (by rw [integerWindow_card]; exact hT)

noncomputable def uniformIntervalPMF (A : ℤ) (T : ℕ) (hT : 0 < T) : PMF ℤ :=
  FiniteMass.toPMF (uniformIntervalMass A T) (uniformIntervalMass_nonneg A T)
    (uniformIntervalMass_total A hT)

theorem uniformIntervalPMF_apply (A : ℤ) (T : ℕ) (hT : 0 < T) (z : ℤ) :
    uniformIntervalPMF A T hT z =
      ENNReal.ofReal (if z ∈ integerWindow A T then (T : ℝ)⁻¹ else 0) := by
  rw [uniformIntervalPMF, FiniteMass.toPMF_apply, uniformIntervalMass_apply]

def integerResidue (k : ℕ) (hk : 0 < k) (z : ℤ) : Fin k := by
  refine ⟨(z % (k : ℤ)).toNat, ?_⟩
  have hkZ : (0 : ℤ) < k := by exact_mod_cast hk
  have he : z % (k : ℤ) = ((z % (k : ℤ)).toNat : ℤ) :=
    Int.eq_natCast_toNat.mpr (Int.emod_nonneg z hkZ.ne')
  have hl := Int.emod_lt_of_pos z hkZ
  rw [he] at hl
  exact_mod_cast hl

theorem integerResidue_eq_iff (k : ℕ) (hk : 0 < k) (z : ℤ) (a : Fin k) :
    integerResidue k hk z = a ↔ z % (k : ℤ) = (a.val : ℤ) := by
  have hkZ : (0 : ℤ) < k := by exact_mod_cast hk
  have he : z % (k : ℤ) = ((z % (k : ℤ)).toNat : ℤ) :=
    Int.eq_natCast_toNat.mpr (Int.emod_nonneg z hkZ.ne')
  constructor
  · intro h
    exact he.trans (congrArg (fun b : Fin k => (b.val : ℤ)) h)
  · intro h
    apply Fin.ext
    change (z % (k : ℤ)).toNat = a.val
    simp only [h, Int.toNat_natCast]

noncomputable def intervalResidueMass (A : ℤ) (T k : ℕ) (hk : 0 < k) :
    FiniteMass.Mass (Fin k) := (uniformIntervalMass A T).mapDomain (integerResidue k hk)

noncomputable def uniformResidueMass (k : ℕ) : FiniteMass.Mass (Fin k) :=
  FiniteMass.uniformFinsetMass Finset.univ

theorem uniformResidueMass_apply (k : ℕ) (a : Fin k) :
    uniformResidueMass k a = (k : ℝ)⁻¹ := by
  simp [uniformResidueMass, FiniteMass.uniformFinsetMass, FiniteMass.flatMass_apply]

theorem intervalResidueMass_apply (A : ℤ) (T k : ℕ) (hk : 0 < k) (a : Fin k) :
    intervalResidueMass A T k hk a = ((intervalResidueSet A T k a.val).card : ℝ) / T := by
  unfold intervalResidueMass uniformIntervalMass FiniteMass.uniformFinsetMass
  rw [integerWindow_card, FiniteMass.flatMass_push_coeff]
  simp only [intervalResidueSet, integerResidue_eq_iff, div_eq_mul_inv]

theorem uniformIntervalPMF_residue_apply (A : ℤ) {T k : ℕ} (hT : 0 < T) (hk : 0 < k)
    (a : Fin k) :
    ((uniformIntervalPMF A T hT).map (integerResidue k hk)) a =
      ENNReal.ofReal (((intervalResidueSet A T k a.val).card : ℝ) / T) := by
  rw [uniformIntervalPMF, FiniteMass.toPMF_map_apply]
  exact congrArg ENNReal.ofReal (intervalResidueMass_apply A T k hk a)

theorem uniform_interval_residue_class (A : ℤ) {T k : ℕ} (hT : 0 < T) (hk : 0 < k)
    (a : Fin k) : |intervalResidueMass A T k hk a - (k : ℝ)⁻¹| ≤ 1 / T := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hc := interval_residue_count A T hk a.isLt
  rw [intervalResidueMass_apply]
  have he : ((intervalResidueSet A T k a.val).card : ℝ) / T - (k : ℝ)⁻¹ =
      (((intervalResidueSet A T k a.val).card : ℝ) - (T : ℝ) / k) / T := by field_simp
  rw [he, abs_div, abs_of_pos hTr]
  exact div_le_div_of_nonneg_right hc hTr.le

/-- A bound sharper than the paper's 2k/T; it follows from the same counts. -/
theorem uniform_interval_residue_distance (A : ℤ) {T k : ℕ} (hT : 0 < T) (hk : 0 < k) :
    FiniteMass.distance (intervalResidueMass A T k hk) (uniformResidueMass k) ≤ (k : ℝ) / T := by
  rw [FiniteMass.distance, FiniteMass.variation_eq_sum _ (Finset.subset_univ _)]
  simp only [Finsupp.sub_apply, uniformResidueMass_apply]
  calc
    _ ≤ ∑ _a : Fin k, (1 : ℝ) / T :=
      Finset.sum_le_sum (fun a _ => uniform_interval_residue_class A hT hk a)
    _ = (k : ℝ) / T := by simp [div_eq_mul_inv]

theorem uniform_interval_residue_paper_bound (A : ℤ) {T k : ℕ} (hT : 0 < T) (hk : 0 < k) :
    FiniteMass.distance (intervalResidueMass A T k hk) (uniformResidueMass k) ≤ 2 * (k : ℝ) / T :=
  (uniform_interval_residue_distance A hT hk).trans (by
    have hTr : (0 : ℝ) < T := by exact_mod_cast hT
    have hn : (0 : ℝ) ≤ (k : ℝ) / T := div_nonneg (Nat.cast_nonneg _) hTr.le
    rw [mul_div_assoc]
    linarith)

end Hindman168
