import Hindman168.VectorPolynomialNatUniqueness
import Mathlib.Analysis.Normed.Algebra.Exponential

/-! The actual Banach-algebra exponential is injective on nilpotent
elements. Equal exponentials have equal natural-number powers; the real
finite exponential curves therefore have equal coefficients. No logarithm,
commutation of the two elements or matrix representation is assumed. -/

namespace Hindman168
open Finset

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

omit [CompleteSpace A] in
 theorem nilpotent_real_exp_smul_eq_sum {a : A} {k : ℕ} (hk : a ^ k = 0) (t : ℝ) :
    NormedSpace.exp (t • a) =
      ∑ j ∈ range k, (t ^ j) • ((j.factorial : ℝ)⁻¹ • a ^ j) := by
  rw [NormedSpace.exp_eq_tsum ℝ]
  change (∑' j : ℕ, (j.factorial : ℝ)⁻¹ • (t • a) ^ j) =
    ∑ j ∈ range k, (t ^ j) • ((j.factorial : ℝ)⁻¹ • a ^ j)
  have hf : (∑' j : ℕ, (j.factorial : ℝ)⁻¹ • (t • a) ^ j) =
      ∑ j ∈ range k, (j.factorial : ℝ)⁻¹ • (t • a) ^ j := by
    apply tsum_eq_sum
    intro j hj
    have hkj : k ≤ j := by simpa only [Finset.mem_range, not_lt] using hj
    rw [smul_pow, pow_eq_zero_of_le hkj hk, smul_zero, smul_zero]
  rw [hf]
  apply sum_congr rfl
  intro j _
  rw [smul_pow, smul_comm]

 theorem nilpotent_banach_exp_injective {a b : A} (ha : IsNilpotent a)
    (hb : IsNilpotent b) (he : NormedSpace.exp a = NormedSpace.exp b) : a = b := by
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  obtain ⟨ka, hka⟩ := ha
  obtain ⟨kb, hkb⟩ := hb
  let k : ℕ := max ka kb + 2
  have hA : a ^ k = 0 := pow_eq_zero_of_le (by dsimp [k]; omega) hka
  have hB : b ^ k = 0 := pow_eq_zero_of_le (by dsimp [k]; omega) hkb
  have hvals : ∀ n : ℕ,
      (∑ j ∈ range k, ((n : ℝ) ^ j) • ((j.factorial : ℝ)⁻¹ • a ^ j)) =
        ∑ j ∈ range k, ((n : ℝ) ^ j) • ((j.factorial : ℝ)⁻¹ • b ^ j) := by
    intro n
    rw [← nilpotent_real_exp_smul_eq_sum hA, ← nilpotent_real_exp_smul_eq_sum hB,
      Nat.cast_smul_eq_nsmul ℝ, Nat.cast_smul_eq_nsmul ℝ,
      NormedSpace.exp_nsmul, NormedSpace.exp_nsmul, he]
  have hc := vectorPolynomial_coeff_eq_of_nat_values hvals (j := 1) (by dsimp [k]; omega)
  simpa only [Nat.factorial_one, Nat.cast_one, inv_one, pow_one, one_smul] using hc

end Hindman168
