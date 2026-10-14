import Hindman168.TailProducts

/-!
# Integer transport of the actual product comparison

The natural inclusion is injective, so it preserves the complete L1 error.
The divisor comparison is identified on ALL integers, including negative
arguments, where the raw harmonic measure and comparison both vanish.
-/

namespace Hindman168

open scoped BigOperators

noncomputable def integerProductMass (ρ : FiniteMass.Mass ℕ) (X W : ℕ) : FiniteMass.Mass ℤ :=
  (productMass ρ X W).mapDomain (fun n : ℕ => (n : ℤ))

noncomputable def integerProductComparisonMass (ρ : FiniteMass.Mass ℕ) (X W : ℕ) : FiniteMass.Mass ℤ :=
  (productComparisonMass ρ X W).mapDomain (fun n : ℕ => (n : ℤ))

noncomputable def integerDivisorMask (ρ : FiniteMass.Mass ℕ) (z : ℤ) : ℝ :=
  ∑ k ∈ ρ.support, ρ k * (if (k : ℤ) ∣ z then (k : ℝ) else 0)

theorem integerProductComparisonMass_apply (ρ : FiniteMass.Mass ℕ) (X W : ℕ) (z : ℤ) :
    integerProductComparisonMass ρ X W z = integerMass X W z * integerDivisorMask ρ z := by
  classical
  by_cases hz : 0 ≤ z
  · rw [Int.eq_natCast_toNat.mpr hz, integerProductComparisonMass,
      Finsupp.mapDomain_apply (f := fun n : ℕ => (n : ℤ)) Int.ofNat_injective,
      productComparisonMass_apply, integerMass_apply_nat]
    simp only [integerDivisorMask, divisorMask, Int.natCast_dvd_natCast]
  · rw [integerMass_apply_of_neg X W (lt_of_not_ge hz), zero_mul]
    unfold integerProductComparisonMass
    apply Finsupp.mapDomain_notin_range
    rintro ⟨n, rfl⟩
    exact hz (Int.natCast_nonneg n)

theorem integerProductPMF_apply {ρ : FiniteMass.Mass ℕ} {X W : ℕ}
    (hρ : ∀ k, 0 ≤ ρ k) (htρ : FiniteMass.total ρ = 1)
    (hZ : 0 < harmonicNormalizer X W) (z : ℤ) :
    ((productPMF ρ hρ htρ X W hZ).map (fun n : ℕ => (n : ℤ))) z =
      ENNReal.ofReal (integerProductMass ρ X W z) := by
  rw [productPMF_eq_toPMF, FiniteMass.toPMF_map_apply]
  rfl

theorem integer_product_law_error {ρ : FiniteMass.Mass ℕ} {X W K : ℕ}
    (hρ : ∀ k, 0 ≤ ρ k) (htρ : FiniteMass.total ρ = 1) (hX : 2 ≤ X) (hW : 0 < W)
    (hKX : K ≤ X) (hs : ∀ k ∈ ρ.support, 0 < k ∧ k ≤ K ∧ W.Coprime k)
    (hlog : (W : ℝ) / X < Real.log X) :
    FiniteMass.distance (integerProductMass ρ X W) (integerProductComparisonMass ρ X W) ≤
      dilationError X W K := by
  rw [integerProductMass, integerProductComparisonMass,
    FiniteMass.distance_push_injective (f := fun n : ℕ => (n : ℤ)) Int.ofNat_injective]
  exact product_law_error hρ htρ hX hW hKX hs hlog

theorem integer_product_comparison_mass_error {ρ : FiniteMass.Mass ℕ} {X W K : ℕ}
    (hρ : ∀ k, 0 ≤ ρ k) (htρ : FiniteMass.total ρ = 1) (hX : 2 ≤ X) (hW : 0 < W)
    (hs : ∀ k ∈ ρ.support, 0 < k ∧ k ≤ K ∧ W.Coprime k)
    (hlog : (W : ℝ) / X < Real.log X) :
    |FiniteMass.total (integerProductComparisonMass ρ X W) - 1| ≤ residueError X W K := by
  rw [integerProductComparisonMass, FiniteMass.total_push]
  exact product_comparison_mass_error hρ htρ hX hW hs hlog

end Hindman168
