import Hindman168.HarmonicMass

/-!
# Harmonic dilation and its unnormalized divisor comparison

`etaMass` is `k * 1_{k|n} * mu(n)` and is not declared a probability law.
Changing variables identifies it with the pushforward of the fixed-Z
interval `[X/k,X^2/k)`. The common overlap then cancels exactly.
-/

namespace Hindman168

open scoped BigOperators

noncomputable def etaMass (X W k : ℕ) : FiniteMass.Mass ℕ :=
  Finsupp.onFinset (harmonicWindow X W)
    (fun n => if k ∣ n then (k : ℝ) * harmonicWeight X W n else 0)
    (by intro n hn; by_contra ho; simp [harmonicWeight, ho] at hn)

theorem etaMass_apply (X W k n : ℕ) :
    etaMass X W k n = if k ∣ n then (k : ℝ) * harmonicWeight X W n else 0 := rfl

theorem etaMass_nonneg {X W : ℕ} (hZ : 0 < harmonicNormalizer X W) (k n : ℕ) :
    0 ≤ etaMass X W k n := by
  rw [etaMass_apply]
  split_ifs
  · exact mul_nonneg (Nat.cast_nonneg k) (harmonicWeight_nonneg hZ n)
  · exact le_rfl

/-- The comparison weight is a dilated interval mass with the ORIGINAL Z. -/
theorem etaMass_change_variables {X W k : ℕ} (hk : 0 < k) (hco : W.Coprime k) :
    etaMass X W k =
      (intervalMass ((X : ℝ) / k) (((X ^ 2 : ℕ) : ℝ) / k) W (harmonicNormalizer X W)).mapDomain
        (fun n => k * n) := by
  classical
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hi : Function.Injective (fun n : ℕ => k * n) :=
    fun _ _ h => mul_left_cancel₀ hk.ne' h
  ext n
  by_cases hn : k ∣ n
  · obtain ⟨u, rfl⟩ := hn
    rw [etaMass_apply, if_pos (dvd_mul_right k u),
      Finsupp.mapDomain_apply (f := fun n : ℕ => k * n) hi, ← rawMass_apply,
      rawMass, intervalMass_apply, intervalMass_apply]
    have hm : u ∈ unitInterval ((X : ℝ) / k) (((X ^ 2 : ℕ) : ℝ) / k) W ↔
        k * u ∈ unitInterval X (X ^ 2 : ℕ) W := by
      have hkc : k.Coprime W := hco.symm
      simp only [mem_unitInterval, Nat.coprime_mul_iff_left, Nat.cast_mul]
      rw [div_le_iff₀ hkR, lt_div_iff₀ hkR]
      constructor
      · rintro ⟨h₁, h₂, h₃⟩
        exact ⟨by simpa only [mul_comm] using h₁, by simpa only [mul_comm] using h₂, hkc, h₃⟩
      · rintro ⟨h₁, h₂, _, h₃⟩
        exact ⟨by simpa only [mul_comm] using h₁, by simpa only [mul_comm] using h₂, h₃⟩
    by_cases hu : u ∈ unitInterval ((X : ℝ) / k) (((X ^ 2 : ℕ) : ℝ) / k) W
    · rw [if_pos (hm.mp hu), if_pos hu]
      simp only [Nat.cast_mul, div_eq_mul_inv, mul_inv_rev]
      calc
        (k : ℝ) * ((u : ℝ)⁻¹ * (k : ℝ)⁻¹ * (harmonicNormalizer X W)⁻¹) =
            ((k : ℝ) * (k : ℝ)⁻¹) * ((u : ℝ)⁻¹ * (harmonicNormalizer X W)⁻¹) := by ring
        _ = (u : ℝ)⁻¹ * (harmonicNormalizer X W)⁻¹ := by rw [mul_inv_cancel₀ hkR.ne', one_mul]
    · have hku : k * u ∉ unitInterval X (X ^ 2 : ℕ) W := fun h => hu (hm.mpr h)
      rw [if_neg hku, if_neg hu, mul_zero]
  · rw [etaMass_apply, if_neg hn, Finsupp.mapDomain_notin_range]
    rintro ⟨u, hu⟩
    exact hn ⟨u, hu.symm⟩

/-- Exact boundary-mass identity from the paper, including `k=1`. -/
theorem harmonic_dilation_boundaries {X W k : ℕ} (hX : 2 ≤ X) (hk : 0 < k)
    (hkX : k ≤ X) (hco : W.Coprime k) (hZ : 0 < harmonicNormalizer X W) :
    FiniteMass.distance ((rawMass X W).mapDomain (fun n => k * n)) (etaMass X W k) =
      (roughResidueHarmonic ((X : ℝ) / k) X W 1 0 +
        roughResidueHarmonic (((X ^ 2 : ℕ) : ℝ) / k) (X ^ 2 : ℕ) W 1 0) /
          harmonicNormalizer X W := by
  have hi : Function.Injective (fun n : ℕ => k * n) :=
    fun _ _ h => mul_left_cancel₀ hk.ne' h
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hkXR : (k : ℝ) ≤ X := by exact_mod_cast hkX
  have hXR : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hXX : (0 : ℝ) < ((X ^ 2 : ℕ) : ℝ) := by rw [Nat.cast_pow]; nlinarith
  have hAC : (X : ℝ) / k ≤ X := (div_le_iff₀ hkR).mpr (by nlinarith)
  have hCB : (X : ℝ) ≤ ((X ^ 2 : ℕ) : ℝ) / k := by
    apply (le_div_iff₀ hkR).mpr
    rw [Nat.cast_pow]
    nlinarith
  have hBD : ((X ^ 2 : ℕ) : ℝ) / k ≤ ((X ^ 2 : ℕ) : ℝ) :=
    (div_le_iff₀ hkR).mpr (by nlinarith)
  rw [etaMass_change_variables hk hco, FiniteMass.distance_push_injective hi,
    FiniteMass.distance_comm, rawMass, intervalMass_distance_boundaries hAC hCB hBD W hZ,
    intervalMass_total, intervalMass_total]
  rw [add_div]

/-- Its total mass is k times the probability of the zero residue class. -/
theorem etaMass_total (X W k : ℕ) :
    FiniteMass.total (etaMass X W k) = (k : ℝ) * residueProbability X W k 0 := by
  classical
  rw [FiniteMass.total_eq_sum _ (show (etaMass X W k).support ⊆ harmonicWindow X W from
    Finsupp.support_onFinset_subset)]
  simp only [etaMass_apply, Nat.dvd_iff_mod_eq_zero]
  rw [← Finset.sum_filter]
  exact (Finset.mul_sum _ _ _).symm

theorem etaMass_mass_error {X W k : ℕ} (hX : 2 ≤ X) (hW : 0 < W)
    (hk : 0 < k) (hco : W.Coprime k) (hlog : (W : ℝ) / X < Real.log X) :
    |FiniteMass.total (etaMass X W k) - 1| ≤ residueError X W k := by
  rw [etaMass_total]
  exact harmonic_residue_error hX hW hk hco hk hlog

/-- The endpoint-equality case is included for the dilation k=1. -/
theorem interval_harmonic_upper {A B : ℝ} {W : ℕ} (hA : 0 < A) (hAB : A ≤ B)
    (hW : 0 < W) :
    roughResidueHarmonic A B W 1 0 ≤
      unitDensity W * Real.log (B / A) + (W.totient : ℝ) / A := by
  rcases hAB.eq_or_lt with rfl | hlt
  · simp only [roughResidueHarmonic, roughResidueWindow, Finset.Ico_self,
      Finset.filter_empty, Finset.sum_empty, div_self hA.ne', Real.log_one, mul_zero, zero_add]
    exact div_nonneg (Nat.cast_nonneg _) hA.le
  · have he := periodic_harmonic_error hA hlt hW (by decide : 0 < 1)
      (by simp : W.Coprime 1) (by decide : 0 < 1)
    have hu := (abs_le.mp he).2
    simp only [Nat.cast_one, div_one] at hu
    linarith

noncomputable def dilationError (X W k : ℕ) : ℝ :=
  (2 * Real.log k + ((W : ℝ) * k / X) * (1 + 1 / (X : ℝ))) /
    (Real.log X - (W : ℝ) / X)

/-- Paper's harmonic-dilation bound, in the sum-of-absolute-masses norm. -/
theorem harmonic_dilation_error {X W k : ℕ} (hX : 2 ≤ X) (hW : 0 < W)
    (hk : 0 < k) (hkX : k ≤ X) (hco : W.Coprime k)
    (hlog : (W : ℝ) / X < Real.log X) :
    FiniteMass.distance ((rawMass X W).mapDomain (fun n => k * n)) (etaMass X W k) ≤
      dilationError X W k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hXR : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hXX : (0 : ℝ) < ((X ^ 2 : ℕ) : ℝ) := by rw [Nat.cast_pow]; positivity
  have hWR : (0 : ℝ) < W := by exact_mod_cast hW
  have hφ : (0 : ℝ) < W.totient := by exact_mod_cast (Nat.totient_pos.mpr hW)
  have hD : 0 < Real.log X - (W : ℝ) / X := sub_pos.mpr hlog
  have hZ := harmonicNormalizer_pos hX hW hlog
  have hZlower := harmonicNormalizer_lower hX hW
  have hA₁ := div_pos hXR hkR
  have hA₂ := div_pos hXX hkR
  have hAC : (X : ℝ) / k ≤ X := (div_le_iff₀ hkR).mpr (by nlinarith)
  have hBD : ((X ^ 2 : ℕ) : ℝ) / k ≤ ((X ^ 2 : ℕ) : ℝ) :=
    (div_le_iff₀ hkR).mpr (by nlinarith)
  have hr₁ : (X : ℝ) / ((X : ℝ) / k) = k := by field_simp
  have hr₂ : ((X ^ 2 : ℕ) : ℝ) / (((X ^ 2 : ℕ) : ℝ) / k) = k := by field_simp
  have hu₁ := interval_harmonic_upper hA₁ hAC hW
  have hu₂ := interval_harmonic_upper hA₂ hBD hW
  rw [hr₁] at hu₁
  rw [hr₂] at hu₂
  let N := 2 * unitDensity W * Real.log k + (W.totient : ℝ) / ((X : ℝ) / k) +
    (W.totient : ℝ) / (((X ^ 2 : ℕ) : ℝ) / k)
  have hnum : roughResidueHarmonic ((X : ℝ) / k) X W 1 0 +
      roughResidueHarmonic (((X ^ 2 : ℕ) : ℝ) / k) (X ^ 2 : ℕ) W 1 0 ≤ N := by
    dsimp [N]
    linarith
  have hN : 0 ≤ N := by
    dsimp [N]
    exact add_nonneg (add_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (unitDensity_pos hW).le) (Real.log_nonneg hk1))
      (div_nonneg hφ.le hA₁.le)) (div_nonneg hφ.le hA₂.le)
  rw [harmonic_dilation_boundaries hX hk hkX hco hZ]
  calc
    _ ≤ N / harmonicNormalizer X W := div_le_div_of_nonneg_right hnum hZ.le
    _ ≤ N / (unitDensity W * (Real.log X - (W : ℝ) / X)) :=
      div_le_div_of_nonneg_left hN (mul_pos (unitDensity_pos hW) hD) hZlower
    _ = dilationError X W k := by
      dsimp [N]
      unfold unitDensity dilationError
      rw [Nat.cast_pow]
      field_simp
      ring

noncomputable def integerEtaMass (X W k : ℕ) : FiniteMass.Mass ℤ :=
  (etaMass X W k).mapDomain (fun n : ℕ => (n : ℤ))

theorem integerMass_apply_of_neg (X W : ℕ) {z : ℤ} (hz : z < 0) :
    integerMass X W z = 0 := by
  unfold integerMass
  apply Finsupp.mapDomain_notin_range
  rintro ⟨n, rfl⟩
  exact (not_lt_of_ge (Int.natCast_nonneg n)) hz

theorem integerEtaMass_apply_of_neg (X W k : ℕ) {z : ℤ} (hz : z < 0) :
    integerEtaMass X W k z = 0 := by
  unfold integerEtaMass
  apply Finsupp.mapDomain_notin_range
  rintro ⟨n, rfl⟩
  exact (not_lt_of_ge (Int.natCast_nonneg n)) hz

/-- This is precisely the paper's unnormalized comparison on all integers. -/
theorem integerEtaMass_apply (X W k : ℕ) (z : ℤ) :
    integerEtaMass X W k z = if (k : ℤ) ∣ z then (k : ℝ) * integerMass X W z else 0 := by
  by_cases hz : 0 ≤ z
  · have he : z = (z.toNat : ℤ) := Int.eq_natCast_toNat.mpr hz
    rw [he, integerEtaMass,
      Finsupp.mapDomain_apply (f := fun n : ℕ => (n : ℤ)) Int.ofNat_injective,
      etaMass_apply, integerMass_apply_nat]
    simp only [Int.natCast_dvd_natCast]
  · rw [integerEtaMass_apply_of_neg X W k (lt_of_not_ge hz),
      integerMass_apply_of_neg X W (lt_of_not_ge hz)]
    simp only [mul_zero, ite_self]

theorem integer_dilation_commutes (X W k : ℕ) :
    (integerMass X W).mapDomain (fun z => (k : ℤ) * z) =
      ((rawMass X W).mapDomain (fun n => k * n)).mapDomain (fun n : ℕ => (n : ℤ)) := by
  unfold integerMass
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  have hf : (fun z : ℤ => (k : ℤ) * z) ∘ (fun n : ℕ => (n : ℤ)) =
      (fun n : ℕ => (n : ℤ)) ∘ (fun n : ℕ => k * n) := by
    funext n
    simp only [Function.comp_apply, Nat.cast_mul]
  rw [hf]

theorem integer_dilation_distance (X W k : ℕ) :
    FiniteMass.distance ((integerMass X W).mapDomain (fun z => (k : ℤ) * z))
      (integerEtaMass X W k) =
      FiniteMass.distance ((rawMass X W).mapDomain (fun n => k * n)) (etaMass X W k) := by
  rw [integer_dilation_commutes, integerEtaMass,
    FiniteMass.distance_push_injective (f := fun n : ℕ => (n : ℤ)) Int.ofNat_injective]

theorem integer_harmonic_dilation_error {X W k : ℕ} (hX : 2 ≤ X) (hW : 0 < W)
    (hk : 0 < k) (hkX : k ≤ X) (hco : W.Coprime k)
    (hlog : (W : ℝ) / X < Real.log X) :
    FiniteMass.distance ((integerMass X W).mapDomain (fun z => (k : ℤ) * z))
      (integerEtaMass X W k) ≤ dilationError X W k := by
  rw [integer_dilation_distance]
  exact harmonic_dilation_error hX hW hk hkX hco hlog

theorem integerEtaMass_mass_error {X W k : ℕ} (hX : 2 ≤ X) (hW : 0 < W)
    (hk : 0 < k) (hco : W.Coprime k) (hlog : (W : ℝ) / X < Real.log X) :
    |FiniteMass.total (integerEtaMass X W k) - 1| ≤ residueError X W k := by
  rw [integerEtaMass, FiniteMass.total_push]
  exact etaMass_mass_error hX hW hk hco hlog

theorem integerMass_nonneg {X W : ℕ} (hZ : 0 < harmonicNormalizer X W) (z : ℤ) :
    0 ≤ integerMass X W z := by
  by_cases hz : 0 ≤ z
  · rw [Int.eq_natCast_toNat.mpr hz, integerMass_apply_nat]
    exact harmonicWeight_nonneg hZ _
  · rw [integerMass_apply_of_neg X W (lt_of_not_ge hz)]

/-- The raw sample law extended to integers by the natural inclusion. -/
noncomputable def integerHarmonicPMF (X W : ℕ) (hZ : 0 < harmonicNormalizer X W) : PMF ℤ :=
  (harmonicPMF X W hZ).map (fun n : ℕ => (n : ℤ))

theorem integerHarmonicPMF_apply {X W : ℕ} (hZ : 0 < harmonicNormalizer X W) (z : ℤ) :
    integerHarmonicPMF X W hZ z = ENNReal.ofReal (integerMass X W z) := by
  classical
  by_cases hz : 0 ≤ z
  · rw [Int.eq_natCast_toNat.mpr hz, integerMass_apply_nat,
      integerHarmonicPMF, PMF.map_apply]
    simp only [Int.natCast_inj, harmonicPMF_apply]
    rw [tsum_eq_single z.toNat (fun n hn => if_neg (Ne.symm hn)), if_pos rfl]
  · rw [integerMass_apply_of_neg X W (lt_of_not_ge hz), ENNReal.ofReal_zero,
      integerHarmonicPMF, PMF.map_apply]
    have hn : ∀ n : ℕ, z ≠ (n : ℤ) := by
      intro n he
      exact hz (he.symm ▸ Int.natCast_nonneg n)
    simp only [if_neg (hn _), tsum_zero]

end Hindman168
