import Hindman168.SmoothModulus
import Hindman168.MasterSmallPrimeProbability
import Hindman168.MasterPrimeProbability

/-!
# One actual master-parameter family with all arithmetic conditions

The small-prime exponent is selected first. The smooth modulus is then
fixed, before the recursive prime pools, polynomial gaps and dyadic raw
cutoffs. The existence theorem packages the actual constructions and
their probability / growth conclusions with the rational coefficients.
No desired equidistribution or exception estimate is assumed as input.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical

structure MasterParameterFamily where
  exponent : ℕ → ℕ
  modulus : ℕ → ℕ+
  pool : ℕ → ℕ → DyadicPrimePool
  gap : ℕ → ℕ → ℕ
  cutoff : ℕ → ℕ → ℕ

def MasterParameterFamily.auxiliary (F : MasterParameterFamily) (w l : ℕ) : ℕ :=
  2 + (F.modulus w : ℕ) + ∏ j ∈ Finset.range l, F.cutoff w j ^ 2

def MasterParameterFamily.residueModulus (F : MasterParameterFamily) (w l : ℕ) : ℕ :=
  masterStageModulus w (F.exponent w) (F.auxiliary w l)

noncomputable def constructedMasterFamily {n : ℕ} (N : ℕ)
    (D : Finset (MvPolynomial (Fin n) ℤ)) (hD : ∀ f ∈ D, f ≠ 0) : MasterParameterFamily :=
  let e := masterSmallPrimeExponent D hD
  let M : ℕ → ℕ+ := fun w => ⟨smoothMasterModulus w N (e w), smoothMasterModulus_pos _ _ _⟩
  let H := fun w l => masterPrimeHistory w (e w) (M w) D l
  { exponent := e
    modulus := M
    pool := fun w l => masterStagePool w (e w) (M w) (H w l)
    gap := fun w l => masterStageGap w (e w) (M w) D (H w l)
    cutoff := fun w l => masterStageCutoff w (e w) (M w) D (H w l) }

theorem constructedMasterFamily_auxiliary {n : ℕ} (N : ℕ)
    (D : Finset (MvPolynomial (Fin n) ℤ)) (hD : ∀ f ∈ D, f ≠ 0) (w l : ℕ) :
    (constructedMasterFamily N D hD).auxiliary w l =
      masterStageAuxiliary ((constructedMasterFamily N D hD).modulus w)
        (masterPrimeHistory w ((constructedMasterFamily N D hD).exponent w)
          ((constructedMasterFamily N D hD).modulus w) D l) :=
  (masterPrimeHistory_auxiliary_eq _ _ _ D l).symm

theorem constructedMasterFamily_coefficients {n : ℕ} (N : ℕ) (A : Finset ℚ)
    (hA : ∀ a ∈ A, 0 < a) (D : Finset (MvPolynomial (Fin n) ℤ))
    (hD : ∀ f ∈ D, f ≠ 0) :
    ∀ᶠ w in atTop, ∀ a ∈ A, ∀ S : Finset ℕ, S ⊆ Finset.range N → S.Nonempty →
      ∃ c : ℕ, 0 < c ∧ (masterScale (primorial w) w N S : ℚ) * a = (c : ℚ) ∧
        (primorial w) ^ ((constructedMasterFamily N D hD).exponent w + 1) * c ∣
          ((constructedMasterFamily N D hD).modulus w : ℕ) := by
  filter_upwards [rational_family_smoothMasterModulus_absorbs A N hA] with w hw
  intro a ha S hS hSn
  exact hw a ha S hS hSn _

theorem rational_family_chain_ratios (N : ℕ) (A : Finset ℚ) (hA : ∀ a ∈ A, 0 < a) :
    ∀ᶠ w in atTop, ∀ a ∈ A, ∀ b ∈ A, ∀ m : ℕ, ∀ C : Chain m,
      (∀ i, C.block i ⊆ Finset.range N) → ∀ i j : Fin m, i < j →
      ∃ c : ℕ,
        ((masterScale (primorial w) w N (C.block i) : ℚ) * a) /
          ((masterScale (primorial w) w N (C.block j) : ℚ) * b) = (primorial w : ℚ) * c := by
  apply (eventually_all_finset A).mpr
  intro a ha
  apply (eventually_all_finset A).mpr
  intro b hb
  filter_upwards [eventually_ge_atTop ((a / b).den + 1)] with w hw
  intro m C hC i j hij
  exact rational_chain_scale_ratio_integral C hC i j hij a b (hA a ha).le (hA b hb) hw

structure MasterParameterConditions {n : ℕ} (N : ℕ) (A : Finset ℚ)
    (D : Finset (MvPolynomial (Fin n) ℤ)) (F : MasterParameterFamily) : Prop where
  exponent_positive : ∀ w, 1 ≤ F.exponent w
  smooth_modulus : ∀ w, ∃ e : ℕ, (F.modulus w : ℕ) = (primorial w) ^ e
  primorial_power_dvd : ∀ w, (primorial w) ^ w ∣ (F.modulus w : ℕ)
  subset_scale_dvd : ∀ w S, S ⊆ Finset.range N →
    masterScale (primorial w) w N S ∣ (F.modulus w : ℕ)
  subset_scale_le : ∀ w S, S ⊆ Finset.range N →
    masterScale (primorial w) w N S ≤ (F.modulus w : ℕ)
  adding_scales : ∀ w P T j i, Chain.AddsTo P j T i → T.Nonempty →
    insert j P ⊆ Finset.range N → insert i T ⊆ Finset.range N →
    masterScale (primorial w) w N (insert i T) * (primorial w) ^ w ∣
      masterScale (primorial w) w N (insert j P)
  coefficients : ∀ᶠ w in atTop, ∀ a ∈ A, ∀ S : Finset ℕ,
    S ⊆ Finset.range N → S.Nonempty → ∃ c : ℕ, 0 < c ∧
      (masterScale (primorial w) w N S : ℚ) * a = (c : ℚ) ∧
      (primorial w) ^ (F.exponent w + 1) * c ∣ (F.modulus w : ℕ)
  chain_ratios : ∀ᶠ w in atTop, ∀ a ∈ A, ∀ b ∈ A, ∀ m : ℕ, ∀ C : Chain m,
    (∀ i, C.block i ⊆ Finset.range N) → ∀ i j : Fin m, i < j → ∃ c : ℕ,
      ((masterScale (primorial w) w N (C.block i) : ℚ) * a) /
        ((masterScale (primorial w) w N (C.block j) : ℚ) * b) = (primorial w : ℚ) * c
  uniform_small_prime : ∀ w,
    smallPrimeDivisibilityProbability ((primorial w) ^ (F.exponent w)) w D (F.exponent w) <
      1 / ((w : ℝ) + 1)
  pool_beyond_modulus : ∀ w l, F.residueModulus w l < (F.pool w l).lower
  pool_positive_mass : ∀ w l, 0 < (F.pool w l).harmonicMass
  pool_lower_growth : ∀ l, PowerDominates atTop (fun w => ((F.pool w l).lower : ℝ))
    (fun w => (F.auxiliary w l : ℝ))
  pool_mass_growth : ∀ l, PowerDominates atTop (fun w => (F.pool w l).harmonicMass)
    (fun w => (F.auxiliary w l : ℝ))
  pool_residue_error : ∀ l, RapidlySmall atTop (fun w => (F.auxiliary w l : ℝ))
    (fun w => FiniteMass.distance
      (primePoolResidueMass (F.residueModulus w l) (F.pool w l).lower (F.pool w l).upper)
      (primeUnitUniformMass (F.residueModulus w l)))
  gap_positive : ∀ w l, 0 < F.gap w l
  gap_modulus_dvd : ∀ w l, (F.modulus w : ℕ) ∣ F.gap w l
  gap_earlier_dvd : ∀ w j l, j < l → F.gap w j ∣ F.gap w l
  gap_polynomial_dvd : ∀ w l, ∀ f ∈ D, ∀ x : Fin n → ℕ,
    (∀ i, x i ∈ primePool (F.pool w l).lower (F.pool w l).upper) →
    MvPolynomial.eval (fun i => (x i : ℤ)) f ≠ 0 →
    (F.modulus w : ℕ) * (MvPolynomial.eval (fun i => (x i : ℤ)) f).natAbs ∣ F.gap w l
  gap_growth : ∀ l, PowerDominates atTop (fun w => (F.gap w l : ℝ))
    (fun w => ((F.pool w l).upper + F.auxiliary w l : ℝ))
  dyadic_cutoff : ∀ w l, ∃ e : ℕ, F.cutoff w l = 2 ^ e
  cutoff_growth : ∀ l, PowerDominates atTop (fun w => Real.log (F.cutoff w l : ℝ))
    (fun w => (F.gap w l : ℝ))
  polynomial_zeros : ∀ l, RapidlySmall atTop (fun w => (F.auxiliary w l : ℝ))
    (fun w => primePolynomialFamilyZeroMass (F.pool w l).lower (F.pool w l).upper D)
  repeated_entries : ∀ l, RapidlySmall atTop (fun w => (F.auxiliary w l : ℝ))
    (fun w => primeRepeatedMass n (F.pool w l).lower (F.pool w l).upper)
  actual_small_prime : ∀ l, Tendsto (fun w => primeSmallPrimeDivisibilityProbability
    (F.pool w l).lower (F.pool w l).upper w D (F.exponent w)) atTop (𝓝 0)

theorem constructedMasterFamily_conditions {n : ℕ} (N : ℕ) (A : Finset ℚ)
    (hA : ∀ a ∈ A, 0 < a) (D : Finset (MvPolynomial (Fin n) ℤ))
    (hD : ∀ f ∈ D, f ≠ 0) : MasterParameterConditions N A D (constructedMasterFamily N D hD) := by
  let F := constructedMasterFamily N D hD
  change MasterParameterConditions N A D F
  have haux (w l : ℕ) : F.auxiliary w l = masterStageAuxiliary (F.modulus w)
      (masterPrimeHistory w (F.exponent w) (F.modulus w) D l) :=
    constructedMasterFamily_auxiliary N D hD w l
  have hpool (w l : ℕ) : F.pool w l = masterStagePool w (F.exponent w) (F.modulus w)
      (masterPrimeHistory w (F.exponent w) (F.modulus w) D l) := rfl
  have hgap (w l : ℕ) : F.gap w l = masterStageGap w (F.exponent w) (F.modulus w) D
      (masterPrimeHistory w (F.exponent w) (F.modulus w) D l) := rfl
  refine {
    exponent_positive := fun w => (masterSmallPrimeExponent_spec D hD w).1
    smooth_modulus := fun w => ⟨_, rfl⟩
    primorial_power_dvd := fun w => power_dvd_smoothMasterModulus w N _
    subset_scale_dvd := fun w _ hS => masterScale_dvd_smoothMasterModulus w _ hS
    subset_scale_le := fun w _ hS => Nat.le_of_dvd (F.modulus w).pos (masterScale_dvd_smoothMasterModulus w _ hS)
    adding_scales := fun w _ _ _ _ hadd hT hA hB =>
      adding_block_scale_divisibility (primorial w) w hadd hT hA hB
    coefficients := constructedMasterFamily_coefficients N A hA D hD
    chain_ratios := rational_family_chain_ratios N A hA
    uniform_small_prime := ?_
    pool_beyond_modulus := ?_
    pool_positive_mass := ?_
    pool_lower_growth := ?_
    pool_mass_growth := ?_
    pool_residue_error := ?_
    gap_positive := fun w l => masterStageGap_pos _ _ _ D _
    gap_modulus_dvd := fun w l => masterStageGap_modulus_dvd _ _ _ D _
    gap_earlier_dvd := fun w j l hjl => masterPrimeHistory_gap_dvd _ _ _ D hjl
    gap_polynomial_dvd := fun w l f hf x hx hz => masterStageGap_value_dvd _ _ _ _ hf hx hz
    gap_growth := ?_
    dyadic_cutoff := fun w l => masterStageCutoff_power_two _ _ _ D _
    cutoff_growth := fun l => masterStageCutoff_powerDominates D
    polynomial_zeros := ?_
    repeated_entries := ?_
    actual_small_prime := ?_ }
  · intro w
    exact (masterSmallPrimeExponent_spec D hD w).2 _ le_rfl _
      (Nat.pow_pos (primorial_pos w)) dvd_rfl
  · intro w l
    dsimp [MasterParameterFamily.residueModulus]
    rw [haux, hpool]
    exact (equidistributedGrowingPrimePool_bounds _ _ _ (masterStageModulus_pos _ _ _)).1
  · intro w l
    rw [hpool]
    exact equidistributedGrowingPrimePool_mass_pos _ _ _ (masterStageModulus_pos _ _ _)
  · intro l
    simpa only [haux, hpool] using (masterStagePool_lower_powerDominates
      (M := F.modulus) (e0 := F.exponent)
      (history := fun w => masterPrimeHistory w (F.exponent w) (F.modulus w) D l))
  · intro l
    simpa only [haux, hpool] using (masterStagePool_mass_powerDominates
      (M := F.modulus) (e0 := F.exponent)
      (history := fun w => masterPrimeHistory w (F.exponent w) (F.modulus w) D l))
  · intro l
    simpa only [MasterParameterFamily.residueModulus, haux, hpool] using (masterStagePool_residue_rapid
      (M := F.modulus) (e0 := F.exponent)
      (history := fun w => masterPrimeHistory w (F.exponent w) (F.modulus w) D l))
  · intro l
    simpa only [haux, hpool, hgap, Nat.cast_add] using (masterStageGap_powerDominates
      (M := F.modulus) (e0 := F.exponent)
      (history := fun w => masterPrimeHistory w (F.exponent w) (F.modulus w) D l) D)
  · intro l
    simpa only [haux, hpool] using (masterStagePolynomialFamilyZero_rapid
      (M := F.modulus) (e0 := F.exponent)
      (history := fun w => masterPrimeHistory w (F.exponent w) (F.modulus w) D l) D hD)
  · intro l
    simpa only [haux, hpool] using (masterStageRepeated_rapid
      (M := F.modulus) (e0 := F.exponent)
      (history := fun w => masterPrimeHistory w (F.exponent w) (F.modulus w) D l) n)
  · intro l
    exact masterStage_smallPrime_actual_probability_tendsto D hD F.modulus
      (fun w => masterPrimeHistory w (F.exponent w) (F.modulus w) D l)

theorem exists_masterParameterFamily {n : ℕ} (N : ℕ) (A : Finset ℚ)
    (hA : ∀ a ∈ A, 0 < a) (D : Finset (MvPolynomial (Fin n) ℤ))
    (hD : ∀ f ∈ D, f ≠ 0) : ∃ F : MasterParameterFamily, MasterParameterConditions N A D F :=
  ⟨constructedMasterFamily N D hD, constructedMasterFamily_conditions N A hA D hD⟩

end Hindman168
