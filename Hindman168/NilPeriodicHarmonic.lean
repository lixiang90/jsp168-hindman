import Hindman168.HarmonicMass
import Hindman168.FiniteProductExpectations
import Hindman168.UnitCRTJointLaw

/-! Harmonic mass of any finite periodic set, with the original endpoints
and fixed normalization. The discrepancy includes both partial endpoint
cells and is not a replacement sampling law. -/

namespace Hindman168
open scoped BigOperators Classical
open FiniteMass

noncomputable def periodicResidueWindow (A B : ℝ) (q : ℕ) (U : Finset ℕ) : Finset ℕ :=
  (Finset.Ico ⌈A⌉₊ ⌈B⌉₊).filter (fun n => n % q ∈ U)

noncomputable def periodicResidueHarmonic (A B : ℝ) (q : ℕ) (U : Finset ℕ) : ℝ :=
  ∑ n ∈ periodicResidueWindow A B q U, (n : ℝ)⁻¹

theorem periodicResidueWindow_partition (A B : ℝ) (q : ℕ) (U : Finset ℕ) :
    periodicResidueWindow A B q U = U.biUnion (fun a => residueWindow A B q a) := by
  ext n
  simp only [periodicResidueWindow, residueWindow, Finset.mem_filter, Finset.mem_biUnion]
  constructor
  · rintro ⟨hn, hu⟩
    exact ⟨n % q, hu, hn, rfl⟩
  · rintro ⟨a, ha, hn, he⟩
    exact ⟨hn, he.symm ▸ ha⟩

theorem periodicResidueHarmonic_partition (A B : ℝ) (q : ℕ) (U : Finset ℕ) :
    periodicResidueHarmonic A B q U = ∑ a ∈ U, residueHarmonic A B q a := by
  have hd : (↑U : Set ℕ).PairwiseDisjoint (fun a => residueWindow A B q a) := by
    intro a _ b _ hab
    apply Finset.disjoint_left.mpr
    intro n hn hm
    exact hab ((Finset.mem_filter.mp hn).2.symm.trans (Finset.mem_filter.mp hm).2)
  rw [periodicResidueHarmonic, periodicResidueWindow_partition, Finset.sum_biUnion hd]
  rfl

theorem periodicResidueHarmonic_error {A B : ℝ} {q : ℕ}
    (hA : 0 < A) (hAB : A < B) (hq : 0 < q)
    (U : Finset ℕ) (hU : U ⊆ Finset.range q) :
    |periodicResidueHarmonic A B q U - (U.card : ℝ) / q * Real.log (B / A)| ≤
      (U.card : ℝ) / A := by
  have hc : (∑ _a ∈ U, Real.log (B / A) / q) =
      (U.card : ℝ) / q * Real.log (B / A) := by simp [div_eq_mul_inv]; ring
  rw [← hc, periodicResidueHarmonic_partition, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ a ∈ U, |residueHarmonic A B q a - Real.log (B / A) / q| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ U, A⁻¹ := Finset.sum_le_sum (fun a ha =>
      residue_harmonic_error hA hAB hq (Finset.mem_range.mp (hU ha)))
    _ = _ := by simp [div_eq_mul_inv]

theorem rawMass_periodic_test (X W q : ℕ) (U : Finset ℕ) (c : ℝ)
    (hunit : ∀ n : ℕ, n % q ∈ U → n.Coprime W) :
    expectation (rawMass X W) (fun n => if n % q ∈ U then c else 0) =
      c * periodicResidueHarmonic X (X ^ 2 : ℕ) q U / harmonicNormalizer X W := by
  have hs : (rawMass X W).support ⊆ Finset.Ico X (X ^ 2) :=
    ((intervalMass_support X (X ^ 2 : ℕ) W _).trans (unitInterval_raw X W).subset).trans
      (Finset.filter_subset _ _)
  rw [expectation_eq_sum _ _ hs]
  have he : ∀ n ∈ Finset.Ico X (X ^ 2),
      rawMass X W n * (if n % q ∈ U then c else 0) =
      if n % q ∈ U then c * (n : ℝ)⁻¹ / harmonicNormalizer X W else 0 := by
    intro n hn
    rw [rawMass_apply]
    by_cases hu : n % q ∈ U
    · have hw : n ∈ harmonicWindow X W := Finset.mem_filter.mpr ⟨hn, hunit n hu⟩
      simp only [harmonicWeight, if_pos hu, if_pos hw]
      ring
    · simp only [if_neg hu, mul_zero]
  rw [Finset.sum_congr rfl he, ← Finset.sum_filter]
  simp only [periodicResidueHarmonic, periodicResidueWindow, Nat.ceil_natCast]
  rw [← Finset.sum_div, ← Finset.mul_sum]

theorem integerMass_periodic_test (X W q : ℕ) (U : Finset ℕ) (c : ℝ)
    (hunit : ∀ n : ℕ, n % q ∈ U → n.Coprime W) :
    expectation (integerMass X W) (fun y => if y.toNat % q ∈ U then c else 0) =
      c * periodicResidueHarmonic X (X ^ 2 : ℕ) q U / harmonicNormalizer X W := by
  rw [integerMass, expectation_push]
  calc
    _ = expectation (rawMass X W) (fun n => if n % q ∈ U then c else 0) := by
      congr 1
    _ = _ := rawMass_periodic_test X W q U c hunit

end Hindman168
