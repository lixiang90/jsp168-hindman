import Hindman168.HarmonicSampling
import Hindman168.FiniteMass
import Mathlib.Tactic.Abel

/-!
# Finite signed harmonic masses on arbitrary intervals

The denominator `Z` is held fixed when the interval endpoints change.
In particular a dilated comparison interval is generally not a probability
law. Overlap cancellation is exact before any harmonic estimate is applied.
-/

namespace Hindman168

open scoped BigOperators

noncomputable def unitInterval (A B : ℝ) (W : ℕ) : Finset ℕ :=
  (Finset.Ico ⌈A⌉₊ ⌈B⌉₊).filter (fun n => n.Coprime W)

theorem mem_unitInterval {A B : ℝ} {W n : ℕ} :
    n ∈ unitInterval A B W ↔ A ≤ (n : ℝ) ∧ (n : ℝ) < B ∧ n.Coprime W := by
  simp only [unitInterval, Finset.mem_filter, Finset.mem_Ico, Nat.ceil_le, Nat.lt_ceil,
    and_assoc]

noncomputable def intervalMass (A B : ℝ) (W : ℕ) (Z : ℝ) : FiniteMass.Mass ℕ :=
  Finsupp.onFinset (unitInterval A B W)
    (fun n => if n ∈ unitInterval A B W then (n : ℝ)⁻¹ / Z else 0)
    (by intro n hn; by_contra h; simp [h] at hn)

theorem intervalMass_apply (A B : ℝ) (W n : ℕ) (Z : ℝ) :
    intervalMass A B W Z n = if n ∈ unitInterval A B W then (n : ℝ)⁻¹ / Z else 0 := rfl

theorem intervalMass_support (A B : ℝ) (W : ℕ) (Z : ℝ) :
    (intervalMass A B W Z).support ⊆ unitInterval A B W := Finsupp.support_onFinset_subset

theorem intervalMass_nonneg (A B : ℝ) (W : ℕ) {Z : ℝ} (hZ : 0 < Z) (n : ℕ) :
    0 ≤ intervalMass A B W Z n := by
  rw [intervalMass_apply]
  split_ifs
  · exact div_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) hZ.le
  · exact le_rfl

theorem intervalMass_total (A B : ℝ) (W : ℕ) (Z : ℝ) :
    FiniteMass.total (intervalMass A B W Z) = roughResidueHarmonic A B W 1 0 / Z := by
  classical
  rw [FiniteMass.total_eq_sum _ (intervalMass_support A B W Z)]
  simp only [intervalMass_apply, Finset.sum_congr rfl (fun n hn => if_pos hn)]
  rw [← Finset.sum_div]
  congr 1
  simp only [roughResidueHarmonic, roughResidueWindow, unitInterval, Nat.mod_one, and_true]

theorem unitInterval_split {A B C : ℝ} (hAC : A ≤ C) (hCB : C ≤ B) (W : ℕ) :
    unitInterval A B W = unitInterval A C W ∪ unitInterval C B W := by
  ext n
  simp only [Finset.mem_union, mem_unitInterval]
  constructor
  · rintro ⟨hAn, hnB, hc⟩
    rcases lt_or_ge (n : ℝ) C with hnC | hCn
    · exact Or.inl ⟨hAn, hnC, hc⟩
    · exact Or.inr ⟨hCn, hnB, hc⟩
  · rintro (⟨hAn, hnC, hc⟩ | ⟨hCn, hnB, hc⟩)
    · exact ⟨hAn, hnC.trans_le hCB, hc⟩
    · exact ⟨hAC.trans hCn, hnB, hc⟩

theorem unitInterval_disjoint {A B C D : ℝ} (hBC : B ≤ C) (W : ℕ) :
    Disjoint (unitInterval A B W) (unitInterval C D W) := by
  apply Finset.disjoint_left.mpr
  intro n hn hm
  have hn' := mem_unitInterval.mp hn
  have hm' := mem_unitInterval.mp hm
  exact (not_lt_of_ge (hBC.trans hm'.1)) hn'.2.1

theorem intervalMass_split {A B C : ℝ} (hAC : A ≤ C) (hCB : C ≤ B) (W : ℕ) (Z : ℝ) :
    intervalMass A B W Z = intervalMass A C W Z + intervalMass C B W Z := by
  classical
  ext n
  simp only [Finsupp.add_apply, intervalMass_apply, unitInterval_split hAC hCB W,
    Finset.mem_union]
  have hd := unitInterval_disjoint (A := A) (B := C) (C := C) (D := B) le_rfl W
  by_cases hn : n ∈ unitInterval A C W
  · have hm : n ∉ unitInterval C B W := fun hm => Finset.disjoint_left.mp hd hn hm
    simp [hn, hm]
  · by_cases hm : n ∈ unitInterval C B W <;> simp [hn, hm]

/-- Only the two exposed boundary intervals remain in the L1 difference. -/
theorem intervalMass_distance_boundaries {A B C D : ℝ} (hAC : A ≤ C) (hCB : C ≤ B)
    (hBD : B ≤ D) (W : ℕ) {Z : ℝ} (hZ : 0 < Z) :
    FiniteMass.distance (intervalMass A B W Z) (intervalMass C D W Z) =
      FiniteMass.total (intervalMass A C W Z) + FiniteMass.total (intervalMass B D W Z) := by
  rw [FiniteMass.distance, intervalMass_split hAC hCB W Z,
    intervalMass_split hCB hBD W Z]
  have he : (intervalMass A C W Z + intervalMass C B W Z) -
      (intervalMass C B W Z + intervalMass B D W Z) =
      intervalMass A C W Z - intervalMass B D W Z := by abel
  rw [he]
  apply FiniteMass.distance_of_disjoint _ _
    (intervalMass_nonneg A C W hZ) (intervalMass_nonneg B D W hZ)
  exact (unitInterval_disjoint hCB W).mono
    (intervalMass_support A C W Z) (intervalMass_support B D W Z)

theorem unitInterval_raw (X W : ℕ) : unitInterval X (X ^ 2 : ℕ) W = harmonicWindow X W := by
  simp only [unitInterval, harmonicWindow, Nat.ceil_natCast]

noncomputable def rawMass (X W : ℕ) : FiniteMass.Mass ℕ :=
  intervalMass X (X ^ 2 : ℕ) W (harmonicNormalizer X W)

theorem rawMass_apply (X W n : ℕ) : rawMass X W n = harmonicWeight X W n := by
  rw [rawMass, intervalMass_apply, unitInterval_raw]
  rfl

theorem rawMass_total {X W : ℕ} (hZ : 0 < harmonicNormalizer X W) :
    FiniteMass.total (rawMass X W) = 1 := by
  rw [FiniteMass.total_eq_sum _ (show (rawMass X W).support ⊆ harmonicWindow X W from
    (intervalMass_support X (X ^ 2 : ℕ) W _).trans (unitInterval_raw X W).subset)]
  simp only [rawMass_apply]
  exact harmonicWeight_sum hZ

noncomputable def integerMass (X W : ℕ) : FiniteMass.Mass ℤ :=
  (rawMass X W).mapDomain (fun n : ℕ => (n : ℤ))

theorem integerMass_total {X W : ℕ} (hZ : 0 < harmonicNormalizer X W) :
    FiniteMass.total (integerMass X W) = 1 := by
  rw [integerMass, FiniteMass.total_push, rawMass_total hZ]

theorem integerMass_apply_nat (X W n : ℕ) : integerMass X W (n : ℤ) = harmonicWeight X W n := by
  rw [integerMass, Finsupp.mapDomain_apply (f := fun m : ℕ => (m : ℤ))
    Int.ofNat_injective, rawMass_apply]

end Hindman168
