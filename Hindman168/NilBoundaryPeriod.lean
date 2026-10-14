import Hindman168.NilPeriodicBoundaryCells
import Mathlib.Data.Int.Init

/-! The bad roots and an arbitrary periodic restriction have a common
period q*R. Counting all q complete R-cells bounds the occupied residues.
The period is used only to estimate the original harmonic law later. -/

namespace Hindman168
open scoped BigOperators Classical

noncomputable def jointBoundaryResidues (R H q : ℕ) (U : Finset ℕ) : Finset ℕ :=
  (Finset.range (q * R)).filter (fun n => n % q ∈ U ∧
    ¬ intervalInteriorRoot R H (n : ℤ))

theorem jointBoundaryResidues_subset (R H q : ℕ) (U : Finset ℕ) :
    jointBoundaryResidues R H q U ⊆ Finset.range (q * R) := Finset.filter_subset _ _

theorem jointBoundaryResidues_image (R H q : ℕ) (U : Finset ℕ)
    (_hq : 0 < q) (hU : U ⊆ Finset.range q) :
    (jointBoundaryResidues R H q U).image (fun n : ℕ => (n : ℤ)) =
      (periodicCellWindow 0 (q * R) q U).filter (fun y => ¬ intervalInteriorRoot R H y) := by
  ext y
  simp only [Finset.mem_image, jointBoundaryResidues, Finset.mem_filter,
    Finset.mem_range, periodicCellWindow_mem_iff, integerWindow, zero_add, Finset.mem_Ico]
  constructor
  · rintro ⟨n, ⟨hn, hu, hb⟩, rfl⟩
    exact ⟨⟨⟨Int.natCast_nonneg n, by exact_mod_cast hn⟩,
      n % q, hu, (Int.natCast_mod n q).symm⟩, hb⟩
  · rintro ⟨⟨⟨hy0, hyQ⟩, a, ha, he⟩, hb⟩
    have hy : (y.toNat : ℤ) = y := Int.toNat_of_nonneg hy0
    refine ⟨y.toNat, ⟨?_, ?_, by simpa only [hy] using hb⟩, hy⟩
    · exact_mod_cast hy ▸ hyQ
    · have haQ := Finset.mem_range.mp (hU ha)
      have hnmod : y.toNat % q = a := by
        apply Int.ofNat_injective
        change ((y.toNat % q : ℕ) : ℤ) = (a : ℤ)
        rw [Int.natCast_mod, hy]
        exact he
      simpa only [hnmod] using ha

theorem periodicCell_boundary_count_dimension_bound (k : ℤ) (R H q d : ℕ)
    (hR : 0 < R) (hq : 0 < q) (hH : H ≤ d * R)
    (U : Finset ℕ) (hU : U ⊆ Finset.range q) :
    (((periodicCellWindow (k * R) R q U).filter
      (fun y => ¬ intervalInteriorRoot R H y)).card : ℝ) ≤
      (U.card : ℝ) * (2 * (H : ℝ) / q + 2 + 4 * d) := by
  have hb := periodicCell_boundary_count_bound k R H q hR hq U hU
  have hf := (abs_le.mp (periodicCellCount_discrepancy (k * R) R q hq U hU)).2
  have hRr : (0 : ℝ) < R := by exact_mod_cast hR
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hHr : (H : ℝ) ≤ (d : ℝ) * R := by exact_mod_cast hH
  have ha : (H : ℝ) / R ≤ d := (div_le_iff₀ hRr).mpr hHr
  have hfull : periodicCellCount (k * R) R q U ≤ (U.card : ℝ) * R / q + U.card := by linarith
  calc
    _ ≤ (2 * (H : ℝ) / R) * periodicCellCount (k * R) R q U +
      (U.card : ℝ) * (2 + 2 * (H : ℝ) / R) := hb
    _ ≤ (2 * (H : ℝ) / R) * ((U.card : ℝ) * R / q + U.card) +
      (U.card : ℝ) * (2 + 2 * (H : ℝ) / R) :=
      add_le_add (mul_le_mul_of_nonneg_left hfull
        (div_nonneg (by positivity : 0 ≤ 2 * (H : ℝ)) hRr.le)) le_rfl
    _ = (U.card : ℝ) * (2 * (H : ℝ) / q + 2 + 4 * ((H : ℝ) / R)) := by
      field_simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)

theorem jointBoundaryResidues_card_bound (R H q d : ℕ)
    (hR : 0 < R) (hq : 0 < q) (hH : H ≤ d * R)
    (U : Finset ℕ) (hU : U ⊆ Finset.range q) :
    ((jointBoundaryResidues R H q U).card : ℝ) ≤
      (U.card : ℝ) * (2 * (H : ℝ) + (q : ℝ) * (2 + 4 * d)) := by
  let C (k : ℕ) := (periodicCellWindow ((k : ℤ) * R) R q U).filter
    (fun y => ¬ intervalInteriorRoot R H y)
  have hs : (periodicCellWindow 0 (q * R) q U).filter
      (fun y => ¬ intervalInteriorRoot R H y) ⊆ (Finset.range q).biUnion C := by
    intro y hy
    obtain ⟨hw, hb⟩ := Finset.mem_filter.mp hy
    obtain ⟨hwin, hres⟩ := (periodicCellWindow_mem_iff 0 (q * R) q U y).mp hw
    have hyI := Finset.mem_Ico.mp hwin
    simp only [zero_add, Nat.cast_mul] at hyI
    have hRz : (0 : ℤ) < R := by exact_mod_cast hR
    have hk0 : 0 ≤ y / (R : ℤ) := Int.ediv_nonneg hyI.1 hRz.le
    have hkq : y / (R : ℤ) < q := (Int.ediv_lt_iff_lt_mul hRz).mpr hyI.2
    let k := (y / (R : ℤ)).toNat
    have hk : (k : ℤ) = y / (R : ℤ) := Int.toNat_of_nonneg hk0
    apply Finset.mem_biUnion.mpr
    refine ⟨k, Finset.mem_range.mpr (by exact_mod_cast hk ▸ hkq), ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨(periodicCellWindow_mem_iff _ _ _ _ _).mpr ⟨?_, hres⟩, hb⟩
    apply Finset.mem_Ico.mpr
    exact (Int.ediv_eq_iff_of_pos hRz).mp hk.symm
  have hc := (Finset.card_le_card hs).trans Finset.card_biUnion_le
  have he := jointBoundaryResidues_image R H q U hq hU
  have him : ((jointBoundaryResidues R H q U).image (fun n : ℕ => (n : ℤ))).card =
      (jointBoundaryResidues R H q U).card := Finset.card_image_of_injective _ Int.ofNat_injective
  rw [he] at him
  have hcr : ((jointBoundaryResidues R H q U).card : ℝ) ≤
      ∑ k ∈ Finset.range q, ((C k).card : ℝ) := by
    rw [← him]
    exact_mod_cast hc
  calc
    _ ≤ ∑ k ∈ Finset.range q, ((U.card : ℝ) * (2 * (H : ℝ) / q + 2 + 4 * d)) :=
      hcr.trans (Finset.sum_le_sum (fun k _ =>
        periodicCell_boundary_count_dimension_bound k R H q d hR hq hH U hU))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
      field_simp
      ring

theorem jointBoundaryResidues_card_total_bound (R H q : ℕ) (hq : 0 < q)
    (U : Finset ℕ) (hU : U ⊆ Finset.range q) :
    ((jointBoundaryResidues R H q U).card : ℝ) ≤ (U.card : ℝ) * ((R : ℝ) + 1) := by
  have he := jointBoundaryResidues_image R H q U hq hU
  have hc := Finset.card_le_card (Finset.filter_subset
    (fun y => ¬ intervalInteriorRoot R H y) (periodicCellWindow 0 (q * R) q U))
  have him : ((jointBoundaryResidues R H q U).image (fun n : ℕ => (n : ℤ))).card =
      (jointBoundaryResidues R H q U).card := Finset.card_image_of_injective _ Int.ofNat_injective
  rw [he] at him
  have hcr : ((jointBoundaryResidues R H q U).card : ℝ) ≤ periodicCellCount 0 (q * R) q U := by
    rw [periodicCellCount_eq_card, ← him]
    exact_mod_cast hc
  have hb := (abs_le.mp (periodicCellCount_discrepancy 0 (q * R) q hq U hU)).2
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hh : (U.card : ℝ) * (q * R : ℕ) / q = (U.card : ℝ) * R := by
    rw [Nat.cast_mul]
    field_simp
  rw [hh] at hb
  nlinarith

theorem jointBoundaryResidues_mem_mod (R H q : ℕ) (hR : 0 < R) (hq : 0 < q)
    (U : Finset ℕ) (n : ℕ) :
    n % (q * R) ∈ jointBoundaryResidues R H q U ↔
      n % q ∈ U ∧ ¬ intervalInteriorRoot R H (n : ℤ) := by
  have hqmod : (n % (q * R)) % q = n % q := Nat.mod_mod_of_dvd n (dvd_mul_right q R)
  have hRmod : (n % (q * R)) % R = n % R := Nat.mod_mod_of_dvd n (dvd_mul_left R q)
  have hint : intervalInteriorRoot R H ((n % (q * R) : ℕ) : ℤ) ↔
      intervalInteriorRoot R H (n : ℤ) := by
    simp only [intervalInteriorRoot, ← Int.natCast_mod, hRmod]
  simp only [jointBoundaryResidues, Finset.mem_filter, Finset.mem_range,
    Nat.mod_lt n (Nat.mul_pos hq hR), true_and, hqmod, hint]

end Hindman168
