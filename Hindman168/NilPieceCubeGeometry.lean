import Hindman168.NilPieceZeroPrimeDual

/-! Actual shift support, interval interior and residue stability for the
original zero-prime cube. Every integer root is allowed; no cutoff or
positive-root assumption is needed for the geometric containment. -/

namespace Hindman168
open scoped BigOperators Classical
open FiniteMass

variable {d : ℕ}

def intervalResiduePiece (R M : ℕ) (y : ℤ) : ℤ × ℤ := (y / (R : ℤ), y % (M : ℤ))

def zeroPrimeCubeMargin (d R J M : ℕ) : ℕ := d * M * (R / (J * M))

def intervalInteriorRoot (R H : ℕ) (y : ℤ) : Prop :=
  (H : ℤ) ≤ y % (R : ℤ) ∧ y % (R : ℤ) + H < R

theorem zeroPrimeRecipeShiftMass_slot_bounds (R J M : ℕ)
    (z : Fin d × Bool → ℤ) (hz : z ∈ (zeroPrimeRecipeShiftMass d R J M).support)
    (j : Fin d × Bool) : 0 ≤ z j ∧ z j < (R / (J * M) : ℕ) := by
  classical
  have hmass : zeroPrimeRecipeShiftMass d R J M z ≠ 0 := Finsupp.mem_support_iff.mp hz
  change piMass (fun _ : Fin d × Bool => uniformIntervalMass 0 (R / (J * M))) z ≠ 0 at hmass
  rw [piMass_apply] at hmass
  have hne := Finset.prod_ne_zero_iff.mp hmass j (Finset.mem_univ j)
  rw [uniformIntervalMass_apply] at hne
  have hwin : z j ∈ integerWindow 0 (R / (J * M)) := by
    by_contra h
    exact hne (if_neg h)
  simpa only [integerWindow, Finset.mem_Ico, zero_add] using hwin

theorem zeroPrimeRecipeVertex_distance_bound (R J M : ℕ) (y : ℤ)
    (z : Fin d × Bool → ℤ) (hz : z ∈ (zeroPrimeRecipeShiftMass d R J M).support)
    (S : CubeVertex d) :
    |zeroPrimeRecipeVertex M y z S - y| ≤ (zeroPrimeCubeMargin d R J M : ℤ) := by
  have hdiff (j : Fin d) : |z (j, true) - z (j, false)| ≤ (R / (J * M) : ℕ) := by
    obtain ⟨ha, hb⟩ := zeroPrimeRecipeShiftMass_slot_bounds R J M z hz (j, true)
    obtain ⟨hc, hd⟩ := zeroPrimeRecipeShiftMass_slot_bounds R J M z hz (j, false)
    rw [abs_le]
    omega
  have hcard : S.val.card ≤ d := by
    simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_le_card (Finset.subset_univ S.val)
  have hsum : |∑ j ∈ S.val, (z (j, true) - z (j, false))| ≤
      (d : ℤ) * (R / (J * M) : ℕ) := by
    calc
      _ ≤ ∑ j ∈ S.val, |z (j, true) - z (j, false)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ S.val, ((R / (J * M) : ℕ) : ℤ) := Finset.sum_le_sum (fun j _ => hdiff j)
      _ = (S.val.card : ℤ) * (R / (J * M) : ℕ) := by simp
      _ ≤ (d : ℤ) * (R / (J * M) : ℕ) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (Int.natCast_nonneg _)
  simp only [zeroPrimeRecipeVertex, add_sub_cancel_left, abs_mul, abs_of_nonneg (Int.natCast_nonneg M)]
  calc
    _ ≤ (M : ℤ) * ((d : ℤ) * (R / (J * M) : ℕ)) := mul_le_mul_of_nonneg_left hsum (Int.natCast_nonneg _)
    _ = (zeroPrimeCubeMargin d R J M : ℤ) := by simp only [zeroPrimeCubeMargin, Nat.cast_mul]; ring

theorem intervalInteriorRoot_shift_quotient (R H : ℕ) (hR : 0 < R)
    (y h : ℤ) (hy : intervalInteriorRoot R H y) (hh : |h| ≤ (H : ℤ)) :
    (y + h) / (R : ℤ) = y / (R : ℤ) := by
  have hRZ : (0 : ℤ) < R := by exact_mod_cast hR
  have hdecomp : y / (R : ℤ) * R + y % (R : ℤ) = y := by
    simpa only [mul_comm] using Int.mul_ediv_add_emod y (R : ℤ)
  have hlo := (abs_le.mp hh).1
  have hhi := (abs_le.mp hh).2
  apply (Int.ediv_eq_iff_of_pos hRZ).mpr
  exact ⟨by linarith [hy.1], by linarith [hy.2]⟩

theorem zeroPrimeRecipeVertex_piece_stable (R J M : ℕ) (hR : 0 < R) (y : ℤ)
    (hy : intervalInteriorRoot R (zeroPrimeCubeMargin d R J M) y)
    (z : Fin d × Bool → ℤ) (hz : z ∈ (zeroPrimeRecipeShiftMass d R J M).support)
    (S : CubeVertex d) :
    intervalResiduePiece R M (zeroPrimeRecipeVertex M y z S) = intervalResiduePiece R M y := by
  apply Prod.ext
  · change zeroPrimeRecipeVertex M y z S / (R : ℤ) = y / (R : ℤ)
    have h := intervalInteriorRoot_shift_quotient R (zeroPrimeCubeMargin d R J M) hR y
      (zeroPrimeRecipeVertex M y z S - y) hy (zeroPrimeRecipeVertex_distance_bound R J M y z hz S)
    simpa only [add_sub_cancel] using h
  · simp [intervalResiduePiece, zeroPrimeRecipeVertex, Int.add_emod]

theorem zeroPrimeCubeMargin_scale_bound (d R J M : ℕ) :
    J * zeroPrimeCubeMargin d R J M ≤ d * R := by
  calc
    _ = d * ((R / (J * M)) * (J * M)) := by unfold zeroPrimeCubeMargin; ring
    _ ≤ d * R := Nat.mul_le_mul_left d (Nat.div_mul_le_self R (J * M))

end Hindman168
