import Hindman168.AlignmentIntegerPairScales
import Mathlib.Data.Int.ModEq

/-! Bounded residue shifts use the full modulus M * V. This supplies
V-divisibility of the progression shift, without requiring t to divide q. -/

namespace Hindman168

def alignmentProgressionShift (q t ρ M : ℕ) : ℤ :=
  ((q : ℤ) - (t : ℤ) * ρ) / M

theorem alignment_residue_progression_exact {q t ρ M V : ℕ} (hM : 0 < M)
    (hcong : (t : ℤ) * ρ ≡ q [ZMOD (M : ℤ) * V]) :
    (M : ℤ) * alignmentProgressionShift q t ρ M = (q : ℤ) - (t : ℤ) * ρ ∧
      (V : ℤ) ∣ alignmentProgressionShift q t ρ M := by
  obtain ⟨k, hk⟩ := hcong.dvd
  have hMz : (M : ℤ) ≠ 0 := by exact_mod_cast hM.ne'
  have hshift : alignmentProgressionShift q t ρ M = (V : ℤ) * k := by
    unfold alignmentProgressionShift
    rw [hk, mul_assoc, Int.mul_ediv_cancel_left _ hMz]
  rw [hshift]
  exact ⟨by simpa only [mul_assoc] using hk.symm, dvd_mul_right _ _⟩

theorem alignment_residue_divisible {q t ρ W L : ℕ}
    (hunit : Nat.Coprime t W) (hWL : W ∣ L) (hWq : W ∣ q)
    (hcong : (t : ℤ) * ρ ≡ q [ZMOD L]) : W ∣ ρ := by
  have hWLz : (W : ℤ) ∣ (L : ℤ) := by exact_mod_cast hWL
  have hWqz : (W : ℤ) ∣ (q : ℤ) := by exact_mod_cast hWq
  have hWtr : (W : ℤ) ∣ (t : ℤ) * ρ := by
    have hd := hWLz.trans hcong.dvd
    have hs := Int.dvd_sub hWqz hd
    simpa only [sub_sub_cancel] using hs
  have hr := Int.dvd_of_dvd_mul_right_of_gcd_one hWtr
    (by simpa only [Int.gcd_def, Int.natAbs_natCast] using hunit.symm)
  exact_mod_cast hr

theorem alignment_bounded_residue_shift (q t M V W : ℕ)
    (hM : 0 < M) (hV : 0 < V) (hunit : Nat.Coprime t (M * V))
    (hWMV : W ∣ M * V) (hWq : W ∣ q) :
    ∃ ρ : ℕ, ρ < M * V ∧ W ∣ ρ ∧
      (t : ℤ) * ρ ≡ q [ZMOD (M : ℤ) * V] ∧
      (M : ℤ) * alignmentProgressionShift q t ρ M = (q : ℤ) - (t : ℤ) * ρ ∧
      (V : ℤ) ∣ alignmentProgressionShift q t ρ M := by
  obtain ⟨ρ, hρ, hcong⟩ := Nat.exists_mul_mod_eq_of_coprime q hunit
    (Nat.mul_pos hM hV).ne'
  change Nat.ModEq (M * V) (t * ρ) q at hcong
  have hz : (t : ℤ) * ρ ≡ q [ZMOD (M : ℤ) * V] := by
    simpa only [← Nat.cast_mul, Int.natCast_modEq_iff] using hcong
  have hunitW : Nat.Coprime t W := hunit.of_dvd_right hWMV
  have hr := alignment_residue_divisible hunitW hWMV hWq
    (by simpa only [Nat.cast_mul] using hz)
  obtain ⟨hexact, hdiv⟩ := alignment_residue_progression_exact hM hz
  exact ⟨ρ, hρ, hr, hz, hexact, hdiv⟩

theorem alignment_integer_displacement_identity {q t ρ M : ℕ}
    (hexact : (M : ℤ) * alignmentProgressionShift q t ρ M =
      (q : ℤ) - (t : ℤ) * ρ) (p m : ℤ) :
    (t : ℤ) * (p + m * ρ) + m * M * alignmentProgressionShift q t ρ M =
      (t : ℤ) * p + m * q := by
  calc
    _ = (t : ℤ) * (p + m * ρ) + m *
      ((M : ℤ) * alignmentProgressionShift q t ρ M) := by ring
    _ = (t : ℤ) * p + m * q := by rw [hexact]; ring

end Hindman168
