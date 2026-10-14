import Hindman168.AlignmentResidueEndpoints

namespace Hindman168

def alignmentMicrocellFirst (R M p : ℤ) : ℤ :=
  alignmentResidueEndpoint ((p / R) * R) M p

theorem alignmentMicrocellFirst_modEq (R M p : ℤ) :
    Int.ModEq M (alignmentMicrocellFirst R M p) p :=
  alignmentResidueEndpoint_modEq _ _ _

theorem alignmentMicrocellFirst_minimal (R M p z : ℤ) (hM : 0 < M)
    (hz : Int.ModEq M p z) : alignmentMicrocellFirst R M p ≤ z ↔ (p / R) * R ≤ z :=
  alignmentResidueEndpoint_le_iff _ _ _ _ hM hz

theorem alignmentMicrocellFirst_bounds (R M p : ℤ) (hM : 0 < M) (hMR : M ≤ R) :
    (p / R) * R ≤ alignmentMicrocellFirst R M p ∧
      alignmentMicrocellFirst R M p < (p / R) * R + R := by
  have h := alignmentResidueEndpoint_bounds ((p / R) * R) M p hM
  exact ⟨h.1, h.2.trans_le (by omega)⟩

theorem alignmentMicrocellFirst_distance (R M p : ℤ) (hM : 0 < M) (hMR : M ≤ R) :
    |alignmentMicrocellFirst R M p - p| ≤ R := by
  have hR : 0 < R := hM.trans_le hMR
  have hp0 := Int.emod_nonneg p hR.ne'
  have hpR := Int.emod_lt_of_pos p hR
  have he := Int.mul_ediv_add_emod p R
  have hf := alignmentMicrocellFirst_bounds R M p hM hMR
  rw [abs_le]
  constructor <;> nlinarith

theorem alignment_residue_progression_interval (A M J r ell : ℤ) (hM : 0 < M) :
    A ≤ alignmentResidueEndpoint A M r + M * ell ∧
      alignmentResidueEndpoint A M r + M * ell < A + M * J ↔ 0 ≤ ell ∧ ell < J := by
  have hb := alignmentResidueEndpoint_bounds A M r hM
  constructor
  · rintro ⟨hl, hu⟩
    constructor
    · by_contra hn
      have : ell ≤ -1 := by omega
      nlinarith
    · by_contra hn
      have : J ≤ ell := by omega
      nlinarith
  · rintro ⟨hl, hu⟩
    have : ell + 1 ≤ J := by omega
    constructor <;> nlinarith

theorem alignmentMicrocellFirst_progression (R M p ell : ℤ) (hM : 0 < M) (hMR : M ∣ R) :
    (p / R) * R ≤ alignmentMicrocellFirst R M p + M * ell ∧
      alignmentMicrocellFirst R M p + M * ell < (p / R) * R + R ↔
      0 ≤ ell ∧ ell < R / M := by
  have h := alignment_residue_progression_interval ((p / R) * R) M (R / M) p ell hM
  rw [Int.mul_ediv_cancel' hMR] at h
  exact h

end Hindman168
