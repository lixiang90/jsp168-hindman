import Hindman168.AlignmentCubeCoordinates

namespace Hindman168

theorem alignment_nested_step_class (D t a y b : ℤ) (hD : D ≠ 0) :
    Int.ModEq (D * t) (a + D * y) (a + D * b) ↔ Int.ModEq t y b := by
  rw [Int.modEq_iff_dvd, Int.modEq_iff_dvd]
  have he : a + D * b - (a + D * y) = D * (b - y) := by ring
  rw [he]
  exact mul_dvd_mul_iff_left hD

theorem alignment_nested_step_representative (D t a c : ℤ) (hD : D ≠ 0)
    (h : Int.ModEq D a c) :
    ∃ b : ℤ, c = a + D * b ∧ ∀ y : ℤ,
      (Int.ModEq (D * t) (a + D * y) c ↔ Int.ModEq t y b) := by
  obtain ⟨b, hb⟩ := Int.modEq_iff_add_fac.mp h
  exact ⟨b, hb, fun y => hb ▸ alignment_nested_step_class D t a y b hD⟩

theorem alignmentCubeBase_residue_iff (M t p Y ell a d : ℤ) (ht : t ≠ 0) :
    Int.ModEq (d * t) (alignmentCubeBase M t p Y ell)
      (alignmentCubeBase M t p Y a) ↔ Int.ModEq d ell a := by
  have h := alignment_nested_step_class t d (t * p / M - Y) ell a ht
  have he (b : ℤ) : alignmentCubeBase M t p Y b = t * p / M - Y + t * b := by
    unfold alignmentCubeBase
    ring
  rw [he ell, he a, mul_comm d t]
  exact h

end Hindman168
