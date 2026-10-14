import Hindman168.AlignmentAffineIntervalClasses

namespace Hindman168

def alignmentResidueEndpoint (A d r : ℤ) : ℤ := A + (r - A) % d

theorem alignmentResidueEndpoint_bounds (A d r : ℤ) (hd : 0 < d) :
    A ≤ alignmentResidueEndpoint A d r ∧ alignmentResidueEndpoint A d r < A + d := by
  have h₁ := Int.emod_nonneg (r - A) hd.ne'
  have h₂ := Int.emod_lt_of_pos (r - A) hd
  unfold alignmentResidueEndpoint
  omega

theorem alignmentResidueEndpoint_modEq (A d r : ℤ) :
    Int.ModEq d (alignmentResidueEndpoint A d r) r := by
  have h := (Int.mod_modEq (r - A) d).add_left A
  simpa only [alignmentResidueEndpoint, add_sub_cancel] using h

theorem alignmentResidueEndpoint_le_iff (A d r z : ℤ) (hd : 0 < d)
    (hz : Int.ModEq d r z) : alignmentResidueEndpoint A d r ≤ z ↔ A ≤ z := by
  have hb := alignmentResidueEndpoint_bounds A d r hd
  constructor
  · exact fun h => hb.1.trans h
  · intro h
    obtain ⟨k, hk⟩ := Int.modEq_iff_add_fac.mp ((alignmentResidueEndpoint_modEq A d r).trans hz)
    have hk0 : 0 ≤ k := by
      by_contra hn
      have hn' : k ≤ -1 := by omega
      nlinarith
    nlinarith

theorem alignmentResidueEndpoint_interval_exact (A B d r : ℤ) (hd : 0 < d) :
    (Finset.Ico A B).filter (fun z => Int.ModEq d r z) =
      (Finset.Ico (alignmentResidueEndpoint A d r) (alignmentResidueEndpoint B d r)).filter
        (fun z => Int.ModEq d r z) := by
  classical
  ext z
  simp only [Finset.mem_filter, Finset.mem_Ico]
  by_cases hz : Int.ModEq d r z
  · have ha := alignmentResidueEndpoint_le_iff A d r z hd hz
    have hb := alignmentResidueEndpoint_le_iff B d r z hd hz
    simp only [← not_le, ha, hb]
  · simp only [hz, and_false]

theorem alignmentResidueEndpoint_affine_displacement (A d r t b : ℤ)
    (hd : 0 < d) (ht : 0 < t) :
    0 ≤ (b + t * alignmentResidueEndpoint A d r) - (b + t * A) ∧
      (b + t * alignmentResidueEndpoint A d r) - (b + t * A) < t * d := by
  have hb := alignmentResidueEndpoint_bounds A d r hd
  constructor <;> nlinarith

end Hindman168
