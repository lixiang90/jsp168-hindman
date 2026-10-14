import Hindman168.AlignmentRetainedCRT

namespace Hindman168

theorem alignment_coprime_modEq_cancel (M q : ℕ) (hq : 0 < q)
    (hMq : Nat.Coprime M q) (a b : ℤ)
    (h : Int.ModEq q ((M : ℤ) * a) ((M : ℤ) * b)) : Int.ModEq q a b := by
  have hh := h.cancel_left_div_gcd (by exact_mod_cast hq)
  simpa only [Int.gcd_def, Int.natAbs_natCast, hMq.symm.gcd_eq_one, Nat.cast_one,
    Int.ediv_one] using hh

theorem alignmentRetainedRepresentative_class_iff (M d q : ℕ) (hq : 0 < q)
    (hMq : Nat.Coprime M q) (hdq : Nat.Coprime d q) (Y r c z : ℤ) :
    Int.ModEq ((d : ℤ) * q) (alignmentRetainedRepresentative M d q Y r c) z ↔
      Int.ModEq d z c ∧ Int.ModEq q ((M : ℤ) * (z + Y) + r) 0 := by
  have hc := alignmentRetainedRepresentative_classes M d q hdq Y r c
  have ho := alignmentRetainedRepresentative_origin M d q hMq hdq Y r c
  constructor
  · intro h
    have h₁ := h.of_dvd (dvd_mul_right (d : ℤ) q)
    have h₂ := h.of_dvd (dvd_mul_left (q : ℤ) d)
    exact ⟨h₁.symm.trans hc.1, (((h₂.symm.add_right Y).mul_left M).add_right r).trans ho⟩
  · rintro ⟨hz, hzo⟩
    have hm := (ho.trans hzo.symm).add_right_cancel' r
    have hqz := (alignment_coprime_modEq_cancel M q hq hMq _ _ hm).add_right_cancel' Y
    exact (Int.modEq_and_modEq_iff_modEq_mul (by simpa only [Int.natAbs_natCast] using hdq)).mp
      ⟨hc.1.trans hz.symm, hqz⟩

theorem alignment_retained_cube_class (M d q : ℕ) (hq : 0 < q)
    (hMq : Nat.Coprime M q) (hdq : Nat.Coprime d q) (t p Y r c ell : ℤ)
    (hqt : (q : ℤ) ∣ t) (hr : (t * p) % M = r)
    (hc : Int.ModEq d (alignmentCubeBase M t p Y ell) c) :
    Int.ModEq ((d : ℤ) * q) (alignmentRetainedRepresentative M d q Y r c)
      (alignmentCubeBase M t p Y ell) := by
  apply (alignmentRetainedRepresentative_class_iff M d q hq hMq hdq Y r c _).mpr
  refine ⟨hc, ?_⟩
  have h := alignmentCubeBase_origin_dvd M t p Y ell q hqt
  rw [hr] at h
  exact h.modEq_zero_int

end Hindman168
