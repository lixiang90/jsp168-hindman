import Hindman168.AlignmentNestedStepClasses

namespace Hindman168

def alignmentRetainedOriginResidue (M q : ℕ) (Y r : ℤ) : ℤ :=
  -Y - r * Nat.gcdA M q

def alignmentRetainedRepresentative (M d q : ℕ) (Y r c : ℤ) : ℤ :=
  (c + (d : ℤ) * Nat.gcdA d q * (alignmentRetainedOriginResidue M q Y r - c)) %
    ((d : ℤ) * q)

theorem alignmentRetainedOriginResidue_valid (M q : ℕ) (hMq : Nat.Coprime M q) (Y r : ℤ) :
    Int.ModEq q ((M : ℤ) * (alignmentRetainedOriginResidue M q Y r + Y) + r) 0 := by
  have h : Int.ModEq q ((M : ℤ) * Nat.gcdA M q) 1 := by
    simpa only [hMq.gcd_eq_one, Nat.cast_one] using Int.gcd_a_modEq M q
  have hh := (h.mul_left (-r)).add_right r
  have he : (M : ℤ) * (alignmentRetainedOriginResidue M q Y r + Y) + r =
      -r * ((M : ℤ) * Nat.gcdA M q) + r := by
    unfold alignmentRetainedOriginResidue
    ring
  rw [he]
  simpa only [mul_one, neg_add_cancel] using hh

theorem alignmentRetainedRepresentative_bounds (M d q : ℕ) (hd : 0 < d) (hq : 0 < q)
    (Y r c : ℤ) :
    0 ≤ alignmentRetainedRepresentative M d q Y r c ∧
      alignmentRetainedRepresentative M d q Y r c < (d : ℤ) * q := by
  have h : (0 : ℤ) < (d : ℤ) * q := by exact_mod_cast Nat.mul_pos hd hq
  exact ⟨Int.emod_nonneg _ h.ne', Int.emod_lt_of_pos _ h⟩

theorem alignmentRetainedRepresentative_classes (M d q : ℕ) (hdq : Nat.Coprime d q)
    (Y r c : ℤ) :
    Int.ModEq d (alignmentRetainedRepresentative M d q Y r c) c ∧
      Int.ModEq q (alignmentRetainedRepresentative M d q Y r c) (alignmentRetainedOriginResidue M q Y r) := by
  let v := alignmentRetainedOriginResidue M q Y r
  let b := c + (d : ℤ) * Nat.gcdA d q * (v - c)
  have hm : Int.ModEq ((d : ℤ) * q) (alignmentRetainedRepresentative M d q Y r c) b :=
    Int.mod_modEq b ((d : ℤ) * q)
  have hb : Int.ModEq d b c := by
    have he : b = c + (d : ℤ) * (Nat.gcdA d q * (v - c)) := by dsimp [b]; ring
    rw [he]
    exact Int.modEq_add_fac_self
  have hi : Int.ModEq q ((d : ℤ) * Nat.gcdA d q) 1 := by
    simpa only [hdq.gcd_eq_one, Nat.cast_one] using Int.gcd_a_modEq d q
  have hqv : Int.ModEq q b v := by
    simpa only [b, one_mul, add_sub_cancel] using (hi.mul_right (v - c)).add_left c
  exact ⟨(hm.of_dvd (dvd_mul_right (d : ℤ) q)).trans hb,
    (hm.of_dvd (dvd_mul_left (q : ℤ) d)).trans hqv⟩

theorem alignmentRetainedRepresentative_origin (M d q : ℕ)
    (hMq : Nat.Coprime M q) (hdq : Nat.Coprime d q) (Y r c : ℤ) :
    Int.ModEq q ((M : ℤ) * (alignmentRetainedRepresentative M d q Y r c + Y) + r) 0 := by
  have h := (alignmentRetainedRepresentative_classes M d q hdq Y r c).2
  exact (((h.add_right Y).mul_left M).add_right r).trans
    (alignmentRetainedOriginResidue_valid M q hMq Y r)

end Hindman168
