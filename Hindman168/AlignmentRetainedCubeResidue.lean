import Hindman168.AlignmentMasterRetainedCRT
import Hindman168.AlignmentCubeBoxCoordinates

/-! Literal retained residue VECTOR for base and increment coordinates.
Base uses the original exposed origin congruence; increments use zero modulo
the retained product. The entire vector is fixed before the removed factor. -/
namespace Hindman168

def alignmentRetainedCubeResidue {κ : Type*} (M d retained : ℕ)
    (Y r : ℤ) (c : Option κ → ℤ) : Option κ → ℤ :=
  fun k => k.elim (alignmentRetainedRepresentative M d retained Y r (c none))
    (fun k => alignmentRetainedRepresentative 1 d retained 0 0 (c (some k)))

theorem alignment_retained_cube_residue_bounds {κ : Type*} (M d retained : ℕ)
    (hd : 0 < d) (hretained : 0 < retained) (Y r : ℤ) (c : Option κ → ℤ) :
    ∀ k, 0 ≤ alignmentRetainedCubeResidue M d retained Y r c k ∧
      alignmentRetainedCubeResidue M d retained Y r c k < (d*retained : ℕ) := by
  intro k
  cases k with
  | none =>
    simpa only [alignmentRetainedCubeResidue,Option.elim_none,Nat.cast_mul] using
      alignmentRetainedRepresentative_bounds M d retained hd hretained Y r (c none)
  | some k =>
    simpa only [alignmentRetainedCubeResidue,Option.elim_some,Nat.cast_mul] using
      alignmentRetainedRepresentative_bounds 1 d retained hd hretained 0 0 (c (some k))

theorem alignment_retained_cube_residue_denominator_class {κ : Type*}
    (M d retained : ℕ) (hd : Nat.Coprime d retained) (Y r : ℤ) (c : Option κ → ℤ) :
    ∀ k, Int.ModEq d (alignmentRetainedCubeResidue M d retained Y r c k) (c k) := by
  intro k
  cases k with
  | none => exact (alignmentRetainedRepresentative_classes M d retained hd Y r (c none)).1
  | some k => exact (alignmentRetainedRepresentative_classes 1 d retained hd 0 0 (c (some k))).1

theorem alignment_retained_increment_class_iff (d retained : ℕ) (hr : 0 < retained)
    (hd : Nat.Coprime d retained) (c z : ℤ) :
    Int.ModEq ((d*retained : ℕ) : ℤ) (alignmentRetainedRepresentative 1 d retained 0 0 c) z ↔
      Int.ModEq d z c ∧ Int.ModEq retained z 0 := by
  simpa only [Nat.cast_mul,Nat.cast_one,one_mul,add_zero] using
    alignmentRetainedRepresentative_class_iff 1 d retained hr (by simp) hd 0 0 c z

theorem alignment_retained_cube_vector_class {κ : Type*} (M d retained : ℕ)
    (hr : 0 < retained) (hM : Nat.Coprime M retained) (hd : Nat.Coprime d retained)
    (tau p Y r : ℤ) (hdiv : (retained : ℤ) ∣ tau) (hrOrigin : (tau*p) % M=r)
    (c : Option κ → ℤ) (ell : Option κ → ℤ)
    (hc : ∀ k, Int.ModEq d (alignmentCubeCoordinate M tau p Y k (ell k)) (c k)) :
    ∀ k, Int.ModEq (d*retained : ℕ) (alignmentRetainedCubeResidue M d retained Y r c k)
      (alignmentCubeCoordinate M tau p Y k (ell k)) := by
  intro k
  cases k with
  | none =>
    simpa only [Nat.cast_mul,alignmentRetainedCubeResidue,Option.elim_none,alignmentCubeCoordinate] using alignment_retained_cube_class M d retained hr hM hd
      tau p Y r (c none) (ell none) hdiv hrOrigin (hc none)
  | some k =>
    apply (alignment_retained_increment_class_iff d retained hr hd (c (some k)) _).mpr
    refine ⟨hc (some k),?_⟩
    exact (dvd_mul_of_dvd_left hdiv (ell (some k))).modEq_zero_int

end Hindman168
