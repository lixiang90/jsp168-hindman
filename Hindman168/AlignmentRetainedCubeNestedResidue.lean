import Hindman168.AlignmentRetainedCubeResidue

/-! Original CRT fine/coarse residue vectors are nested when a factor is
removed, EVEN when that factor shares primes with the retained product. -/
namespace Hindman168

theorem alignment_retained_cube_residue_class_iff {κ : Type*}
    (M d retained : ℕ) (hr : 0 < retained) (hM : Nat.Coprime M retained)
    (hd : Nat.Coprime d retained) (Y r : ℤ) (c z : Option κ → ℤ) :
    (∀ k, Int.ModEq (d*retained : ℕ) (alignmentRetainedCubeResidue M d retained Y r c k) (z k)) ↔
    (∀ k, Int.ModEq d (z k) (c k)) ∧
      Int.ModEq retained ((M : ℤ)*(z none+Y)+r) 0 ∧
      (∀ k : κ, Int.ModEq retained (z (some k)) 0) := by
  constructor
  · intro hz
    have hn := (alignmentRetainedRepresentative_class_iff M d retained hr hM hd Y r (c none) (z none)).mp
      (by simpa only [alignmentRetainedCubeResidue,Option.elim_none,Nat.cast_mul] using hz none)
    refine ⟨?_,hn.2,?_⟩
    · intro k
      cases k with
      | none => exact hn.1
      | some k => exact ((alignment_retained_increment_class_iff d retained hr hd _ _).mp (hz (some k))).1
    · intro k
      exact ((alignment_retained_increment_class_iff d retained hr hd _ _).mp (hz (some k))).2
  · rintro ⟨hc,ho,hi⟩ k
    cases k with
    | none =>
      simpa only [alignmentRetainedCubeResidue,Option.elim_none,Nat.cast_mul] using
        (alignmentRetainedRepresentative_class_iff M d retained hr hM hd Y r (c none) (z none)).mpr ⟨hc none,ho⟩
    | some k => exact (alignment_retained_increment_class_iff d retained hr hd _ _).mpr ⟨hc (some k),hi k⟩

theorem alignment_retained_cube_fine_coarse_compatible {κ : Type*}
    (M d retained t : ℕ) (hr : 0 < retained)
    (hM : Nat.Coprime M retained) (hd : Nat.Coprime d retained)
    (hMfine : Nat.Coprime M (retained*t)) (hdfine : Nat.Coprime d (retained*t))
    (Y r : ℤ) (c : Option κ → ℤ) :
    ∀ k, Int.ModEq (d*retained : ℕ)
      (alignmentRetainedCubeResidue M d retained Y r c k)
      (alignmentRetainedCubeResidue M d (retained*t) Y r c k) := by
  apply (alignment_retained_cube_residue_class_iff M d retained hr hM hd Y r c _).mpr
  refine ⟨alignment_retained_cube_residue_denominator_class M d (retained*t) hdfine Y r c,?_,?_⟩
  · have ho := alignmentRetainedRepresentative_origin M d (retained*t) hMfine hdfine Y r (c none)
    exact ho.of_dvd (by exact_mod_cast Nat.dvd_mul_right retained t)
  · intro k
    have ho := alignmentRetainedRepresentative_origin 1 d (retained*t) (by simp) hdfine 0 0 (c (some k))
    have hh := ho.of_dvd (show (retained : ℤ) ∣ ((retained*t : ℕ) : ℤ) by exact_mod_cast Nat.dvd_mul_right retained t)
    simpa only [alignmentRetainedCubeResidue,Option.elim_some,Nat.cast_one,one_mul,add_zero] using hh

end Hindman168
