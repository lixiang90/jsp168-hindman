import Hindman168.AlignmentNestedStepClasses
import Hindman168.AlignedInteriorEndpoints

namespace Hindman168

theorem alignment_affine_interval_image (t b A B z : ℤ) (ht : 0 < t) :
    z ∈ (Finset.Ico A B).image (fun ell => b + t * ell) ↔
      b + t * A ≤ z ∧ z < b + t * B ∧ Int.ModEq t b z := by
  constructor
  · intro h
    obtain ⟨ell, he, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨ha, hb⟩ := Finset.mem_Ico.mp he
    refine ⟨by nlinarith, by nlinarith, ?_⟩
    exact Int.modEq_iff_add_fac.mpr ⟨ell, rfl⟩
  · rintro ⟨ha, hb, hz⟩
    obtain ⟨ell, rfl⟩ := Int.modEq_iff_add_fac.mp hz
    apply Finset.mem_image.mpr
    exact ⟨ell, Finset.mem_Ico.mpr ⟨by nlinarith, by nlinarith⟩, rfl⟩

theorem alignment_affine_interval_residue_image (t d b A B r z : ℤ) (ht : 0 < t) :
    z ∈ ((Finset.Ico A B).filter (fun ell => Int.ModEq d r ell)).image
        (fun ell => b + t * ell) ↔
      b + t * A ≤ z ∧ z < b + t * B ∧ Int.ModEq (t * d) (b + t * r) z := by
  classical
  constructor
  · intro h
    obtain ⟨ell, he, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨he, hr⟩ := Finset.mem_filter.mp he
    obtain ⟨ha, hb⟩ := Finset.mem_Ico.mp he
    exact ⟨by nlinarith, by nlinarith,
      (alignment_nested_step_class t d b r ell ht.ne').mpr hr⟩
  · rintro ⟨ha, hb, hz⟩
    have hcoarse : Int.ModEq t b z := by
      have h₁ : Int.ModEq t b (b + t * r) := Int.modEq_iff_add_fac.mpr ⟨r, rfl⟩
      exact h₁.trans (hz.of_dvd (dvd_mul_right t d))
    obtain ⟨ell, rfl⟩ := Int.modEq_iff_add_fac.mp hcoarse
    apply Finset.mem_image.mpr
    refine ⟨ell, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by nlinarith, by nlinarith⟩, ?_⟩, rfl⟩
    exact (alignment_nested_step_class t d b r ell ht.ne').mp hz

theorem alignmentCubeBase_interval_residue_image (M t p Y A B r d z : ℤ) (ht : 0 < t) :
    z ∈ ((Finset.Ico A B).filter (fun ell => Int.ModEq d r ell)).image
        (alignmentCubeBase M t p Y) ↔
      alignmentCubeBase M t p Y A ≤ z ∧ z < alignmentCubeBase M t p Y B ∧
        Int.ModEq (t * d) (alignmentCubeBase M t p Y r) z := by
  classical
  have he (ell : ℤ) : alignmentCubeBase M t p Y ell = (t * p / M - Y) + t * ell := by
    unfold alignmentCubeBase
    ring
  rw [show alignmentCubeBase M t p Y = (fun ell => (t * p / M - Y) + t * ell) from funext he]
  exact alignment_affine_interval_residue_image t d (t * p / M - Y) A B r z ht

theorem alignmentCubeBase_interval_length (M t p Y A B : ℤ) :
    alignmentCubeBase M t p Y B - alignmentCubeBase M t p Y A = t * (B - A) := by
  unfold alignmentCubeBase
  ring

end Hindman168
