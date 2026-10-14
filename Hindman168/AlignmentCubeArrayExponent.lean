import Hindman168.AlignmentCubeCoordinates

namespace Hindman168
open scoped BigOperators

theorem alignment_remainder_quotient (M a : ℤ) (hM : M ≠ 0) :
    (a - a % M) / M = a / M := by
  have h := Int.mul_ediv_add_emod a M
  have he : a - a % M = M * (a / M) := by linarith
  rw [he, Int.mul_ediv_cancel_left _ hM]

theorem alignment_cube_residue_correction (M t p s : ℤ) (hM : M ≠ 0) :
    ((t * p) % M + t * s - (t * (p + s)) % M) / M =
      ((t * p) % M + t * s) / M := by
  have he : (t * (p + s)) % M = ((t * p) % M + t * s) % M := by
    simp only [mul_add, Int.add_emod, Int.emod_emod]
  rw [he, alignment_remainder_quotient M _ hM]

theorem alignmentIntegerArrayArgument_cube_quotient
    {κ : Type*} [Fintype κ] {n : ℕ} {i : Fin n}
    (t : Fin n → ℕ) (M : ℕ) (hM : 0 < M)
    (ρ : AlignmentAddingPair n i → ℕ) (Δ : AlignmentAddingPair n i → ℤ)
    (T : Finset (Fin n)) (p Y ell : ℤ) (inc weight : κ → ℤ)
    (v u : AlignmentAddingPair n i → ℤ) :
    alignmentIntegerArrayArgument t M ρ Δ T
        (p + (M : ℤ) * (ell + ∑ j, weight j * inc j)) v u / (M : ℤ) =
      alignmentCubeVertex M (alignmentNaturalBlockProduct t T) p Y ell inc weight + Y +
        (alignmentPivotArrayResidue t T M p 0 +
          (alignmentNaturalBlockProduct t T : ℤ) * alignmentIntegerSlotShift ρ v -
          alignmentPivotArrayResidue t T M p (alignmentIntegerSlotShift ρ v)) / (M : ℤ) +
        alignmentIntegerArrayProgression Δ T u := by
  have hm : (M : ℤ) ≠ 0 := by exact_mod_cast hM.ne'
  unfold alignmentIntegerArrayArgument alignmentPivotArrayResidue
  simp only [add_zero]
  rw [alignment_cube_residue_correction _ _ _ _ hm]
  exact alignmentCubeVertex_exponent _ _ _ _ _ _ _ hm inc weight

theorem alignment_cube_residue_correction_exact (M t p s : ℤ) (hM : M ≠ 0) :
    M * (((t * p) % M + t * s - (t * (p + s)) % M) / M) =
      (t * p) % M + t * s - (t * (p + s)) % M := by
  rw [alignment_cube_residue_correction M t p s hM]
  have he : (t * (p + s)) % M = ((t * p) % M + t * s) % M := by
    simp only [mul_add, Int.add_emod, Int.emod_emod]
  rw [he]
  have h := Int.mul_ediv_add_emod ((t * p) % M + t * s) M
  linarith

theorem alignmentIntegerArrayArgument_canonical_cube_quotient
    {κ : Type*} [Fintype κ] {n : ℕ} {i : Fin n}
    (t : Fin n → ℕ) (q₀ w M : ℕ) (hM : 0 < M)
    (T : Finset (Fin n)) (p Y ell : ℤ) (inc weight : κ → ℤ)
    (v u : AlignmentAddingPair n i → ℤ) :
    letI := alignmentAddingPairFintype n i
    let ρ := fun e => alignmentPairResidue q₀ w M e t
    let Δ := fun e => alignmentPairProgression q₀ w M e t
    alignmentIntegerArrayArgument t M ρ Δ T
        (p + (M : ℤ) * (ell + ∑ j, weight j * inc j)) v u / (M : ℤ) =
      alignmentCubeVertex M (alignmentNaturalBlockProduct t T) p Y ell inc weight + Y +
        (alignmentPivotArrayResidue t T M p 0 +
          (alignmentNaturalBlockProduct t T : ℤ) * alignmentIntegerSlotShift ρ v -
          alignmentPivotArrayResidue t T M p (alignmentIntegerSlotShift ρ v)) / (M : ℤ) +
        ∑ e, if e.targetTail = T then u e *
          (((alignmentIntegerNumerator q₀ w e t : ℤ) -
            (alignmentNaturalBlockProduct t T : ℤ) * ρ e) / (M : ℤ)) else 0 := by
  letI := alignmentAddingPairFintype n i
  dsimp only
  rw [alignmentIntegerArrayArgument_cube_quotient t M hM]
  congr 1
  unfold alignmentIntegerArrayProgression
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : e.targetTail = T
  · simp only [alignmentPairProgression, alignmentProgressionShift, he]
  · simp only [if_neg he]

theorem alignmentCubeBase_frozen_residue (M t p r : ℤ) (h : Int.ModEq M p r) :
    (t * p) % M = (t * r) % M := h.mul_left t

end Hindman168
