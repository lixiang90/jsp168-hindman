import Hindman168.AlignmentFrozenPieceReading

namespace Hindman168
open scoped BigOperators

def alignmentCubeBase (M t p Y ell : ℤ) : ℤ := t * p / M + t * ell - Y

def alignmentCubeVertex {κ : Type*} [Fintype κ]
    (M t p Y ell : ℤ) (inc weight : κ → ℤ) : ℤ :=
  alignmentCubeBase M t p Y ell + ∑ j, weight j * (t * inc j)

theorem alignmentCubeBase_reconstruction (M t p Y ell : ℤ) :
    M * (alignmentCubeBase M t p Y ell + Y) + (t * p) % M =
      t * (p + M * ell) := by
  have h := Int.mul_ediv_add_emod (t * p) M
  unfold alignmentCubeBase
  linear_combination h

theorem alignmentCubeBase_exact_quotient (M t p Y ell : ℤ) (hM : M ≠ 0) :
    alignmentCubeBase M t p Y ell =
      (t * (p + M * ell) - (t * p) % M) / M - Y := by
  have h := alignmentCubeBase_reconstruction M t p Y ell
  have he : t * (p + M * ell) - (t * p) % M =
      M * (alignmentCubeBase M t p Y ell + Y) := by linarith
  rw [he, Int.mul_ediv_cancel_left _ hM]
  ring

theorem alignmentCubeVertex_affine {κ : Type*} [Fintype κ]
    (M t p Y ell : ℤ) (inc weight : κ → ℤ) :
    alignmentCubeVertex M t p Y ell inc weight =
      alignmentCubeBase M t p Y (ell + ∑ j, weight j * inc j) := by
  unfold alignmentCubeVertex alignmentCubeBase
  rw [mul_add, Finset.mul_sum]
  have hs : (∑ j, weight j * (t * inc j)) = ∑ j, t * (weight j * inc j) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs]
  ring

theorem alignmentCubeVertex_exponent {κ : Type*} [Fintype κ]
    (M t p Y ell s D : ℤ) (hM : M ≠ 0) (inc weight : κ → ℤ) :
    (t * (p + M * (ell + ∑ j, weight j * inc j) + s) + M * D) / M =
      alignmentCubeVertex M t p Y ell inc weight + Y +
        ((t * p) % M + t * s) / M + D := by
  have hr := alignmentCubeBase_reconstruction M t p Y (ell + ∑ j, weight j * inc j)
  rw [← alignmentCubeVertex_affine M t p Y ell inc weight] at hr
  have he : t * (p + M * (ell + ∑ j, weight j * inc j) + s) + M * D =
      ((t * p) % M + t * s) + M *
        (alignmentCubeVertex M t p Y ell inc weight + Y + D) := by
    linear_combination -hr
  rw [he, Int.add_mul_ediv_left _ _ hM]
  ring

theorem alignmentCubeBase_origin_dvd (M t p Y ell w : ℤ) (hw : w ∣ t) :
    w ∣ M * (alignmentCubeBase M t p Y ell + Y) + (t * p) % M := by
  rw [alignmentCubeBase_reconstruction]
  exact dvd_mul_of_dvd_left hw _

theorem alignmentCubeBase_residue (M t p Y ell a d : ℤ)
    (h : Int.ModEq d ell a) :
    Int.ModEq (d * t) (alignmentCubeBase M t p Y ell)
      (alignmentCubeBase M t p Y a) := by
  have hh := h.mul_right' (c := t)
  simpa only [alignmentCubeBase, mul_comm t ell, mul_comm t a, sub_eq_add_neg] using
    (hh.add_left (t * p / M)).add_right (-Y)

end Hindman168
