import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Real.Basic

/-! Exact increment-support decomposition, including the empty face and zero
cube dimension. The base variable is `none`; increments are `some k`. -/
namespace Hindman168
open scoped BigOperators
open MvPolynomial

def cubeIncrementSupport {d : ℕ} (m : Option (Fin d) →₀ ℕ) : Finset (Fin d) :=
  Finset.univ.filter (fun k => m (some k) ≠ 0)

noncomputable def cubePolynomialFacePart {d : ℕ}
    (A : Finset (Fin d)) (p : MvPolynomial (Option (Fin d)) ℝ) :
    MvPolynomial (Option (Fin d)) ℝ :=
  ⟨(AddMonoidAlgebra.coeff p).filter (fun m => cubeIncrementSupport m = A)⟩

theorem cube_polynomial_face_part_coefficient {d : ℕ}
    (A : Finset (Fin d)) (p : MvPolynomial (Option (Fin d)) ℝ)
    (m : Option (Fin d) →₀ ℕ) :
    coeff m (cubePolynomialFacePart A p) =
      if cubeIncrementSupport m = A then coeff m p else 0 := rfl

theorem cube_polynomial_face_part_support {d : ℕ}
    (A : Finset (Fin d)) (p : MvPolynomial (Option (Fin d)) ℝ) :
    (cubePolynomialFacePart A p).support =
      p.support.filter (fun m => cubeIncrementSupport m = A) := rfl

theorem cube_polynomial_face_parts_sum {d : ℕ}
    (p : MvPolynomial (Option (Fin d)) ℝ) :
    ∑ A : Finset (Fin d), cubePolynomialFacePart A p = p := by
  ext m
  simp only [coeff_sum, cube_polynomial_face_part_coefficient]
  simp

theorem cube_polynomial_face_part_degree {d : ℕ}
    (A : Finset (Fin d)) (p : MvPolynomial (Option (Fin d)) ℝ) :
    (cubePolynomialFacePart A p).totalDegree ≤ p.totalDegree := by
  apply totalDegree_le_of_support_subset
  rw [cube_polynomial_face_part_support]
  exact Finset.filter_subset _ _

theorem cube_increment_support_card_le {d : ℕ} (m : Option (Fin d) →₀ ℕ) :
    (cubeIncrementSupport m).card ≤ m.sum (fun _ n => n) := by
  have h : (cubeIncrementSupport m).card ≤ ∑ k : Fin d, m (some k) := by
    calc
      _ = ∑ k ∈ cubeIncrementSupport m, 1 := by simp
      _ ≤ ∑ k ∈ cubeIncrementSupport m, m (some k) := by
        apply Finset.sum_le_sum
        intro k hk
        have := (Finset.mem_filter.mp hk).2
        omega
      _ ≤ ∑ k : Fin d, m (some k) := Finset.sum_le_univ_sum_of_nonneg (by intros; omega)
  rw [Finsupp.sum_fintype _ _ (by simp)]
  rw [Fintype.sum_option]
  omega

theorem cube_polynomial_face_part_eq_zero_of_degree {d : ℕ}
    (A : Finset (Fin d)) (p : MvPolynomial (Option (Fin d)) ℝ)
    (h : p.totalDegree < A.card) : cubePolynomialFacePart A p = 0 := by
  ext m
  rw [cube_polynomial_face_part_coefficient, coeff_zero]
  split_ifs with hm
  · by_contra hn
    have hd := le_totalDegree (mem_support_iff.mpr hn)
    have hc := cube_increment_support_card_le m
    rw [hm] at hc
    omega
  · rfl

end Hindman168
