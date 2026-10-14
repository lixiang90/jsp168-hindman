import Hindman168.UnitriangularExponentialDepth

/-! Exact congruence of the genuine exponential/logarithm with the matrix
support filtration. Multiplication by exp(B) is addition of B on its first
nonzero support layer, with all earlier layers fixed. These proved laws
provide the triangular steps needed for noncommutative coordinate reduction. -/

namespace Hindman168
open Matrix

variable {n : ℕ} {R : Type*} [CommRing R] [Algebra ℚ R]

 theorem matrixDepth_exp_difference_iff {k : ℕ} {A B : Matrix (Fin n) (Fin n) R}
    (hA : MatrixDepth 1 A) (hB : MatrixDepth 1 B) :
    MatrixDepth k (matrixFiniteExp A - matrixFiniteExp B) ↔ MatrixDepth k (A - B) := by
  constructor
  · intro he
    have hstep : ∀ r, r ≤ k → MatrixDepth r (A - B) := by
      intro r
      induction r with
      | zero => intro _; exact (hA.sub hB).antitone (by omega)
      | succ r ih =>
        intro hr
        have hp := ih (by omega)
        have hrem := matrixFiniteExp_difference_depth hA hB hp
        have heq : (matrixFiniteExp A - matrixFiniteExp B) -
            (matrixFiniteExp A - matrixFiniteExp B - (A - B)) = A - B := by abel
        exact heq ▸ (he.antitone hr).sub hrem
    exact hstep k le_rfl
  · intro hd
    have hn := matrixFiniteExp_difference_depth hA hB hd
    have heq : (matrixFiniteExp A - matrixFiniteExp B - (A - B)) + (A - B) =
        matrixFiniteExp A - matrixFiniteExp B := by abel
    exact heq ▸ (hn.antitone (by omega)).add hd

 theorem unitriangular_bch_right_leading_depth (A B : StrictUpperTriangular n R)
    {k : ℕ} (hB : MatrixDepth k B.val) :
    MatrixDepth (k + 1)
      ((unitriangularLogarithm (unitriangularExponential A * unitriangularExponential B)).val -
        A.val - B.val) := by
  have hs : MatrixDepth k ((A.val + B.val) - A.val) := by
    simpa only [add_sub_cancel_left] using hB
  have hsum := matrixFiniteExp_difference_depth (A.property.add B.property) A.property hs
  have hprod : MatrixDepth (k + 1)
      (matrixFiniteExp A.val * matrixFiniteExp B.val - matrixFiniteExp A.val - B.val) := by
    have hEA := matrixDepth_exp_sub_one A.property A.property
    have hEB := matrixDepth_exp_sub_one B.property hB
    have hm : MatrixDepth (k + 1)
        ((matrixFiniteExp A.val - 1) * (matrixFiniteExp B.val - 1)) := by
      simpa only [Nat.add_comm 1 k] using hEA.mul hEB
    have hr := matrixFiniteExp_nonlinear_depth B.property hB
    have heq : matrixFiniteExp A.val * matrixFiniteExp B.val - matrixFiniteExp A.val - B.val =
        (matrixFiniteExp A.val - 1) * (matrixFiniteExp B.val - 1) +
          (matrixFiniteExp B.val - 1 - B.val) := by noncomm_ring
    rw [heq]
    exact hm.add hr
  have he : MatrixDepth (k + 1)
      (matrixFiniteExp A.val * matrixFiniteExp B.val - matrixFiniteExp (A.val + B.val)) := by
    have heq : matrixFiniteExp A.val * matrixFiniteExp B.val - matrixFiniteExp (A.val + B.val) =
        (matrixFiniteExp A.val * matrixFiniteExp B.val - matrixFiniteExp A.val - B.val) -
          (matrixFiniteExp (A.val + B.val) - matrixFiniteExp A.val - ((A.val + B.val) - A.val)) := by abel
    rw [heq]
    exact hprod.sub hsum
  let Z := unitriangularLogarithm (unitriangularExponential A * unitriangularExponential B)
  have hZ : matrixFiniteExp Z.val = matrixFiniteExp A.val * matrixFiniteExp B.val :=
    matrixFiniteExp_logMatrix _
  have hc : MatrixDepth (k + 1) (Z.val - (A.val + B.val)) := by
    apply (matrixDepth_exp_difference_iff Z.property (A.property.add B.property)).mp
    rw [hZ]
    exact he
  simpa only [sub_add_eq_sub_sub] using hc

 theorem unitriangular_log_right_exponential_leading_depth (g : Unitriangular n R)
    (B : StrictUpperTriangular n R) {k : ℕ} (hB : MatrixDepth k B.val) :
    MatrixDepth (k + 1)
      ((unitriangularLogarithm (g * unitriangularExponential B)).val -
        (unitriangularLogarithm g).val - B.val) := by
  have h := unitriangular_bch_right_leading_depth (unitriangularLogarithm g) B hB
  simpa only [unitriangularExponential_logarithm] using h

 theorem unitriangular_log_right_exponential_layer (g : Unitriangular n R)
    (B : StrictUpperTriangular n R) {k : ℕ} (hB : MatrixDepth k B.val)
    (i j : Fin n) (hij : j.val < i.val + k + 1) :
    (unitriangularLogarithm (g * unitriangularExponential B)).val i j =
      (unitriangularLogarithm g).val i j + B.val i j := by
  have h := unitriangular_log_right_exponential_leading_depth g B hB i j hij
  change (unitriangularLogarithm (g * unitriangularExponential B)).val i j -
    (unitriangularLogarithm g).val i j - B.val i j = 0 at h
  exact (sub_eq_iff_eq_add.mp (sub_eq_zero.mp h)).trans (add_comm _ _)

 theorem unitriangular_log_right_exponential_earlier (g : Unitriangular n R)
    (B : StrictUpperTriangular n R) {k : ℕ} (hB : MatrixDepth k B.val)
    (i j : Fin n) (hij : j.val < i.val + k) :
    (unitriangularLogarithm (g * unitriangularExponential B)).val i j =
      (unitriangularLogarithm g).val i j := by
  rw [unitriangular_log_right_exponential_layer g B hB i j (by omega), hB i j hij, add_zero]

end Hindman168
