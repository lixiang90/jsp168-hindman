import Hindman168.UnitriangularExponentialInverse

/-! Exponential coordinates identify the genuine matrix support filtration
exactly. The reverse direction is proved by successive support improvement,
not by an assumed formula for logarithms or equality of central series. -/

namespace Hindman168
open Matrix

variable {n : ℕ} {R : Type*} [CommRing R] [Algebra ℚ R]

 theorem matrixFiniteExp_nonlinear_depth {k : ℕ} {A : Matrix (Fin n) (Fin n) R}
    (hA : MatrixDepth 1 A) (hk : MatrixDepth k A) :
    MatrixDepth (k + 1) (matrixFiniteExp A - 1 - A) := by
  have hd : MatrixDepth k (A - 0) := by simpa only [sub_zero] using hk
  simpa only [matrixFiniteExp_zero, sub_zero] using
    matrixFiniteExp_difference_depth hA (matrixDepth_zero 1) hd

 theorem matrixDepth_exp_sub_one {k : ℕ} {A : Matrix (Fin n) (Fin n) R}
    (hA : MatrixDepth 1 A) (hk : MatrixDepth k A) :
    MatrixDepth k (matrixFiniteExp A - 1) := by
  have h := matrixFiniteExp_nonlinear_depth hA hk
  have heq : A + (matrixFiniteExp A - 1 - A) = matrixFiniteExp A - 1 := by abel
  exact heq ▸ hk.add (h.antitone (by omega))

 theorem matrixDepth_of_exp_sub_one {k : ℕ} {A : Matrix (Fin n) (Fin n) R}
    (hA : MatrixDepth 1 A) (hk : MatrixDepth k (matrixFiniteExp A - 1)) :
    MatrixDepth k A := by
  have hd : ∀ r, r ≤ k → MatrixDepth r A := by
    intro r
    induction r with
    | zero => intro _; exact hA.antitone (by omega)
    | succ r ih =>
      intro hr
      have hp := ih (by omega)
      have hrem := matrixFiniteExp_nonlinear_depth hA hp
      have heq : (matrixFiniteExp A - 1) - (matrixFiniteExp A - 1 - A) = A := by abel
      exact heq ▸ (hk.antitone hr).sub hrem
  exact hd k le_rfl

 theorem matrixDepth_exp_sub_one_iff {k : ℕ} {A : Matrix (Fin n) (Fin n) R}
    (hA : MatrixDepth 1 A) :
    MatrixDepth k (matrixFiniteExp A - 1) ↔ MatrixDepth k A :=
  ⟨matrixDepth_of_exp_sub_one hA, matrixDepth_exp_sub_one hA⟩

 theorem unitriangularExponential_depth_iff (A : StrictUpperTriangular n R) (k : ℕ) :
    UnitriangularDepth k (unitriangularExponential A) ↔ MatrixDepth k A.val := by
  rw [unitriangularDepth_iff_delta]
  exact matrixDepth_exp_sub_one_iff A.property

 theorem unitriangularLogarithm_depth_iff (g : Unitriangular n R) (k : ℕ) :
    MatrixDepth k (unitriangularLogarithm g).val ↔ UnitriangularDepth k g := by
  have h := unitriangularExponential_depth_iff (unitriangularLogarithm g) k
  rw [unitriangularExponential_logarithm] at h
  exact h.symm

end Hindman168
