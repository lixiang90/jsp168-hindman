import Hindman168.PolynomialSmallValueConstantRecovery
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Order.Interval.Finset.Nat

/-! ACTUAL nonlinear scalar polynomial is split by genuine nearest integers.
R has one true denominator and an actual integer polynomial numerator;
E has true original N^-j real coefficient bounds. Numerators may be unbounded. -/
namespace Hindman168
open Polynomial
open scoped BigOperators Classical

noncomputable def scalarNonlinearIntegerNumerator (D : ℕ) (z : ℕ → ℤ) : ℤ[X] :=
  ∑ j ∈ Finset.Icc 2 D, monomial j (z j)

noncomputable def scalarNonlinearRationalPart (D M : ℕ) (z : ℕ → ℤ) : ℝ[X] :=
  ∑ j ∈ Finset.Icc 2 D, monomial j ((z j : ℝ)/(M : ℝ))

theorem scalar_nonlinear_integer_numerator_coeff (D : ℕ) (z : ℕ → ℤ) (j : ℕ) :
    (scalarNonlinearIntegerNumerator D z).coeff j = if j ∈ Finset.Icc 2 D then z j else 0 := by
  simp only [scalarNonlinearIntegerNumerator,finsetSum_coeff,coeff_monomial,Finset.sum_ite_eq']

theorem scalar_nonlinear_rational_part_coeff (D M : ℕ) (z : ℕ → ℤ) (j : ℕ) :
    (scalarNonlinearRationalPart D M z).coeff j = if j ∈ Finset.Icc 2 D then (z j : ℝ)/(M : ℝ) else 0 := by
  simp only [scalarNonlinearRationalPart,finsetSum_coeff,coeff_monomial,Finset.sum_ite_eq']

theorem scalar_nonlinear_rational_part_degree (D M : ℕ) (z : ℕ → ℤ) :
    (scalarNonlinearRationalPart D M z).natDegree ≤ D := by
  apply natDegree_sum_le_of_forall_le
  intro j hj
  exact (natDegree_monomial_le _).trans (Finset.mem_Icc.mp hj).2

theorem scalar_nonlinear_rational_part_integer_map (D M : ℕ) (z : ℕ → ℤ) :
    scalarNonlinearRationalPart D M z =
      C ((M : ℝ)⁻¹)*(scalarNonlinearIntegerNumerator D z).map (Int.castRingHom ℝ) := by
  ext j
  rw [coeff_C_mul,coeff_map,scalar_nonlinear_rational_part_coeff,scalar_nonlinear_integer_numerator_coeff]
  split_ifs
  · change (z j : ℝ)/(M : ℝ) = (M : ℝ)⁻¹*(z j : ℝ)
    ring
  · simp only [map_zero,mul_zero]

theorem scalar_nonlinear_rational_part_integer_eval (D M : ℕ) (z : ℕ → ℤ) (n : ℤ) :
    (scalarNonlinearRationalPart D M z).eval (n : ℝ) =
      (((scalarNonlinearIntegerNumerator D z).eval n : ℤ) : ℝ)/(M : ℝ) := by
  rw [scalar_nonlinear_rational_part_integer_map,eval_mul,eval_C,eval_map]
  have he := eval₂_at_apply (p := scalarNonlinearIntegerNumerator D z) (Int.castRingHom ℝ) n
  have he' : (scalarNonlinearIntegerNumerator D z).eval₂ (Int.castRingHom ℝ) (n : ℝ) =
      (((scalarNonlinearIntegerNumerator D z).eval n : ℤ) : ℝ) := by
    simpa only [Int.coe_castRingHom] using he
  rw [he']
  ring

theorem scalar_nonlinear_small_rational_split (Q : ℝ[X]) (D M N : ℕ) (B : ℝ)
    (hQ : Q.natDegree ≤ D) (hQ0 : Q.coeff 0=0) (hQ1 : Q.coeff 1=0) (hM : 0 < M)
    (hBounds : ∀ j : ℕ, 2 ≤ j → j ≤ D → (N : ℝ)^j*‖(((M : ℝ)*Q.coeff j : ℝ) : UnitAddCircle)‖ ≤ B) :
    ∃ (z : ℕ → ℤ) (E : ℝ[X]), Q=E+scalarNonlinearRationalPart D M z ∧ E.natDegree ≤ D ∧
      E.coeff 0=0 ∧ E.coeff 1=0 ∧ ∀ j : ℕ, 2 ≤ j → j ≤ D →
        (M : ℝ)*(N : ℝ)^j*|E.coeff j| ≤ B := by
  let z (j : ℕ) := round ((M : ℝ)*Q.coeff j)
  let R := scalarNonlinearRationalPart D M z
  let E := Q-R
  have hn : (0 : ℝ) < M := by exact_mod_cast hM
  have hE : E.natDegree ≤ D := (natDegree_sub_le _ _).trans
    (max_le hQ (scalar_nonlinear_rational_part_degree D M z))
  have hR0 : R.coeff 0=0 := by rw [scalar_nonlinear_rational_part_coeff]; simp
  have hR1 : R.coeff 1=0 := by rw [scalar_nonlinear_rational_part_coeff]; simp
  refine ⟨z,E,by dsimp only [E]; ring,hE,?_,?_,?_⟩
  · dsimp only [E]
    rw [coeff_sub,hQ0,hR0,sub_self]
  · dsimp only [E]
    rw [coeff_sub,hQ1,hR1,sub_self]
  · intro j hj hjD
    have hmem : j ∈ Finset.Icc 2 D := Finset.mem_Icc.mpr ⟨hj,hjD⟩
    have he : (M : ℝ)*E.coeff j=(M : ℝ)*Q.coeff j-(z j : ℝ) := by
      dsimp only [E,R]
      rw [coeff_sub,scalar_nonlinear_rational_part_coeff,if_pos hmem]
      field_simp
    have hnorm : |(M : ℝ)*E.coeff j|=‖(((M : ℝ)*Q.coeff j : ℝ) : UnitAddCircle)‖ := by
      rw [he]
      exact UnitAddCircle.norm_eq.symm
    calc
      _ = (N : ℝ)^j*|(M : ℝ)*E.coeff j| := by rw [abs_mul,abs_of_pos hn]; ring
      _ = _ := congrArg (fun t : ℝ => (N : ℝ)^j*t) hnorm
      _ ≤ _ := hBounds j hj hjD

end Hindman168
