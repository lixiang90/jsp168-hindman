import Hindman168.WeightedShearPolynomial
import Mathlib.Data.Real.Basic

/-!
The polynomial growth estimate in the weighted-box part of Lemma 7.7.
The coefficient constant is explicit, and every bound is for the actual
polynomial evaluated on the actual anisotropic box.
-/

namespace Hindman168
open scoped BigOperators
open MvPolynomial

variable {σ : Type*}

/-- The expanding anisotropic box from equation (7.19). -/
def weightedShearBox (w : σ → ℕ) (E : ℝ) : Set (σ → ℝ) :=
  {x | ∀ i, |x i| ≤ E ^ w i}

/-- Sum of the absolute values of the actual polynomial coefficients. -/
noncomputable def weightedShearCoefficientMass (p : MvPolynomial σ ℝ) : ℝ :=
  ∑ a ∈ p.support, |p.coeff a|

theorem weightedShearCoefficientMass_nonneg (p : MvPolynomial σ ℝ) :
    0 ≤ weightedShearCoefficientMass p :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- The basic monomial estimate respects the original coordinate weights. -/
theorem weightedShear_monomial_bound (w : σ → ℕ) {E : ℝ} (_hE : 0 ≤ E)
    {x : σ → ℝ} (hx : x ∈ weightedShearBox w E)
    (a : σ →₀ ℕ) (r : ℝ) :
    |MvPolynomial.eval x (monomial a r)| ≤ |r| * E ^ Finsupp.weight w a := by
  classical
  have hprod : ∏ i ∈ a.support, |x i| ^ a i ≤
      ∏ i ∈ a.support, (E ^ w i) ^ a i := by
    apply Finset.prod_le_prod
    · intro i _
      positivity
    · intro i _
      exact pow_le_pow_left₀ (abs_nonneg _) (hx i) _
  have hpow : (∏ i ∈ a.support, (E ^ w i) ^ a i) = E ^ Finsupp.weight w a := by
    simp only [← pow_mul, ← Finset.prod_pow_eq_pow_sum,
      Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, Nat.cast_id, mul_comm]
  calc
    |MvPolynomial.eval x (monomial a r)| = |r| * ∏ i ∈ a.support, |x i| ^ a i := by
      simp only [MvPolynomial.eval_monomial, Finsupp.prod, abs_mul,
        Finset.abs_prod, abs_pow]
    _ ≤ |r| * ∏ i ∈ a.support, (E ^ w i) ^ a i :=
      mul_le_mul_of_nonneg_left hprod (abs_nonneg _)
    _ = |r| * E ^ Finsupp.weight w a := by rw [hpow]

/-- A degree-`d` polynomial grows by at most its coefficient mass times `E^d`. -/
theorem weightedShear_polynomial_bound (w : σ → ℕ) {E : ℝ} (hE : 1 ≤ E)
    {x : σ → ℝ} (hx : x ∈ weightedShearBox w E)
    (p : MvPolynomial σ ℝ) (d : ℕ) (hp : p ∈ weightedShearDegreeLE w d) :
    |MvPolynomial.eval x p| ≤ weightedShearCoefficientMass p * E ^ d := by
  classical
  have hmono : ∀ a ∈ p.support,
      |MvPolynomial.eval x (monomial a (p.coeff a))| ≤ |p.coeff a| * E ^ d := by
    intro a ha
    apply (weightedShear_monomial_bound w (by linarith) hx a (p.coeff a)).trans
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply pow_le_pow_right₀ hE
    exact_mod_cast hp a ha
  calc
    |MvPolynomial.eval x p| =
        |∑ a ∈ p.support, MvPolynomial.eval x (monomial a (p.coeff a))| := by
      conv_lhs => rw [p.as_sum]
      simp only [map_sum]
    _ ≤ ∑ a ∈ p.support, |MvPolynomial.eval x (monomial a (p.coeff a))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ p.support, |p.coeff a| * E ^ d := Finset.sum_le_sum hmono
    _ = weightedShearCoefficientMass p * E ^ d := by
      rw [← Finset.sum_mul]
      rfl

/-- Actual displacement in a weight-`j` coordinate is `O(E^(j-1))`. -/
theorem weightedShear_displacement_bound (w : σ → ℕ)
    (p : σ → MvPolynomial σ ℝ)
    (hp : ∀ i, p i ∈ weightedShearDegreeLE w ((w i : ℤ)-1))
    (hw : ∀ i, 0 < w i) {E : ℝ} (hE : 1 ≤ E)
    {x : σ → ℝ} (hx : x ∈ weightedShearBox w E) (i : σ) :
    |MvPolynomial.eval x (p i)| ≤ weightedShearCoefficientMass (p i) * E ^ (w i-1) := by
  apply weightedShear_polynomial_bound w hE hx (p i) (w i-1)
  convert hp i using 1
  congr 1
  exact Int.ofNat_sub (hw i)

/-- A single fixed coefficient bound controls every coordinate of a finite-dimensional shear. -/
theorem weightedShear_image_box_bound [Fintype σ] (w : σ → ℕ)
    (p : σ → MvPolynomial σ ℝ)
    (hp : ∀ i, p i ∈ weightedShearDegreeLE w ((w i : ℤ)-1))
    (hw : ∀ i, 0 < w i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ E : ℝ, 1 ≤ E → ∀ x ∈ weightedShearBox w E, ∀ i,
      |x i+MvPolynomial.eval x (p i)| ≤ E ^ w i+C * E ^ (w i-1) := by
  classical
  let C : ℝ := ∑ i, weightedShearCoefficientMass (p i)
  refine ⟨C, Finset.sum_nonneg (fun _ _ => weightedShearCoefficientMass_nonneg _), ?_⟩
  intro E hE x hx i
  have hC : weightedShearCoefficientMass (p i) ≤ C :=
    Finset.single_le_sum (fun j _ => weightedShearCoefficientMass_nonneg _) (Finset.mem_univ i)
  calc
    |x i+MvPolynomial.eval x (p i)| ≤ |x i|+|MvPolynomial.eval x (p i)| := abs_add_le _ _
    _ ≤ E ^ w i+weightedShearCoefficientMass (p i)*E ^ (w i-1) :=
      add_le_add (hx i) (weightedShear_displacement_bound w p hp hw hE hx i)
    _ ≤ E ^ w i+C*E ^ (w i-1) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hC
        (show 0 ≤ E ^ (w i-1) by positivity))

end Hindman168
