import Hindman168.WeightedShearPicardFiltration
import Hindman168.RoughVectorMvCoordinates
import Hindman168.RoughVectorMvConstant
import Hindman168.RoughVectorMvLinearMap

/-! From actual vector-filtration membership to the coordinate-degree inequality
in (7.12).  The extra filtration unit forces every too-high-degree scalar term
to vanish after projection to a weight-`j` coordinate. -/

namespace Hindman168
open MvPolynomial Module
variable {σ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A linear functional killing the next filtration level detects only strict lower-degree terms. -/
theorem weightedShearVector_projection (w : σ → ℕ)
    (F : ℕ → Submodule ℝ E) (hF : Antitone F)
    (ell : E →ₗ[ℝ] ℝ) (j : ℕ)
    (hell : ∀ v ∈ F (j+1), ell v = 0)
    {p : RoughVectorMvPolynomial σ E} (hp : AffineShearWeightedVector w F p 1) :
    roughVectorMvProjection ell p ∈ weightedShearDegreeLE w ((j : ℤ)-1) := by
  induction p with
  | nil => exact (weightedShearDegreeLE w ((j : ℤ)-1)).zero_mem
  | cons a p ih =>
      change a.1 * C (ell a.2)+roughVectorMvProjection ell p ∈ _
      apply Submodule.add_mem
      · by_cases hd : a.1.weightedTotalDegree w < j
        · have hterm := weightedShearDegreeLE_mul w (weightedShearDegreeLE_self w a.1)
            (weightedShearDegreeLE_C w (ell a.2))
          exact weightedShearDegreeLE_mono w (by omega) hterm
        · have hz : ell a.2 = 0 := hell _
            (hF (by omega) (hp a List.mem_cons_self))
          simp only [hz, map_zero, mul_zero, Submodule.zero_mem]
      · exact ih (fun b hb => hp b (List.mem_cons_of_mem a hb))

/-- Actual linear maps preserving a filtration preserve coordinate-weighted vector polynomials. -/
theorem weightedShearVector_linearMap {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] (w : σ → ℕ)
    (F : ℕ → Submodule ℝ E) (F' : ℕ → Submodule ℝ E')
    (L : E →ₗ[ℝ] E') (l : ℕ) (hL : ∀ d v, v ∈ F d → L v ∈ F' (d+l))
    {p : RoughVectorMvPolynomial σ E} {k : ℕ}
    (hp : AffineShearWeightedVector w F p k) :
    AffineShearWeightedVector w F' (roughVectorMvLinearMap L p) (k+l) := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  simpa only [Nat.add_assoc] using hL _ _ (hp b hb)

/-- Constants have no polynomial weight; their filtration level is retained exactly. -/
theorem weightedShearVector_constant (w : σ → ℕ)
    (F : ℕ → Submodule ℝ E) {v : E} {k : ℕ} (hv : v ∈ F k) :
    AffineShearWeightedVector w F (roughVectorMvConstant v) k := by
  classical
  intro a ha
  have ha' := List.mem_singleton.mp ha
  subst a
  simpa [MvPolynomial.weightedTotalDegree] using hv

/-- The identity coordinate polynomial has its original, potentially nonuniform weights. -/
theorem weightedShearVector_basis {n : ℕ} (w : Fin n → ℕ)
    (F : ℕ → Submodule ℝ E) (b : Basis (Fin n) ℝ E)
    (hb : ∀ i, b i ∈ F (w i)) :
    AffineShearWeightedVector w F (roughVectorMvFromBasis b (fun i => X i)) 0 := by
  classical
  intro a ha
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
  simpa [MvPolynomial.weightedTotalDegree, MvPolynomial.support_X, Finsupp.weight_single] using hb i

/-- Arbitrary prescribed polynomial coordinates evaluate to the actual basis-coordinate function. -/
theorem weightedShearVector_basis_eval {n : ℕ} (b : Basis (Fin n) ℝ E) (x : Fin n → ℝ) :
    roughVectorMvEval (roughVectorMvFromBasis b (fun i => X i)) x = b.equivFun.symm x := by
  rw [roughVectorMvFromBasis_eval]
  simp only [MvPolynomial.eval_X]
  exact (b.equivFun_symm_apply x).symm

end Hindman168
