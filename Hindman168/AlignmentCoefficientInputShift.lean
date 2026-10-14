import Hindman168.AlignmentLieArrayEvaluation
import Mathlib.Algebra.MvPolynomial.Degrees

namespace Hindman168
open scoped BigOperators TensorProduct
open MvPolynomial

variable {σ R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

noncomputable def alignmentCoefficientInputShift (v : σ → R) :
    MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval (fun j => X j + C (v j))

theorem alignmentCoefficientInputShift_degree [Nontrivial R] (v : σ → R)
    (p : MvPolynomial σ R) :
    (alignmentCoefficientInputShift v p).totalDegree ≤ p.totalDegree := by
  classical
  change (eval₂Hom C (fun j => X j + C (v j)) p).totalDegree ≤ p.totalDegree
  conv_lhs => arg 1; rw [p.as_sum]
  rw [map_sum]
  apply totalDegree_finsetSum_le
  intro d hd
  rw [eval₂Hom_monomial]
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add]
  apply (totalDegree_finsetProd _ _).trans
  calc
    ∑ j ∈ d.support, ((X j + C (v j)) ^ d j).totalDegree ≤
        ∑ j ∈ d.support, d j := by
      apply Finset.sum_le_sum
      intro j _
      apply (totalDegree_pow _ _).trans
      have h : (X j + C (v j) : MvPolynomial σ R).totalDegree ≤ 1 :=
        (totalDegree_add _ _).trans (by rw [totalDegree_X, totalDegree_C]; exact le_rfl)
      simpa only [mul_one] using Nat.mul_le_mul_left (d j) h
    _ ≤ p.totalDegree := le_totalDegree hd

theorem alignmentCoefficientInputShift_eval (v u : σ → R)
    (p : MvPolynomial σ R) :
    aeval u (alignmentCoefficientInputShift v p) = aeval (u + v) p := by
  have h : (aeval u).comp (alignmentCoefficientInputShift v) = aeval (u + v) := by
    ext j
    simp [alignmentCoefficientInputShift, Pi.add_apply]
  exact DFunLike.congr_fun h p

theorem alignmentCoefficientInputShift_add (v w : σ → R) :
    (alignmentCoefficientInputShift v).comp (alignmentCoefficientInputShift w) =
      alignmentCoefficientInputShift (v + w) := by
  ext j
  simp [alignmentCoefficientInputShift, Pi.add_apply, map_add, add_assoc]

theorem alignmentCoefficientInputShift_zero :
    alignmentCoefficientInputShift (0 : σ → R) = AlgHom.id R _ := by
  ext j
  simp [alignmentCoefficientInputShift]

theorem alignmentLiePolynomialArrays_polynomial_tmul (p : MvPolynomial σ R)
    (x : L) (hx : x ∈ LieModule.lowerCentralSeries R L L (p.totalDegree - 1)) :
    p ⊗ₜ[R] x ∈ alignmentLiePolynomialArrays σ R L := by
  classical
  rw [p.as_sum, TensorProduct.sum_tmul]
  apply Submodule.sum_mem
  intro d hd
  have hdegree : d.sum (fun _ n => n) ≤ p.totalDegree := le_totalDegree hd
  have hx' : x ∈ LieModule.lowerCentralSeries R L L (d.sum (fun _ n => n) - 1) :=
    LieModule.antitone_lowerCentralSeries R L L (Nat.sub_le_sub_right hdegree 1) hx
  have h := alignmentLiePolynomialArrays_monomial d (p.coeff d • x)
    ((LieModule.lowerCentralSeries R L L _).smul_mem (p.coeff d) hx')
  change (monomial d (p.coeff d)) ⊗ₜ[R] x ∈ alignmentLiePolynomialArrays σ R L
  simpa only [← TensorProduct.smul_tmul, smul_monomial, smul_eq_mul, mul_one] using h

noncomputable def alignmentLieArrayInputShift (v : σ → R) :
    (MvPolynomial σ R ⊗[R] L) →ₗ⁅R⁆ (MvPolynomial σ R ⊗[R] L) :=
  LieAlgebra.ExtendScalars.map (alignmentCoefficientInputShift v) (LieHom.id : L →ₗ⁅R⁆ L)

theorem alignmentLieArrayInputShift_mem [Nontrivial R] (v : σ → R)
    (z : MvPolynomial σ R ⊗[R] L) (hz : z ∈ alignmentLiePolynomialArrays σ R L) :
    alignmentLieArrayInputShift v z ∈ alignmentLiePolynomialArrays σ R L := by
  change z ∈ alignmentLieArraySpace σ R L at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨d, x, hx, rfl⟩ := hz
    change alignmentCoefficientInputShift v (monomial d 1) ⊗ₜ[R] x ∈ alignmentLiePolynomialArrays σ R L
    apply alignmentLiePolynomialArrays_polynomial_tmul
    apply LieModule.antitone_lowerCentralSeries R L L _ hx
    apply Nat.sub_le_sub_right
    exact (alignmentCoefficientInputShift_degree v _).trans (totalDegree_monomial_le _ _)
  | zero => simpa only [map_zero] using (alignmentLiePolynomialArrays σ R L).zero_mem
  | add a b _ _ ha hb =>
    simpa only [map_add] using (alignmentLiePolynomialArrays σ R L).add_mem ha hb
  | smul r a _ ha =>
    simpa only [map_smul] using (alignmentLiePolynomialArrays σ R L).smul_mem r ha

end Hindman168


