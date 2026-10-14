import Hindman168.NativeRationalKernelLieFiltration
import Hindman168.RoughVectorMonomialCollection
import Hindman168.RoughVectorZeroTrimProjection

/-! True aggregate coefficient collection and zero trimming construct an
ACTUAL source for the kernel filtration, from an actual affine scalar
projection. Cancellation in raw list terms is not discarded. -/
namespace Hindman168
open scoped Manifold ContDiff Classical
universe u

noncomputable def nativeRationalKernelCollectedPolynomial {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial σ D.E) : RoughVectorMvPolynomial σ D.E :=
  roughVectorMvZeroTrim (roughVectorMvCollect p)

theorem native_rational_kernel_collected_polynomial_eval {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial σ D.E) (x : σ → ℝ) :
    roughVectorMvEval (nativeRationalKernelCollectedPolynomial D p) x = roughVectorMvEval p x := by
  rw [nativeRationalKernelCollectedPolynomial,rough_vector_zero_trim_eval,rough_vector_collect_eval]

theorem native_rational_kernel_collected_polynomial_projection {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial σ D.E) (F : D.E →ₗ[ℝ] ℝ) :
    roughVectorMvProjection F (nativeRationalKernelCollectedPolynomial D p) = roughVectorMvProjection F p := by
  rw [nativeRationalKernelCollectedPolynomial,rough_vector_zero_trim_projection,rough_vector_collect_projection]

theorem native_rational_kernel_collect_weighted {s ℓ : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (F : D.E →L[ℝ] ℝ)
    (hF : nativeLieLowerCentralModel (I := D.I) (G := D.G) 1 ≤ F.toLinearMap.ker)
    (hRat : ∀ v ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ, ∃ q : ℚ, F v = (q : ℝ))
    (p : RoughVectorMvPolynomial σ D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (hAffine : (roughVectorMvProjection F.toLinearMap p).totalDegree ≤ 1) :
    RoughVectorMvWeightedDegree (nativeRationalKernelLieFiltration D L F hF hRat).layer (roughVectorMvCollect p) 0 := by
  rintro a ha
  obtain ⟨J,_,rfl⟩ := List.mem_map.mp ha
  rw [MvPolynomial.totalDegree_monomial J one_ne_zero,Nat.add_zero,native_rational_kernel_lie_filtration_layer]
  have hOld := rough_vector_weighted_coefficient L.layer L.antitone hp J
  rw [Nat.add_zero] at hOld
  split_ifs with hhigh
  · refine ⟨hOld,?_⟩
    change F.toLinearMap (roughVectorMvCoefficient p J)=0
    rw [rough_vector_coefficient_projection]
    have hlt : (roughVectorMvProjection F.toLinearMap p).totalDegree < J.sum (fun _ n => n) :=
      hAffine.trans_lt (by omega)
    exact MvPolynomial.coeff_eq_zero_of_totalDegree_lt hlt
  · exact hOld

theorem native_rational_kernel_collected_polynomial_weighted_degree {s ℓ : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (F : D.E →L[ℝ] ℝ)
    (hF : nativeLieLowerCentralModel (I := D.I) (G := D.G) 1 ≤ F.toLinearMap.ker)
    (hRat : ∀ v ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ, ∃ q : ℚ, F v = (q : ℝ))
    (p : RoughVectorMvPolynomial σ D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (hAffine : (roughVectorMvProjection F.toLinearMap p).totalDegree ≤ 1) :
    RoughVectorMvWeightedDegree (nativeRationalKernelLieFiltration D L F hF hRat).layer
      (nativeRationalKernelCollectedPolynomial D p) 0 ∧
    RoughVectorMvDegreeLE (nativeRationalKernelCollectedPolynomial D p) ℓ := by
  have hw := native_rational_kernel_collect_weighted D L F hF hRat p hp hAffine
  let K := nativeRationalKernelLieFiltration D L F hF hRat
  have hd : RoughVectorMvDegreeLE (roughVectorMvZeroTrim (roughVectorMvCollect p)) (ℓ-0) :=
    rough_vector_zero_trim_degree K.layer K.antitone hw K.terminal
  exact ⟨rough_vector_zero_trim_weighted _ hw,
    by simpa only [nativeRationalKernelCollectedPolynomial,Nat.sub_zero] using hd⟩

end Hindman168
