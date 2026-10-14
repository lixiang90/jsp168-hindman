import Hindman168.NativeSequentialBinomialFactors
import Hindman168.NativeSubgroupLevelCharacters
import Hindman168.SequentialCircleFailure

/-! Failure of ACTUAL all-level irrationality constructs one actual
sequential descent step: fixed rational pivot and filtration, strictly
increasing subsequence, bounded scaled smooth coefficient, unbounded true
integer coefficients, corrected weighted normalized sources, strict dimension
decrease and exact all-real factorization. None of these outputs is assumed. -/
namespace Hindman168
open Filter
open scoped Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_sequential_irrationality_failure_descent {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop) (hpos : ∀ n, 0 < L n)
    (p : ℕ → RoughVectorMvPolynomial Unit D.E)
    (hp : ∀ n, RoughVectorMvWeightedDegree F.layer (p n) 0)
    (hz : ∀ n, roughVectorMvEval (p n) (fun _ => (0 : ℝ)) = 0)
    (hnot : ¬ NativeSubgroupSequentialIrrational D F L p) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ Tendsto (L ∘ f) atTop atTop ∧
      ∃ F' : NativeRationalSubgroupFiltration D ℓ,
      ∃ q : ℕ → RoughVectorMvPolynomial Unit D.E,
      ∃ a : NativeSequentialBinomialFactor D,
        nativeRationalSubgroupFiltrationDimension D F' < nativeRationalSubgroupFiltrationDimension D F ∧
        (∀ k, F'.layer k ≤ F.layer k) ∧
        NativeSequentialBinomialFactorAdmissible D ℓ (L ∘ f) a ∧
        ∀ n, RoughVectorMvWeightedDegree F'.layer (q n) 0 ∧
          roughVectorMvEval (q n) (fun _ => (0 : ℝ)) = 0 ∧
          ∀ b : ℝ, nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
            (roughVectorMvEval (E := D.E) (p (f n)) (fun _ => b)) =
              nativeSequentialFactorLeft D a n b *
              nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
                (roughVectorMvEval (E := D.E) (q n) (fun _ => b)) * nativeSequentialFactorRight D a n b := by
  classical
  unfold NativeSubgroupSequentialIrrational at hnot
  push Not at hnot
  obtain ⟨j,hj,hjTop,phi,hphi,hbad⟩ := hnot
  obtain ⟨psi,hAgree,hpsi,hGlobal⟩ := native_subgroup_level_character_rational_extension D F j phi hphi
  let x (n : ℕ) : ℝ := psi (roughVectorMvEval (adaptedTaylorResidual D (p n) j) (fun _ => (j : ℝ)))
  have hsame : (fun n => (L n)^j * ‖(x n : UnitAddCircle)‖) =
      (fun n => (L n)^j * ‖(phi (roughVectorMvEval (adaptedTaylorResidual D (p n) j)
        (fun _ => (j : ℝ))) : UnitAddCircle)‖) := by
    funext n
    exact congrArg (fun r : ℝ => (L n)^j * ‖(r : UnitAddCircle)‖)
      (native_subgroup_taylor_character_values_congr D F (p n) (hp n) j psi phi hAgree)
  have hbad' : ¬ Tendsto (fun n => (L n)^j * ‖(x n : UnitAddCircle)‖) atTop atTop := by
    rw [hsame]
    exact hbad
  obtain ⟨C,hC,f,hf,hLf,hbound⟩ := sequential_circle_failure_decomposition L x hL hpos j hbad'
  obtain ⟨⟨z,hzj,hzne⟩,hNext,hBracket,_⟩ := hpsi
  obtain ⟨V,hV,hVRat,hVOne⟩ := native_rational_subgroup_exists_level_pivot D F j psi hGlobal hzj hzne
  let F' := nativeRationalSubgroupLevelKernel D F j hj psi hNext hBracket hGlobal
  let a : NativeSequentialBinomialFactor D := {
    order := j
    vector := V
    realCoefficient := fun n => sequentialNearestError (x (f n))
    integerCoefficient := fun n => sequentialNearestInteger (x (f n)) }
  let q (n : ℕ) := roughVectorMvCollect (nativeTaylorDescentCorrection D (p (f n)) j
    (a.realCoefficient n) (a.integerCoefficient n) V)
  refine ⟨f,hf,hLf,F',q,a,?_,?_,?_,?_⟩
  · exact native_rational_subgroup_level_kernel_dimension_lt D F j hj hjTop psi hNext hBracket hGlobal hzj hzne
  · intro k
    rw [native_rational_subgroup_level_kernel_layer]
    split_ifs
    · exact inf_le_left
    · exact le_rfl
  · exact ⟨hj,hjTop,hVRat,C,hC,fun n => (hbound n).2.1⟩
  · intro n
    refine ⟨?_,?_,?_⟩
    · exact native_taylor_kernel_corrected_source_adapted D F (p (f n)) (hp (f n)) (hz (f n))
        j hj psi hNext hBracket hGlobal (a.realCoefficient n) (a.integerCoefficient n) hV hVOne (hbound n).1
    · exact native_taylor_kernel_corrected_source_normalized D (p (f n)) (hz (f n))
        j hj (a.realCoefficient n) (a.integerCoefficient n) V
    · intro b
      exact native_taylor_correction_factor_recovery D (p (f n)) j
        (a.realCoefficient n) (a.integerCoefficient n) V b

end Hindman168
