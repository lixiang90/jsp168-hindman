import Hindman168.NativeRationalHighestLayerDirection
import Hindman168.NativeRationalKernelExactFactorization

/-! ACTUAL nonlinearity descent now has a GENUINE source factorization,
with fixed rational highest-layer direction BEFORE every source. The
explicit removed scalar factor is not yet proved small/rational bounded. -/
namespace Hindman168
open Module
open scoped Manifold ContDiff BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_nonlinearity_exact_factorization {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (hdeg : 2 ≤ ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hHor : RoughNativeHorizontalFunctional (I := (nativeRationalRelativeData D L 1).I)
      (nativeRationalRelativeData D L 1).Γ χ.toLinearMap)
    (hzero : ∀ g h : D.G, nativeRationalRelativeCommutatorValue D L χ g h=0)
    (hne : nativeRationalRelativeDifferenceCharacter D L χ ≠ 0) :
    let K := nativeRationalNonlinearKernelFiltration D L χ hHor hzero
    let F := nativeRationalDifferenceExtension D L χ
    nativeRationalFiltrationNonlinearity D K < nativeRationalFiltrationNonlinearity D L ∧
      ∃ (j : ℕ) (y : D.E) (q : ℕ), 2 ≤ j ∧ j ≤ ℓ ∧ y ∈ L.layer j ∧
        y ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ ∧ F y=1 ∧
        L.layer (j+1) ≤ F.toLinearMap.ker ∧ 0 < q ∧
        nativeLieExponential (E := D.E) (I := D.I) (G := D.G) y ^ q ∈ D.Γ ∧
        ∀ (p : RoughVectorMvPolynomial Unit D.E), RoughVectorMvWeightedDegree L.layer p 0 →
          ∃ pK : RoughVectorMvPolynomial Unit D.E, RoughVectorMvWeightedDegree K.layer pK 0 ∧
            RoughVectorMvDegreeLE pK ℓ ∧ ∀ x : Unit → ℝ,
              nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) p x) =
                nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
                  (MvPolynomial.eval x (unitMvNonlinearPart (roughVectorMvProjection F.toLinearMap p)) • y) *
                    nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) pK x) := by
  let F := nativeRationalDifferenceExtension D L χ
  have hF : nativeLieLowerCentralModel (I := D.I) (G := D.G) 1 ≤ F.toLinearMap.ker :=
    native_rational_difference_extension_kills_commutator D L χ hHor.2.1 hzero
  have hRat : ∀ v ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ, ∃ q : ℚ, F v = (q : ℝ) :=
    fun v hv => native_rational_difference_extension_rational_value D L χ hHor.2.2 ⟨v,hv⟩
  have hNonzero := native_rational_difference_extension_nonzero_on_two D L χ hne
  obtain ⟨j,y,q,hj2,hjL,hy,hyRat,hFy,hHigher,hq,hpow⟩ :=
    native_rational_highest_layer_direction D L hdeg F hRat hNonzero
  refine ⟨native_rational_nonlinear_kernel_filtration_nonlinearity_lt D L hdeg χ hHor hzero hne,
    j,y,q,hj2,hjL,hy,hyRat,hFy,hHigher,hq,hpow,?_⟩
  intro p hp
  obtain ⟨hWeighted,hDegree⟩ := native_rational_kernel_exact_residual_weighted_degree D L F hF hRat
    p hp j (by omega) y hy hFy hHigher
  exact ⟨nativeRationalKernelExactResidual D F p y,hWeighted,hDegree,
    native_rational_kernel_exact_factorization D F p y⟩

end Hindman168
