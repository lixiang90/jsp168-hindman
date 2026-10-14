import Hindman168.NativeFourierPairFactor
import Hindman168.RoughVectorMvPairPolynomial
import Hindman168.RoughMvAffineSubstitution
import Hindman168.NativeCentralPolynomialProjection
import Hindman168.NativeProductExponential

/-! ACTUAL shifted pair polynomial and its original diagonal-factor samples.
The finite correlation is EXACTLY the original derivative average. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativePairShiftPolynomial {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial σ D.E) (h : σ → ℤ) :
    RoughVectorMvPolynomial σ (nativeNilmanifoldProduct D D).E :=
  roughVectorMvPairPolynomial (roughVectorMvAffineSubstitution (fun i => (h i : ℝ)) (fun _ => 1) p) p

theorem native_pair_shift_polynomial_degree {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial σ D.E) (h : σ → ℤ) (d : ℕ)
    (hp : RoughVectorMvDegreeLE p d) : RoughVectorMvDegreeLE (nativePairShiftPolynomial D p h) d :=
  rough_vector_mv_pair_polynomial_degree _ _ d (roughVectorMvAffineSubstitution_degree _ _ hp) hp

theorem native_pair_shift_polynomial_orbit {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial σ D.E) (h x : σ → ℤ) :
    productCosetMap D.Γ D.Γ (nativeMvPolynomialOrbit (nativeNilmanifoldProduct D D)
      (nativePairShiftPolynomial D p h) x) =
        (nativeMvPolynomialOrbit D p (x+h),nativeMvPolynomialOrbit D p x) := by
  change productCosetMap D.Γ D.Γ
    ((nativeLieExponential (E := D.E × D.E) (I := D.I.prod D.I) (G := D.G × D.G)
      (roughVectorMvEval (E := D.E × D.E)
        (roughVectorMvPairPolynomial (roughVectorMvAffineSubstitution
          (fun i => (h i : ℝ)) (fun _ => 1) p) p) (fun i => (x i : ℝ)))) :
        (D.G × D.G) ⧸ D.Γ.prod D.Γ) =
      (nativeMvPolynomialOrbit D p (x+h),nativeMvPolynomialOrbit D p x)
  unfold nativeMvPolynomialOrbit
  rw [rough_vector_mv_pair_polynomial_eval,roughVectorMvAffineSubstitution_eval,
    nativeProductExponential_eq (I := D.I) (J := D.I) (G := D.G) (K := D.G),productCosetMap_mk]
  have hx : (fun i => (h i : ℝ)+1*(x i : ℝ)) = (fun i => ((x+h) i : ℝ)) := by
    funext i
    simp only [Pi.add_apply,Int.cast_add,one_mul,add_comm]
  rw [hx]

theorem native_fourier_pair_factor_polynomial_sample {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial σ D.E) (h x : σ → ℤ)
    (k : nativeNilmanifoldCenterIndex D → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ, ℂ),
      nativeFourierPairFactor D k F (nativeDiagonalFactorMap D
        (nativeMvPolynomialOrbit (nativeNilmanifoldProduct D D) (nativePairShiftPolynomial D p h) x)) =
      nativeCentralFourierProjection D k F (nativeMvPolynomialOrbit D p (x+h)) *
        star (nativeCentralFourierProjection D k F (nativeMvPolynomialOrbit D p x)) := by
  intro F
  rw [native_fourier_pair_factor_apply,native_fourier_pair_observable_apply,native_pair_shift_polynomial_orbit]

theorem native_fourier_pair_factor_polynomial_mean {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial σ D.E) (h : σ → ℤ)
    (a : Finset (σ → ℤ)) (k : nativeNilmanifoldCenterIndex D → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ, ℂ),
      finiteComplexSetMean a (fun x => nativeFourierPairFactor D k F (nativeDiagonalFactorMap D
        (nativeMvPolynomialOrbit (nativeNilmanifoldProduct D D) (nativePairShiftPolynomial D p h) x))) =
      finiteComplexSetMean a (fun x => nativeCentralFourierProjection D k F (nativeMvPolynomialOrbit D p (x+h)) *
        star (nativeCentralFourierProjection D k F (nativeMvPolynomialOrbit D p x))) := by
  intro F
  congr 1
  funext x
  exact native_fourier_pair_factor_polynomial_sample D p h x k F

end Hindman168
