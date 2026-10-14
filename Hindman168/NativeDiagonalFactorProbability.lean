import Hindman168.NativeFourierPairFactor
import Hindman168.CentralSubgroupFactorProbability

/-! ACTUAL pushforward of genuine ORIGINAL product canonical Haar to the
actual diagonal-center factor. Canonical identification of separately built
factor native data still requires rational lattice/geometry construction. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u
attribute [local instance] diagonal_center_normal

noncomputable def nativeDiagonalFactorProbability {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace (nativeNilmanifoldProduct D D).E := borel (nativeNilmanifoldProduct D D).E
    letI : MeasurableSpace (nativeNilmanifoldProduct D D).G := borel (nativeNilmanifoldProduct D D).G
    letI : MeasurableSpace (D.G × D.G) := borel (D.G × D.G)
    letI : (diagonalCenterSubgroup D.G).Normal := diagonal_center_normal D.G
    @Measure (nativeDiagonalFactorSpace D) (borel (nativeDiagonalFactorSpace D)) := by
  letI : MeasurableSpace (nativeNilmanifoldProduct D D).E := borel (nativeNilmanifoldProduct D D).E
  letI : MeasurableSpace (nativeNilmanifoldProduct D D).G := borel (nativeNilmanifoldProduct D D).G
  letI : MeasurableSpace (D.G × D.G) := borel (D.G × D.G)
  letI : (diagonalCenterSubgroup D.G).Normal := diagonal_center_normal D.G
  letI : BorelSpace ((D.G × D.G) ⧸ D.Γ.prod D.Γ) := native_nilmanifold_coset_borel (nativeNilmanifoldProduct D D)
  exact centralSubgroupFactorProbability (diagonalCenterSubgroup D.G) (D.Γ.prod D.Γ)
    (nativeNilmanifoldQuotientProbability (nativeNilmanifoldProduct D D))

theorem native_diagonal_factor_probability_isProbability {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace (nativeNilmanifoldProduct D D).E := borel (nativeNilmanifoldProduct D D).E
    letI : MeasurableSpace (nativeNilmanifoldProduct D D).G := borel (nativeNilmanifoldProduct D D).G
    letI : MeasurableSpace (D.G × D.G) := borel (D.G × D.G)
    letI : (diagonalCenterSubgroup D.G).Normal := diagonal_center_normal D.G
    IsProbabilityMeasure (nativeDiagonalFactorProbability D) := by
  letI : MeasurableSpace (nativeNilmanifoldProduct D D).E := borel (nativeNilmanifoldProduct D D).E
  letI : MeasurableSpace (nativeNilmanifoldProduct D D).G := borel (nativeNilmanifoldProduct D D).G
  letI : MeasurableSpace (D.G × D.G) := borel (D.G × D.G)
  letI : (diagonalCenterSubgroup D.G).Normal := diagonal_center_normal D.G
  letI : BorelSpace ((D.G × D.G) ⧸ D.Γ.prod D.Γ) := native_nilmanifold_coset_borel (nativeNilmanifoldProduct D D)
  let μ : Measure ((D.G × D.G) ⧸ D.Γ.prod D.Γ) :=
    nativeNilmanifoldQuotientProbability (nativeNilmanifoldProduct D D)
  letI : IsProbabilityMeasure μ := native_nilmanifold_quotient_probability_isProbability (nativeNilmanifoldProduct D D)
  exact central_subgroup_factor_probability_isProbability (G := D.G × D.G)
    (diagonalCenterSubgroup D.G) (D.Γ.prod D.Γ) μ

theorem native_diagonal_factor_probability_integral {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace (nativeNilmanifoldProduct D D).E := borel (nativeNilmanifoldProduct D D).E
    letI : MeasurableSpace (nativeNilmanifoldProduct D D).G := borel (nativeNilmanifoldProduct D D).G
    letI : MeasurableSpace (D.G × D.G) := borel (D.G × D.G)
    letI : (diagonalCenterSubgroup D.G).Normal := diagonal_center_normal D.G
    ∀ F : C(nativeDiagonalFactorSpace D, ℂ),
      (∫ y, F y ∂nativeDiagonalFactorProbability D) =
        ∫ q, F (nativeDiagonalFactorMap D q) ∂nativeNilmanifoldQuotientProbability (nativeNilmanifoldProduct D D) := by
  letI : MeasurableSpace (nativeNilmanifoldProduct D D).E := borel (nativeNilmanifoldProduct D D).E
  letI : MeasurableSpace (nativeNilmanifoldProduct D D).G := borel (nativeNilmanifoldProduct D D).G
  letI : MeasurableSpace (D.G × D.G) := borel (D.G × D.G)
  letI : (diagonalCenterSubgroup D.G).Normal := diagonal_center_normal D.G
  letI : BorelSpace ((D.G × D.G) ⧸ D.Γ.prod D.Γ) := native_nilmanifold_coset_borel (nativeNilmanifoldProduct D D)
  intro F
  exact central_subgroup_factor_probability_integral _ _ _ F

theorem native_diagonal_factor_probability_translate {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (g : (D.G × D.G) ⧸ diagonalCenterSubgroup D.G) :
    letI : MeasurableSpace (nativeNilmanifoldProduct D D).E := borel (nativeNilmanifoldProduct D D).E
    letI : MeasurableSpace (nativeNilmanifoldProduct D D).G := borel (nativeNilmanifoldProduct D D).G
    letI : MeasurableSpace (D.G × D.G) := borel (D.G × D.G)
    letI : (diagonalCenterSubgroup D.G).Normal := diagonal_center_normal D.G
    letI : MeasurableSpace (nativeDiagonalFactorSpace D) := borel (nativeDiagonalFactorSpace D)
    Measure.map (fun y : nativeDiagonalFactorSpace D => g • y) (nativeDiagonalFactorProbability D) =
      nativeDiagonalFactorProbability D := by
  letI : MeasurableSpace (nativeNilmanifoldProduct D D).E := borel (nativeNilmanifoldProduct D D).E
  letI : MeasurableSpace (nativeNilmanifoldProduct D D).G := borel (nativeNilmanifoldProduct D D).G
  letI : MeasurableSpace (D.G × D.G) := borel (D.G × D.G)
  letI : (diagonalCenterSubgroup D.G).Normal := diagonal_center_normal D.G
  letI : BorelSpace ((D.G × D.G) ⧸ D.Γ.prod D.Γ) := native_nilmanifold_coset_borel (nativeNilmanifoldProduct D D)
  let μ : Measure ((D.G × D.G) ⧸ D.Γ.prod D.Γ) :=
    nativeNilmanifoldQuotientProbability (nativeNilmanifoldProduct D D)
  have hμ : ∀ h : D.G × D.G, Measure.map (fun q : (D.G × D.G) ⧸ D.Γ.prod D.Γ => h • q) μ = μ := by
    intro h
    exact native_nilmanifold_quotient_probability_translate (nativeNilmanifoldProduct D D) h
  exact central_subgroup_factor_probability_translate (G := D.G × D.G)
    (diagonalCenterSubgroup D.G) (D.Γ.prod D.Γ) μ hμ g

end Hindman168
