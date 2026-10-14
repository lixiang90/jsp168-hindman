import Hindman168.NativeProductCanonicalProbability
import Mathlib.MeasureTheory.Integral.Prod

/-! Exact ORIGINAL canonical product integrals and product coordinate
pushforward, using true coset homeomorphism and PROVED canonical uniqueness. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

theorem native_product_canonical_integral {s : ℕ} (A B : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace A.E := borel A.E
    letI : MeasurableSpace A.G := borel A.G
    letI : MeasurableSpace B.E := borel B.E
    letI : MeasurableSpace B.G := borel B.G
    letI : MeasurableSpace (nativeNilmanifoldProduct A B).E := borel (nativeNilmanifoldProduct A B).E
    letI : MeasurableSpace (nativeNilmanifoldProduct A B).G := borel (nativeNilmanifoldProduct A B).G
    letI : MeasurableSpace (A.G ⧸ A.Γ) := borel (A.G ⧸ A.Γ)
    letI : MeasurableSpace (B.G ⧸ B.Γ) := borel (B.G ⧸ B.Γ)
    ∀ f : ((A.G × B.G) ⧸ A.Γ.prod B.Γ) → ℂ,
      (∫ q, f q ∂nativeNilmanifoldQuotientProbability (nativeNilmanifoldProduct A B)) =
        ∫ p, f ((productCosetHomeomorph A.Γ B.Γ).symm p)
          ∂(nativeNilmanifoldBorelProbability A).prod (nativeNilmanifoldBorelProbability B) := by
  letI : MeasurableSpace A.E := borel A.E
  letI : MeasurableSpace A.G := borel A.G
  letI : MeasurableSpace B.E := borel B.E
  letI : MeasurableSpace B.G := borel B.G
  letI : MeasurableSpace (nativeNilmanifoldProduct A B).E := borel (nativeNilmanifoldProduct A B).E
  letI : MeasurableSpace (nativeNilmanifoldProduct A B).G := borel (nativeNilmanifoldProduct A B).G
  letI : MeasurableSpace (A.G ⧸ A.Γ) := borel (A.G ⧸ A.Γ)
  letI : MeasurableSpace (B.G ⧸ B.Γ) := borel (B.G ⧸ B.Γ)
  letI : BorelSpace (A.G ⧸ A.Γ) := ⟨rfl⟩
  letI : BorelSpace (B.G ⧸ B.Γ) := ⟨rfl⟩
  letI : SecondCountableTopology B.G :=
    (nativeLieGlobalExponentialHomeomorph (I := B.I) (G := B.G)).symm.secondCountableTopology
  intro f
  rw [← native_nilmanifold_borel_probability_integral (nativeNilmanifoldProduct A B),
    ← native_product_borel_probability_canonical]
  letI : MeasurableSpace ((A.G × B.G) ⧸ A.Γ.prod B.Γ) := borel ((A.G × B.G) ⧸ A.Γ.prod B.Γ)
  letI : BorelSpace ((A.G × B.G) ⧸ A.Γ.prod B.Γ) := ⟨rfl⟩
  exact (productCosetHomeomorph A.Γ B.Γ).symm.measurableEmbedding.integral_map f

theorem native_product_canonical_coordinate_map {s : ℕ} (A B : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace A.E := borel A.E
    letI : MeasurableSpace A.G := borel A.G
    letI : MeasurableSpace B.E := borel B.E
    letI : MeasurableSpace B.G := borel B.G
    letI : MeasurableSpace (A.G ⧸ A.Γ) := borel (A.G ⧸ A.Γ)
    letI : MeasurableSpace (B.G ⧸ B.Γ) := borel (B.G ⧸ B.Γ)
    letI : MeasurableSpace ((A.G × B.G) ⧸ A.Γ.prod B.Γ) := borel ((A.G × B.G) ⧸ A.Γ.prod B.Γ)
    Measure.map (productCosetMap A.Γ B.Γ) (nativeNilmanifoldBorelProbability (nativeNilmanifoldProduct A B)) =
      (nativeNilmanifoldBorelProbability A).prod (nativeNilmanifoldBorelProbability B) := by
  letI : MeasurableSpace A.E := borel A.E
  letI : MeasurableSpace A.G := borel A.G
  letI : MeasurableSpace B.E := borel B.E
  letI : MeasurableSpace B.G := borel B.G
  letI : MeasurableSpace (A.G ⧸ A.Γ) := borel (A.G ⧸ A.Γ)
  letI : MeasurableSpace (B.G ⧸ B.Γ) := borel (B.G ⧸ B.Γ)
  letI : BorelSpace (A.G ⧸ A.Γ) := ⟨rfl⟩
  letI : BorelSpace (B.G ⧸ B.Γ) := ⟨rfl⟩
  letI : SecondCountableTopology B.G :=
    (nativeLieGlobalExponentialHomeomorph (I := B.I) (G := B.G)).symm.secondCountableTopology
  rw [← native_product_borel_probability_canonical]
  exact product_coset_probability_map _ _ _ _

end Hindman168
