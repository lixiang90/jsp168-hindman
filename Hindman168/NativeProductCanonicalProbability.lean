import Hindman168.NativeBorelProbabilityTranslation
import Hindman168.ProductCosetProbability

/-! Genuine ORIGINAL product canonical Haar is the actual product of the
two ORIGINAL probabilities under the ACTUAL coset homeomorphism. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

noncomputable def nativeProductBorelProbability {s : ℕ} (A B : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace A.E := borel A.E
    letI : MeasurableSpace A.G := borel A.G
    letI : MeasurableSpace B.E := borel B.E
    letI : MeasurableSpace B.G := borel B.G
    @Measure ((A.G × B.G) ⧸ A.Γ.prod B.Γ) (borel ((A.G × B.G) ⧸ A.Γ.prod B.Γ)) := by
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
  exact productCosetProbability A.Γ B.Γ (nativeNilmanifoldBorelProbability A) (nativeNilmanifoldBorelProbability B)

theorem native_product_borel_probability_isProbability {s : ℕ} (A B : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace A.E := borel A.E
    letI : MeasurableSpace A.G := borel A.G
    letI : MeasurableSpace B.E := borel B.E
    letI : MeasurableSpace B.G := borel B.G
    IsProbabilityMeasure (nativeProductBorelProbability A B) := by
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
  letI := native_nilmanifold_borel_probability_isProbability A
  letI := native_nilmanifold_borel_probability_isProbability B
  exact product_coset_probability_isProbability _ _ _ _

theorem native_product_borel_probability_translate {s : ℕ} (A B : NativeNilmanifoldData.{u} s)
    (g : A.G × B.G) :
    letI : MeasurableSpace A.E := borel A.E
    letI : MeasurableSpace A.G := borel A.G
    letI : MeasurableSpace B.E := borel B.E
    letI : MeasurableSpace B.G := borel B.G
    letI : MeasurableSpace ((A.G × B.G) ⧸ A.Γ.prod B.Γ) := borel ((A.G × B.G) ⧸ A.Γ.prod B.Γ)
    Measure.map (fun q : (A.G × B.G) ⧸ A.Γ.prod B.Γ => g • q) (nativeProductBorelProbability A B) =
      nativeProductBorelProbability A B := by
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
  letI := native_nilmanifold_borel_probability_isProbability A
  letI := native_nilmanifold_borel_probability_isProbability B
  exact product_coset_probability_translate _ _ _ _ (native_borel_probability_translate A)
    (native_borel_probability_translate B) g.1 g.2

theorem native_product_borel_probability_canonical {s : ℕ} (A B : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace A.E := borel A.E
    letI : MeasurableSpace A.G := borel A.G
    letI : MeasurableSpace B.E := borel B.E
    letI : MeasurableSpace B.G := borel B.G
    nativeProductBorelProbability A B = nativeNilmanifoldBorelProbability (nativeNilmanifoldProduct A B) := by
  letI : MeasurableSpace A.E := borel A.E
  letI : MeasurableSpace A.G := borel A.G
  letI : MeasurableSpace B.E := borel B.E
  letI : MeasurableSpace B.G := borel B.G
  exact native_nilmanifold_borel_probability_unique (nativeNilmanifoldProduct A B) _
    (native_product_borel_probability_isProbability A B) (native_product_borel_probability_translate A B)

end Hindman168
