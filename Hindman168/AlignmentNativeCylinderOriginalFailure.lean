import Hindman168.AlignmentNativeCompleteCubeFailure
import Hindman168.AlignmentOriginalProductAllFacesPosterior

/-! Literal cylinder face failure enters the ORIGINAL duplicated-component
all-face failure. The exact same samples, geometry, face, vertex profile and
source are retained; numerical observer membership is explicit. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators Classical
universe u

variable {ι : Type} [Fintype ι] {κ : Type*} [Fintype κ]
  {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))

theorem alignment_native_cylinder_failure_original_product {χ : Type} [Fintype χ]
    (label : χ → ι) (slots : χ → AlignmentAddingPair N i → ℤ)
    (test : (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G ⧸
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).Γ → ℂ)
    (B : χ → ℝ) (L : χ → NNReal) :
    letI : ∀ z, MetricSpace ((D (label z)).G ⧸ (D (label z)).Γ) := fun z => (D (label z)).metric
    letI : ∀ z, TopologicalSpace ((D (label z)).G ⧸ (D (label z)).Γ) :=
      fun z => (D (label z)).metric.toUniformSpace.toTopologicalSpace
    ∀ (obs : ∀ z, C((D (label z)).G ⧸ (D (label z)).Γ,ℂ)),
      (∀ z, obs z ∈ boundedComplexLipschitzObservables ((D (label z)).G ⧸ (D (label z)).Γ) (B z) (L z)) →
      (∀ x, test x=∏ z, obs z (alignmentJointNativeCosetEvaluation D n v hv (label z) (slots z) x)) →
      ∀ (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (d : ℕ)
        (shift : ι → AlignmentAddingPair N i → ℤ) (g a : ∀ ν, (D ν).G) (c C τ : ℝ) (y : Fin N → ℕ),
        alignmentNativeCylinderCubeAllFacesFailure (κ := κ) D n v hv F q₀ w T d shift g a c C τ test y →
        alignmentOriginalProductAllFacesFailure (β := κ) (fun z => D (label z)) F q₀ w T d
          (fun z => shift (label z)) slots (fun z => g (label z)) (fun z => a (label z)) B L c C τ y := by
  letI : ∀ z, MetricSpace ((D (label z)).G ⧸ (D (label z)).Γ) := fun z => (D (label z)).metric
  letI : ∀ z, TopologicalSpace ((D (label z)).G ⧸ (D (label z)).Γ) :=
    fun z => (D (label z)).metric.toUniformSpace.toTopologicalSpace
  intro obs hobs htest F q₀ w T d shift g a c C τ y hbad
  obtain ⟨weight,hw,e,he,j,lower,upper,ellResidue,hgeo,hbad⟩ := hbad
  let p := alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)) (F.modulus w) (y i)
  let Y : ℤ := (alignmentShortBinStart F w i T y : ℤ)/(F.modulus w : ℤ)
  have hmean : alignmentOriginalNativeCubeMean D n v hv F q₀ w T y p Y d ellResidue lower upper shift weight g a test=
      alignmentOriginalProductCubeMean (fun z => D (label z)) F q₀ w T y p d ellResidue lower upper
        (fun z => shift (label z)) slots (fun z => weight (label z))
        (fun z => g (label z)) (fun z => a (label z)) (fun z => obs z) := by
    rw [show test=(fun x => ∏ z, obs z (alignmentJointNativeCosetEvaluation D n v hv (label z) (slots z) x)) from funext htest]
    exact alignment_original_native_cube_product_mean D n v hv label slots (fun z => obs z)
      F q₀ w T y p Y d ellResidue lower upper shift weight g a
  have hface : alignmentOriginalNativeCubeMean D n v hv F q₀ w T y p Y d ellResidue lower upper shift weight g a
      (fun x => test (alignmentJointNativeCosetSlotTranslation D n v hv (fun ν => Pi.single e (weight ν j)) x))=
      alignmentOriginalProductCubeMean (fun z => D (label z)) F q₀ w T y p d ellResidue lower upper
        (fun z => shift (label z)) (fun z => slots z+Pi.single e (weight (label z) j)) (fun z => weight (label z))
        (fun z => g (label z)) (fun z => a (label z)) (fun z => obs z) := by
    rw [show test=(fun x => ∏ z, obs z (alignmentJointNativeCosetEvaluation D n v hv (label z) (slots z) x)) from funext htest]
    exact alignment_original_native_cube_translated_product_mean D n v hv label slots (fun z => obs z)
      (fun ν => Pi.single e (weight ν j)) F q₀ w T y p Y d ellResidue lower upper shift weight g a
  rw [hface,hmean] at hbad
  exact ⟨(fun z => weight (label z)),(fun z j => hw (label z) j),e,he,j,
    lower,upper,ellResidue,obs,hgeo,hobs,hbad⟩

end Hindman168
