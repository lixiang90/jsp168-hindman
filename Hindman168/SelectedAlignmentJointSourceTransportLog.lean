import Hindman168.AlignmentNativeExposedJointLog
import Hindman168.SelectedAlignmentJointSourceTransportEvaluation

/-! Gap-view adapters for the repository's original native source proofs.
The original master conditions and modulus are retained; only the short
exposure key and its bin origin use the separately specified model gap.
No master conditions for the changed-gap view are asserted. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators Classical

attribute [local instance 10] nativeFiniteProductTopologicalSpace
attribute [local instance] nativeFiniteProductGroup
  nativeFiniteProductNormedAddCommGroup nativeFiniteProductNormedSpace
  nativeFiniteProductCompleteSpace nativeFiniteProductFiniteDimensional
  nativeFiniteProductT2Space nativeFiniteProductIsNilpotent nativeFiniteProductConnectedSpace
  nativeFiniteProductChartTopology nativeFiniteProductChartedSpace
  nativeFiniteProductLieGroup nativeFiniteProductBoundaryless lieGroup_smooth_min_three
  alignmentAddingPairFintype

variable {κ : Type*} [Fintype κ] {N : ℕ} {i : Fin N}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [ConnectedSpace G] [SimplyConnectedSpace G]

variable (n : ℕ) (u : Fin (n + 1) → AlignmentAddingPair N i → ℤ)
  (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u))

theorem selected_alignmentNativeExposedJointLogPolynomial_frozen
    {d : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A D F) (gap : ℕ)
    (q₀ w : ℕ) (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i) {x y : Fin N → ℕ}
    (hx : ∀ j, Nat.Coprime (x j) (primorial w))
    (hy : ∀ j, Nat.Coprime (y j) (primorial w))
    (hkey : alignmentShortExposureKey (alignmentGeometryWithGap F i.val gap) w i T x = alignmentShortExposureKey (alignmentGeometryWithGap F i.val gap) w i T y)
    (v : AlignmentAddingPair N i → ℤ) (weight : κ → ℤ) (g b : G)
    (L : alignmentLiePolynomialArrays (AlignmentAddingPair N i) ℝ (GroupLieAlgebra I G) →ₗ[ℝ] ℝ) :
    alignmentNativeExposedJointLogPolynomial n u (alignmentGeometryWithGap F i.val gap) q₀ w T y v weight g b L =
      alignmentNativeExposedJointLogPolynomial n u (alignmentGeometryWithGap F i.val gap) q₀ w T x v weight g b L := by
  unfold alignmentNativeExposedJointLogPolynomial
  rw [selected_alignmentExposedJointBasePolynomial_frozen hF gap q₀ w i T hT hx hy hkey v weight]
  have hQ : alignmentExposedJointIncrementPolynomial (κ := κ) (alignmentGeometryWithGap F i.val gap) q₀ w i T y =
      alignmentExposedJointIncrementPolynomial (alignmentGeometryWithGap F i.val gap) q₀ w i T x := by
    funext e
    exact selected_alignmentExposedJointIncrementPolynomial_frozen hF gap q₀ w i T hx hy hkey e
  rw [hQ]

theorem selected_alignmentNativeExposedJointLogPolynomial_eval
    {d : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A D F) (gap : ℕ)
    {q₀ w : ℕ} (hq : 0 < q₀) (hw : q₀ + 1 ≤ w)
    (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i) {x y : Fin N → ℕ}
    (hx : ∀ j, Nat.Coprime (x j) (primorial w))
    (hy : ∀ j, Nat.Coprime (y j) (primorial w))
    (hkey : alignmentShortExposureKey (alignmentGeometryWithGap F i.val gap) w i T x = alignmentShortExposureKey (alignmentGeometryWithGap F i.val gap) w i T y)
    (p ell : ℤ) (hp : Int.ModEq (F.modulus w : ℕ) p (y i))
    (inc weight : κ → ℤ) (v : AlignmentAddingPair N i → ℤ) (g b : G)
    (L : alignmentLiePolynomialArrays (AlignmentAddingPair N i) ℝ (GroupLieAlgebra I G) →ₗ[ℝ] ℝ) :
    let Y : ℤ := (alignmentShortBinStart (alignmentGeometryWithGap F i.val gap) w i T x : ℤ) / (F.modulus w : ℤ)
    let tau : ℤ := alignmentNaturalBlockProduct y T
    MvPolynomial.eval (Sum.elim
      (fun j => match j with
        | none => (alignmentCubeBase (F.modulus w) tau p Y ell : ℝ)
        | some j => ((tau * inc j : ℤ) : ℝ)) (fun j => (y j : ℝ)))
      (alignmentNativeExposedJointLogPolynomial n u (alignmentGeometryWithGap F i.val gap) q₀ w T x v weight g b L) =
      L (alignmentNativeCoefficientLog n u hu
        (alignmentNativeCanonicalCubeArray n u hu g b y (F.modulus w)
          (fun e => alignmentPairResidue q₀ w (F.modulus w) e y)
          (fun e => alignmentPairProgression q₀ w (F.modulus w) e y)
          T p Y ell inc weight v)) := by
  dsimp only
  unfold alignmentNativeExposedJointLogPolynomial alignmentNativeCanonicalCubeArray
  apply alignmentNativeModelLogPolynomial_eval n u hu
  · exact selected_alignmentExposedJointBasePolynomial_eval hF gap q₀ w i T hT hx hy hkey p ell hp inc weight v
  · intro e
    exact selected_alignmentExposedJointIncrementPolynomial_eval hF gap hq hw i T hx hy hkey _ e


end Hindman168
