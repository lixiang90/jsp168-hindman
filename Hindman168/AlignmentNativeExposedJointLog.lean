import Hindman168.AlignmentNativeCanonicalCubeArray
import Hindman168.AlignmentExposedJointEvaluation

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

noncomputable def alignmentNativeExposedJointLogPolynomial
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (x : Fin N → ℕ)
    (v : AlignmentAddingPair N i → ℤ) (weight : κ → ℤ) (g b : G)
    (L : alignmentLiePolynomialArrays (AlignmentAddingPair N i) ℝ (GroupLieAlgebra I G) →ₗ[ℝ] ℝ) :
    MvPolynomial (Sum (Option κ) (Fin N)) ℝ :=
  alignmentNativeModelLogPolynomial n u g b L
    (alignmentExposedJointBasePolynomial F q₀ w i T x v weight)
    (alignmentExposedJointIncrementPolynomial F q₀ w i T x)

theorem alignmentNativeExposedJointLogPolynomial_degree
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (x : Fin N → ℕ)
    (v : AlignmentAddingPair N i → ℤ) (weight : κ → ℤ) (g b : G)
    (L : alignmentLiePolynomialArrays (AlignmentAddingPair N i) ℝ (GroupLieAlgebra I G) →ₗ[ℝ] ℝ)
    (s : ℕ) (hs : Group.nilpotencyClass G ≤ s) :
    (alignmentNativeExposedJointLogPolynomial n u F q₀ w T x v weight g b L).totalDegree ≤
      ((s * s + 1) ^ (s + 1)) * max 1 T.card := by
  apply alignmentNativeModelLogPolynomial_degree n u _ _ _ _ _ s (max 1 T.card) hs
  · exact alignmentExposedJointBasePolynomial_degree _ _ _ _ _ _ _ _
  · intro e
    exact (alignmentExposedJointIncrementPolynomial_degree _ _ _ _ _ _ e).trans (le_max_right _ _)

theorem alignmentNativeExposedJointLogPolynomial_frozen
    {d : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A D F)
    (q₀ w : ℕ) (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i) {x y : Fin N → ℕ}
    (hx : ∀ j, Nat.Coprime (x j) (primorial w))
    (hy : ∀ j, Nat.Coprime (y j) (primorial w))
    (hkey : alignmentShortExposureKey F w i T x = alignmentShortExposureKey F w i T y)
    (v : AlignmentAddingPair N i → ℤ) (weight : κ → ℤ) (g b : G)
    (L : alignmentLiePolynomialArrays (AlignmentAddingPair N i) ℝ (GroupLieAlgebra I G) →ₗ[ℝ] ℝ) :
    alignmentNativeExposedJointLogPolynomial n u F q₀ w T y v weight g b L =
      alignmentNativeExposedJointLogPolynomial n u F q₀ w T x v weight g b L := by
  unfold alignmentNativeExposedJointLogPolynomial
  rw [alignmentExposedJointBasePolynomial_frozen hF q₀ w i T hT hx hy hkey v weight]
  have hQ : alignmentExposedJointIncrementPolynomial (κ := κ) F q₀ w i T y =
      alignmentExposedJointIncrementPolynomial F q₀ w i T x := by
    funext e
    exact alignmentExposedJointIncrementPolynomial_frozen hF q₀ w i T hx hy hkey e
  rw [hQ]

theorem alignmentNativeExposedJointLogPolynomial_eval
    {d : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A D F)
    {q₀ w : ℕ} (hq : 0 < q₀) (hw : q₀ + 1 ≤ w)
    (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i) {x y : Fin N → ℕ}
    (hx : ∀ j, Nat.Coprime (x j) (primorial w))
    (hy : ∀ j, Nat.Coprime (y j) (primorial w))
    (hkey : alignmentShortExposureKey F w i T x = alignmentShortExposureKey F w i T y)
    (p ell : ℤ) (hp : Int.ModEq (F.modulus w : ℕ) p (y i))
    (inc weight : κ → ℤ) (v : AlignmentAddingPair N i → ℤ) (g b : G)
    (L : alignmentLiePolynomialArrays (AlignmentAddingPair N i) ℝ (GroupLieAlgebra I G) →ₗ[ℝ] ℝ) :
    let Y : ℤ := (alignmentShortBinStart F w i T x : ℤ) / (F.modulus w : ℤ)
    let tau : ℤ := alignmentNaturalBlockProduct y T
    MvPolynomial.eval (Sum.elim
      (fun j => match j with
        | none => (alignmentCubeBase (F.modulus w) tau p Y ell : ℝ)
        | some j => ((tau * inc j : ℤ) : ℝ)) (fun j => (y j : ℝ)))
      (alignmentNativeExposedJointLogPolynomial n u F q₀ w T x v weight g b L) =
      L (alignmentNativeCoefficientLog n u hu
        (alignmentNativeCanonicalCubeArray n u hu g b y (F.modulus w)
          (fun e => alignmentPairResidue q₀ w (F.modulus w) e y)
          (fun e => alignmentPairProgression q₀ w (F.modulus w) e y)
          T p Y ell inc weight v)) := by
  dsimp only
  unfold alignmentNativeExposedJointLogPolynomial alignmentNativeCanonicalCubeArray
  apply alignmentNativeModelLogPolynomial_eval n u hu
  · exact alignmentExposedJointBasePolynomial_eval hF q₀ w i T hT hx hy hkey p ell hp inc weight v
  · intro e
    exact alignmentExposedJointIncrementPolynomial_eval hF hq hw i T hx hy hkey _ e

end Hindman168
