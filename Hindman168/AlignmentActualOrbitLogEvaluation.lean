import Hindman168.AlignmentExposedOrbitLogPolynomial

namespace Hindman168
open scoped Manifold ContDiff BigOperators Classical

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

theorem alignment_actual_orbit_log_evaluation
    {κ : Type*} [Fintype κ] {n d : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) {q₀ w : ℕ}
    (hq : 0 < q₀) (hw : q₀ + 1 ≤ w) (i : Fin n)
    (T : Finset (Fin n)) (hT : ∀ j ∈ T, j < i) {x y : Fin n → ℕ}
    (hx : ∀ j, Nat.Coprime (x j) (primorial w))
    (hy : ∀ j, Nat.Coprime (y j) (primorial w))
    (hkey : alignmentShortExposureKey F w i T x = alignmentShortExposureKey F w i T y)
    (p ell : ℤ) (hp : Int.ModEq (F.modulus w : ℕ) p (y i))
    (inc weight : κ → ℤ) (v u : AlignmentAddingPair n i → ℤ)
    (g b : G) (lambda : E →ₗ[ℝ] ℝ) :
    let Y : ℤ := (alignmentShortBinStart F w i T x : ℤ) / (F.modulus w : ℤ)
    let X := alignmentCubeVertex (F.modulus w) (alignmentNaturalBlockProduct y T) p Y ell inc weight
    let z : Option (Option (AlignmentAddingPair n i)) → ℚ := fun j => match j with
      | none => (X : ℚ)
      | some none => (alignmentNaturalBlockProduct y T : ℚ)
      | some (some e) => (u e : ℚ)
    let k : ℤ := alignmentIntegerArrayArgument y (F.modulus w)
      (fun e => alignmentPairResidue q₀ w (F.modulus w) e y)
      (fun e => alignmentPairProgression q₀ w (F.modulus w) e y) T
      (p + (F.modulus w : ℤ) * (ell + ∑ j, weight j * inc j)) v u / (F.modulus w : ℤ)
    MvPolynomial.eval (fun j => (z j : ℝ))
      (alignmentExposedOrbitLogPolynomial (I := I) F q₀ w i T x v g b lambda) =
      lambda (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) (g ^ k * b)) := by
  dsimp only
  apply alignmentExposedOrbitLogPolynomial_eval
  exact alignmentExposedCubePolynomial_eval hF hq hw i T hT hx hy hkey p ell hp inc weight v u

end Hindman168
