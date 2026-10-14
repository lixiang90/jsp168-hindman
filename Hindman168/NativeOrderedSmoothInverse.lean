import Hindman168.NativeOrderedExponentialSmooth

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]

def NativeOrderedCoordinateSmoothInverse {m : ℕ} (v : Fin m → E) : Prop :=
  ∃ r : G → (Fin m → ℝ),
    Function.LeftInverse r (nativeOrderedExponentialCoordinates (I := I) (G := G) v) ∧
    Function.RightInverse r (nativeOrderedExponentialCoordinates (I := I) (G := G) v) ∧
    ContMDiff I 𝓘(ℝ, Fin m → ℝ) ∞ r

end Hindman168
