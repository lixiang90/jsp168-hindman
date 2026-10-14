import Hindman168.NativeOrderedExponentialCoordinates
import Hindman168.FiniteCoordinateSplit
import Mathlib.Data.List.OfFn

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]

attribute [local instance] lieGroup_smooth_min_three

theorem native_ordered_exponential_coordinates_append {m n : ℕ}
    (u : Fin m → E) (v : Fin n → E) (x : Fin m → ℝ) (y : Fin n → ℝ) :
    nativeOrderedExponentialCoordinates (I := I) (G := G) (Fin.append u v) (Fin.append x y) =
      nativeOrderedExponentialCoordinates (I := I) (G := G) u x *
        nativeOrderedExponentialCoordinates (I := I) (G := G) v y := by
  have he : (fun i => nativeLieExponential (I := I) (G := G)
      (Fin.append x y i • Fin.append u v i)) =
      Fin.append (fun i => nativeLieExponential (I := I) (G := G) (x i • u i))
        (fun i => nativeLieExponential (I := I) (G := G) (y i • v i)) := by
    funext i
    cases i using Fin.addCases <;> simp only [Fin.append_left, Fin.append_right]
  unfold nativeOrderedExponentialCoordinates
  rw [he, List.ofFn_fin_append, List.prod_append]

theorem native_ordered_exponential_coordinates_split {m n : ℕ}
    (u : Fin m → E) (v : Fin n → E) (x : Fin (m+n) → ℝ) :
    nativeOrderedExponentialCoordinates (I := I) (G := G) (Fin.append u v) x =
      nativeOrderedExponentialCoordinates (I := I) (G := G) u
          ((finiteCoordinateSplitEquiv m n x).1) *
        nativeOrderedExponentialCoordinates (I := I) (G := G) v
          ((finiteCoordinateSplitEquiv m n x).2) := by
  have h := native_ordered_exponential_coordinates_append (I := I) (G := G) u v
    (fun i => x (Fin.castAdd n i)) (fun i => x (Fin.natAdd m i))
  rw [Fin.append_castAdd_natAdd] at h
  exact h

end Hindman168
