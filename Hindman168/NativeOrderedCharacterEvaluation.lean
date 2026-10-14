import Hindman168.NativeOrderedExponentialCoordinates
import Hindman168.NativeLieLogarithmCharacter
import Mathlib.Algebra.BigOperators.Fin

/-! Actual horizontal characters evaluate ordered original exponential
products as linear forms. The ordered product is retained throughout. -/

namespace Hindman168
open scoped BigOperators Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem native_logarithm_character_one (f : E →ₗ[ℝ] ℝ) :
    nativeLieLogarithmCharacter (I := I) (G := G) f 1 = 0 := by
  change f (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) 1) = 0
  rw [nativeLieGlobalLogarithm_one, map_zero]

theorem native_logarithm_character_list_product (f : E →ₗ[ℝ] ℝ)
    (hf : nativeLieLowerCentralModel (I := I) (G := G) 1 ≤ f.ker) (l : List G) :
    nativeLieLogarithmCharacter (I := I) (G := G) f l.prod =
      (l.map (nativeLieLogarithmCharacter (I := I) (G := G) f)).sum := by
  induction l with
  | nil => simp only [List.prod_nil, List.map_nil, List.sum_nil,
      native_logarithm_character_one]
  | cons g l ih =>
      simp only [List.prod_cons, List.map_cons, List.sum_cons,
        nativeLieLogarithmCharacter_mul f hf, ih]

theorem native_ordered_character_evaluation (f : E →ₗ[ℝ] ℝ)
    (hf : nativeLieLowerCentralModel (I := I) (G := G) 1 ≤ f.ker)
    {m : ℕ} (v : Fin m → E) (x : Fin m → ℝ) :
    nativeLieLogarithmCharacter (I := I) (G := G) f
      (nativeOrderedExponentialCoordinates (I := I) (G := G) v x) =
        ∑ i, x i * f (v i) := by
  rw [nativeOrderedExponentialCoordinates, native_logarithm_character_list_product f hf]
  simp only [List.map_ofFn, Function.comp_def, nativeLieLogarithmCharacter_exponential,
    map_smul, smul_eq_mul, List.sum_ofFn]

theorem native_logarithm_character_contMDiff (f : E →ₗ[ℝ] ℝ) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (nativeLieLogarithmCharacter (I := I) (G := G) f) := by
  exact f.toContinuousLinearMap.contDiff.contMDiff.comp
    (nativeLieGlobalLogarithm_contMDiff (E := E) (I := I))

end Hindman168
