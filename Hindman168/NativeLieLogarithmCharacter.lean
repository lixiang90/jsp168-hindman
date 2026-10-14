import Hindman168.NativeLieGlobalProductLog
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! The genuine original global logarithm yields a real additive
character after applying any real linear functional killing the actual
native commutator layer. The original product-log error proves additivity;
the true exponential inverse proves surjectivity for nonzero functionals. -/

namespace Hindman168
open Function Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeLieLogarithmCharacter (f : E →ₗ[ℝ] ℝ) : C(G, ℝ) where
  toFun g := f (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g)
  continuous_toFun := f.continuous_of_finiteDimensional.comp
    (nativeLieGlobalLogarithm (E := E) (I := I) (G := G)).continuous

 theorem nativeLieLogarithmCharacter_exponential (f : E →ₗ[ℝ] ℝ) (v : E) :
    nativeLieLogarithmCharacter (I := I) (G := G) f
      (nativeLieExponential (I := I) (G := G) v) = f v := by
  change f (nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
    (nativeLieExponential (I := I) (G := G) v)) = f v
  rw [nativeLieGlobalLogarithm_exponential (E := E)]

 theorem nativeLieLogarithmCharacter_mul (f : E →ₗ[ℝ] ℝ)
    (hf : nativeLieLowerCentralModel (I := I) (G := G) 1 ≤ f.ker) (g h : G) :
    nativeLieLogarithmCharacter (I := I) (G := G) f (g * h) =
      nativeLieLogarithmCharacter (I := I) (G := G) f g +
        nativeLieLogarithmCharacter (I := I) (G := G) f h := by
  have hz := hf (nativeLieGlobalLogarithm_mul_add_mod_commutatorLayer (E := E) (I := I) (G := G) g h)
  change f (_ - (_ + _)) = 0 at hz
  rw [map_sub, map_add] at hz
  exact sub_eq_zero.mp hz

 theorem nativeLieLogarithmCharacter_surjective (f : E →ₗ[ℝ] ℝ) (hf : f ≠ 0) :
    Surjective (nativeLieLogarithmCharacter (I := I) (G := G) f) := by
  obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp hf
  have hv' : f v ≠ 0 := by simpa only [LinearMap.zero_apply] using hv
  intro r
  refine ⟨nativeLieExponential (I := I) (G := G) ((r / f v) • v), ?_⟩
  rw [nativeLieLogarithmCharacter_exponential, map_smul]
  change r / f v * f v = r
  exact div_mul_cancel₀ r hv'

end Hindman168
