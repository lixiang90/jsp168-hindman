import Hindman168.RoughNativePolynomialFiltered
import Hindman168.RoughVectorParameterSpecialization

namespace Hindman168
open scoped Manifold ContDiff

variable {κ E : Type*} [Fintype κ] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [Module ℚ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_joint_integer_polynomial_filtered (q : ℕ)
    {p : RoughVectorMvPolynomial (Option κ) E} (hp : RoughVectorMvDegreeLE p q) (z : ℝ) :
    RoughFilteredPolynomial (roughStretchedLowerCentralFiltration G (max 1 q))
      (fun x : κ → ℤ => nativeLieExponential (I := I) (G := G)
        (roughVectorMvEval (E := E) p (fun j => j.elim z (fun j => (x j : ℝ))))) := by
  have hs := rough_vector_parameter_specialize_degree z hp
  have hf := rough_native_integer_log_polynomial_filtered (I := I) (G := G) (max 1 q)
    (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))
    (roughVectorMvDegreeLE_mono hs (le_max_right _ _))
  simpa only [rough_vector_parameter_specialize_eval] using hf

theorem rough_native_joint_affine_integer_polynomial_filtered (q : ℕ)
    {p : RoughVectorMvPolynomial (Option κ) E} (hp : RoughVectorMvDegreeLE p q)
    (z : ℝ) (b r : κ → ℤ) :
    RoughFilteredPolynomial (roughStretchedLowerCentralFiltration G (max 1 q))
      (fun x : κ → ℤ => nativeLieExponential (I := I) (G := G)
        (roughVectorMvEval (E := E) p (fun j => j.elim z (fun j => (b j : ℝ)+(r j : ℝ)*(x j : ℝ))))) := by
  let sp := roughVectorMvAffineSubstitution (fun j => (b j : ℝ)) (fun j => (r j : ℝ))
    (roughVectorMvParameterSpecialize z p)
  have hs : RoughVectorMvDegreeLE sp q :=
    roughVectorMvAffineSubstitution_degree _ _ (rough_vector_parameter_specialize_degree z hp)
  have hf := rough_native_integer_log_polynomial_filtered (I := I) (G := G) (max 1 q)
    (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))
    (roughVectorMvDegreeLE_mono hs (le_max_right _ _))
  simpa only [sp, roughVectorMvAffineSubstitution_eval, rough_vector_parameter_specialize_eval] using hf

end Hindman168
