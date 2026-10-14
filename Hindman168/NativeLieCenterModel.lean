import Hindman168.NativeLatticeCentralizer

/-! The actual original Lie center as a real submodule of its original
model. It is the kernel of the true adjoint differential; the already
proved original bracket identity and exponential detection identify its
vectors with the original group center. -/

namespace Hindman168
open Function Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeLieCenterModel : Submodule ℝ E :=
  (nativeLieAdjointDifferential (I := I) (G := G)).ker

 theorem nativeLieCenterModel_mem_iff_generator_eq_zero (v : E) :
    v ∈ nativeLieCenterModel (I := I) (G := G) ↔
      nativeLieAdjointGenerator (I := I) (G := G) v = 0 := by
  change nativeLieAdjointDifferential (I := I) (G := G) v = 0 ↔ _
  rw [nativeLieAdjointGenerator_eq_differential]

 theorem nativeLieCenterModel_mem_iff_native_bracket_zero (v : GroupLieAlgebra I G) :
    v ∈ nativeLieCenterModel (I := I) (G := G) ↔
      ∀ w : GroupLieAlgebra I G, ⁅v, w⁆ = 0 := by
  refine (nativeLieCenterModel_mem_iff_generator_eq_zero
    (I := I) (G := G) (show E from v)).trans ?_
  constructor
  · intro h w
    have hw := congrArg (fun B : E →L[ℝ] E => B (w : E)) h
    rw [nativeLieAdjointGenerator_eq_native_bracket] at hw
    exact hw
  · intro h
    ext w
    let w' : GroupLieAlgebra I G := w
    have hw := h w'
    rw [← nativeLieAdjointGenerator_eq_native_bracket] at hw
    exact hw

variable [Group.IsNilpotent G] [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

 theorem nativeLieExponential_mem_center_iff_mem_centerModel (v : E) :
    nativeLieExponential (I := I) (G := G) v ∈ Subgroup.center G ↔
      v ∈ nativeLieCenterModel (I := I) (G := G) := by
  rw [nativeLieExponential_mem_center_iff_generator_eq_zero,
    nativeLieCenterModel_mem_iff_generator_eq_zero]

 theorem nativeLieGlobalLogarithm_mem_centerModel_iff (g : G) :
    nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g ∈
      nativeLieCenterModel (I := I) (G := G) ↔ g ∈ Subgroup.center G := by
  rw [nativeLieCenterModel_mem_iff_generator_eq_zero,
    nativeLie_mem_center_iff_logarithm_generator_eq_zero (E := E) (I := I) g]

omit [Group.IsNilpotent G] [FiniteDimensional ℝ E] [ConnectedSpace G]
  [SimplyConnectedSpace G] in
 theorem nativeLieExponential_add_of_mem_centerModel {v w : E}
    (hv : v ∈ nativeLieCenterModel (I := I) (G := G)) :
    nativeLieExponential (I := I) (G := G) (v + w) =
      nativeLieExponential (I := I) (G := G) v * nativeLieExponential (I := I) (G := G) w := by
  apply nativeLieExponential_add_of_generator_apply_eq_zero
  rw [(nativeLieCenterModel_mem_iff_generator_eq_zero v).mp hv]
  rfl

end Hindman168
