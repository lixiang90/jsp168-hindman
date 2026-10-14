import Hindman168.NativeLieCenterModel
import Hindman168.NativeLieExponentialDiffeomorph
import Mathlib.Analysis.Convex.Contractible

/-! The actual center exponential is a natural subtype homeomorphism,
and its true logarithm converts original central multiplication to
addition. Its source remains the original adjoint kernel in E. -/

namespace Hindman168
open Function Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeLieCenterExponentialHomeomorph :
    nativeLieCenterModel (I := I) (G := G) ≃ₜ Subgroup.center G where
  toFun v := ⟨nativeLieExponential (I := I) (G := G) v.val,
    (nativeLieExponential_mem_center_iff_mem_centerModel v.val).mpr v.property⟩
  invFun g := ⟨nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g.val,
    (nativeLieGlobalLogarithm_mem_centerModel_iff g.val).mpr g.property⟩
  left_inv v := Subtype.ext (nativeLieGlobalLogarithm_exponential (I := I) (G := G) v.val)
  right_inv g := Subtype.ext (nativeLieExponential_globalLogarithm (I := I) (G := G) g.val)
  continuous_toFun :=
    ((nativeLieExponential_contMDiff (I := I) (G := G)).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((nativeLieGlobalLogarithm (E := E) (I := I) (G := G)).continuous.comp continuous_subtype_val).subtype_mk _

 theorem nativeLieGlobalLogarithm_central_mul {g h : G} (hg : g ∈ Subgroup.center G) :
    nativeLieGlobalLogarithm (E := E) (I := I) (G := G) (g * h) =
      nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g +
        nativeLieGlobalLogarithm (E := E) (I := I) (G := G) h := by
  apply nativeLieExponential_injective (I := I) (G := G)
  have hs := nativeLieExponential_add_of_mem_centerModel (I := I) (G := G)
    (w := nativeLieGlobalLogarithm (E := E) (I := I) (G := G) h)
    ((nativeLieGlobalLogarithm_mem_centerModel_iff g).mpr hg)
  exact (nativeLieExponential_globalLogarithm (E := E) (I := I) (g * h)).trans
    (hs.trans (congrArg₂ (fun a b : G => a * b)
      (nativeLieExponential_globalLogarithm (E := E) (I := I) g)
      (nativeLieExponential_globalLogarithm (E := E) (I := I) h))).symm

 theorem nativeLieCenterExponentialHomeomorph_add
    (v w : nativeLieCenterModel (I := I) (G := G)) :
    nativeLieCenterExponentialHomeomorph (I := I) (G := G) (v + w) =
      nativeLieCenterExponentialHomeomorph (I := I) (G := G) v *
        nativeLieCenterExponentialHomeomorph (I := I) (G := G) w :=
  Subtype.ext (nativeLieExponential_add_of_mem_centerModel v.property)

 theorem nativeLieCenterExponentialHomeomorph_symm_mul (g h : Subgroup.center G) :
    (nativeLieCenterExponentialHomeomorph (I := I) (G := G)).symm (g * h) =
      (nativeLieCenterExponentialHomeomorph (I := I) (G := G)).symm g +
        (nativeLieCenterExponentialHomeomorph (I := I) (G := G)).symm h :=
  Subtype.ext (nativeLieGlobalLogarithm_central_mul g.property)

include I in
 theorem nativeLieCenter_contractible : ContractibleSpace (Subgroup.center G) := by
  let V : Submodule ℝ E := nativeLieCenterModel (I := I) (G := G)
  letI : ContractibleSpace V := V.convex.contractibleSpace ⟨0, V.zero_mem⟩
  exact (nativeLieCenterExponentialHomeomorph (I := I) (G := G)).symm.contractibleSpace

end Hindman168
