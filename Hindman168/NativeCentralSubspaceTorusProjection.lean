import Hindman168.NativeCentralSubspaceLatticeCoordinates
import Mathlib.Analysis.Fourier.AddCircleMulti

/-! ACTUAL rational central SUBSPACE coordinates modulo ORIGINAL
restricted lattice. This handles the terminal layer separately from the center. -/

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

variable (Γ : Subgroup G) [DiscreteTopology Γ] (V : Submodule ℝ E)
  (hV : V ≤ nativeLieCenterModel (I := I) (G := G))
  (hrat : nativeLatticeRationalSubspace (E := E) (I := I) Γ V)

theorem native_central_subspace_lattice_coordinates_add
    (x y : Fin (Module.finrank ℝ V) → ℝ) :
    nativeCentralSubspaceLatticeCoordinates (I := I) Γ V hV hrat (x+y) =
      nativeCentralSubspaceLatticeCoordinates (I := I) Γ V hV hrat x *
        nativeCentralSubspaceLatticeCoordinates (I := I) Γ V hV hrat y := by
  apply Subtype.ext
  change nativeLieExponential (I := I) (G := G)
    (((nativeCentralSubspaceLatticeRealBasis (I := I) Γ V hV hrat).equivFunL.symm (x+y) : V) : E) = _
  rw [map_add]
  exact nativeLieExponential_add_of_mem_centerModel (hV
    ((nativeCentralSubspaceLatticeRealBasis (I := I) Γ V hV hrat).equivFunL.symm x).property)

theorem native_central_subspace_lattice_coordinates_symm_mul
    (g h : nativeCentralSubspaceSubgroup (I := I) V hV) :
    (nativeCentralSubspaceLatticeCoordinates (I := I) Γ V hV hrat).symm (g*h) =
      (nativeCentralSubspaceLatticeCoordinates (I := I) Γ V hV hrat).symm g +
        (nativeCentralSubspaceLatticeCoordinates (I := I) Γ V hV hrat).symm h := by
  apply (nativeCentralSubspaceLatticeCoordinates (I := I) Γ V hV hrat).injective
  rw [native_central_subspace_lattice_coordinates_add]
  simp only [Homeomorph.apply_symm_apply]

noncomputable def nativeCentralSubspaceTorusProjection
    (g : nativeCentralSubspaceSubgroup (I := I) V hV) : UnitAddTorus (Fin (Module.finrank ℝ V)) :=
  fun i => ((nativeCentralSubspaceLatticeCoordinates (I := I) Γ V hV hrat).symm g i : UnitAddCircle)

theorem native_central_subspace_torus_projection_mul
    (g h : nativeCentralSubspaceSubgroup (I := I) V hV) :
    nativeCentralSubspaceTorusProjection (I := I) Γ V hV hrat (g*h) =
      nativeCentralSubspaceTorusProjection (I := I) Γ V hV hrat g +
        nativeCentralSubspaceTorusProjection (I := I) Γ V hV hrat h := by
  funext i
  simp only [nativeCentralSubspaceTorusProjection,native_central_subspace_lattice_coordinates_symm_mul,
    Pi.add_apply,AddCircle.coe_add]

theorem native_central_subspace_torus_projection_one :
    nativeCentralSubspaceTorusProjection (I := I) Γ V hV hrat 1 = 0 := by
  have h := native_central_subspace_torus_projection_mul (I := I) Γ V hV hrat 1 1
  exact (add_left_cancel (show nativeCentralSubspaceTorusProjection (I := I) Γ V hV hrat 1 + 0 =
    nativeCentralSubspaceTorusProjection (I := I) Γ V hV hrat 1 +
      nativeCentralSubspaceTorusProjection (I := I) Γ V hV hrat 1
    by simpa only [one_mul,add_zero] using h)).symm

theorem native_central_subspace_torus_projection_inv
    (g : nativeCentralSubspaceSubgroup (I := I) V hV) :
    nativeCentralSubspaceTorusProjection (I := I) Γ V hV hrat g⁻¹ =
      -nativeCentralSubspaceTorusProjection (I := I) Γ V hV hrat g := by
  have h := native_central_subspace_torus_projection_mul (I := I) Γ V hV hrat g g⁻¹
  rw [mul_inv_cancel,native_central_subspace_torus_projection_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem native_central_subspace_torus_projection_kernel
    (g : nativeCentralSubspaceSubgroup (I := I) V hV) :
    nativeCentralSubspaceTorusProjection (I := I) Γ V hV hrat g = 0 ↔ (g : G) ∈ Γ := by
  have h := native_central_subspace_lattice_coordinates_mem_iff (I := I) Γ V hV hrat
    ((nativeCentralSubspaceLatticeCoordinates (I := I) Γ V hV hrat).symm g)
  rw [Homeomorph.apply_symm_apply] at h
  rw [h,funext_iff]
  simp only [nativeCentralSubspaceTorusProjection,Pi.zero_apply]
  simp_rw [AddCircle.coe_eq_zero_iff]
  simp only [zsmul_eq_mul,mul_one,eq_comm]

theorem native_central_subspace_torus_projection_surjective :
    Function.Surjective (nativeCentralSubspaceTorusProjection (I := I) Γ V hV hrat) := by
  intro y
  have h : ∀ i, ∃ x : ℝ, (x : UnitAddCircle) = y i := fun i => QuotientAddGroup.mk_surjective (y i)
  choose x hx using h
  refine ⟨nativeCentralSubspaceLatticeCoordinates (I := I) Γ V hV hrat x,?_⟩
  funext i
  simpa only [nativeCentralSubspaceTorusProjection,Homeomorph.symm_apply_apply] using hx i

theorem native_central_subspace_torus_projection_continuous :
    Continuous (nativeCentralSubspaceTorusProjection (I := I) Γ V hV hrat) := by
  apply continuous_pi
  intro i
  exact continuous_quotient_mk'.comp
    ((continuous_apply i).comp (nativeCentralSubspaceLatticeCoordinates (I := I) Γ V hV hrat).symm.continuous)

end Hindman168
