import Hindman168.NativeLieSubalgebraGraph

/-! Projection from the integrated graph to the original integrated
subalgebra is an actual group homomorphism. Original exponential
injectivity and actual exponential preimages make it bijective. -/

namespace Hindman168
open scoped Manifold ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  {G K : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
  [Group K] [TopologicalSpace K] [ChartedSpace H' K]
  [LieGroup I ∞ G] [LieGroup J ∞ K] [BoundarylessManifold I G]
  [BoundarylessManifold J K] [T2Space G] [T2Space K]
  [Group.IsNilpotent G] [Group.IsNilpotent K]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeLieSubalgebraGraphProjection
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) (φ : S →ₗ⁅ℝ⁆ GroupLieAlgebra J K) :
    nativeLieSubalgebraGraphSubgroup (E := E) (F := F) S φ →*
      nativeLieSubalgebraSubgroup (E := E) S where
  toFun g := ⟨g.val.1, nativeLieSubalgebraGraphSubgroup_fst_mem S φ g.val g.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem nativeLieSubalgebraGraphProjection_surjective
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) (φ : S →ₗ⁅ℝ⁆ GroupLieAlgebra J K) :
    Function.Surjective (nativeLieSubalgebraGraphProjection (E := E) (F := F) S φ) := by
  intro g
  obtain ⟨v, hv, hvg⟩ := (nativeLieSubalgebraSubgroup_mem_iff S g.val).mp g.property
  let w : S := ⟨v, hv⟩
  refine ⟨⟨(nativeLieExponential (I := I) (G := G) v,
    nativeLieExponential (I := J) (G := K) (φ w)), ?_⟩, Subtype.ext hvg⟩
  exact (nativeLieSubalgebraGraphSubgroup_mem_iff S φ _).mpr ⟨w, rfl⟩

variable [ConnectedSpace G] [SimplyConnectedSpace G]

theorem nativeLieSubalgebraGraphProjection_injective
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) (φ : S →ₗ⁅ℝ⁆ GroupLieAlgebra J K) :
    Function.Injective (nativeLieSubalgebraGraphProjection (E := E) (F := F) S φ) := by
  intro g h hgh
  obtain ⟨v, hv⟩ := (nativeLieSubalgebraGraphSubgroup_mem_iff S φ g.val).mp g.property
  obtain ⟨w, hw⟩ := (nativeLieSubalgebraGraphSubgroup_mem_iff S φ h.val).mp h.property
  have he : nativeLieExponential (I := I) (G := G) v.val =
      nativeLieExponential (I := I) (G := G) w.val :=
    (congrArg Prod.fst hv).trans
      ((congrArg (fun z : nativeLieSubalgebraSubgroup (E := E) S => z.val) hgh).trans
        (congrArg Prod.fst hw).symm)
  have hvw : v = w := Subtype.ext (nativeLieExponential_injective (I := I) (G := G) he)
  apply Subtype.ext
  exact hv.symm.trans ((congrArg (fun z : S =>
    (nativeLieExponential (I := I) (G := G) z.val,
      nativeLieExponential (I := J) (G := K) (φ z))) hvw).trans hw)

theorem nativeLieSubalgebraGraphProjection_bijective
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) (φ : S →ₗ⁅ℝ⁆ GroupLieAlgebra J K) :
    Function.Bijective (nativeLieSubalgebraGraphProjection (E := E) (F := F) S φ) :=
  ⟨nativeLieSubalgebraGraphProjection_injective S φ,
    nativeLieSubalgebraGraphProjection_surjective S φ⟩

end Hindman168
