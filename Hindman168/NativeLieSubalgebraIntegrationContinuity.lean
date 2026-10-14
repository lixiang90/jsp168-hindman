import Hindman168.NativeLieSubalgebraIntegration

/-! The integrated homomorphism is continuous in the actual inherited
subgroup topology. Its concrete formula is original exponential composed
with a finite-dimensional coefficient linear map and the original log. -/

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
  [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeLieSubalgebraModelHom
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) (φ : S →ₗ⁅ℝ⁆ GroupLieAlgebra J K) :
    nativeLieSubalgebraModel (E := E) S →ₗ[ℝ] F where
  toFun v := φ ⟨v.val, v.property⟩
  map_add' v w := φ.map_add ⟨v.val, v.property⟩ ⟨w.val, w.property⟩
  map_smul' r v := φ.map_smul r ⟨v.val, v.property⟩

theorem nativeLieSubalgebraIntegrate_formula
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) (φ : S →ₗ⁅ℝ⁆ GroupLieAlgebra J K)
    (g : nativeLieSubalgebraSubgroup (E := E) S) :
    nativeLieSubalgebraIntegrate (E := E) (F := F) S φ g =
      nativeLieExponential (I := J) (G := K)
        (nativeLieSubalgebraModelHom (E := E) (F := F) S φ
          ((nativeLieSubalgebraExponentialHomeomorph (E := E) S).symm g)) := by
  let v := (nativeLieSubalgebraExponentialHomeomorph (E := E) S).symm g
  let w : S := ⟨v.val, v.property⟩
  have hg : (⟨nativeLieExponential (I := I) (G := G) v.val,
      ⟨v.val, v.property, rfl⟩⟩ : nativeLieSubalgebraSubgroup (E := E) S) = g :=
    (nativeLieSubalgebraExponentialHomeomorph (E := E) S).apply_symm_apply g
  exact (congrArg (nativeLieSubalgebraIntegrate (E := E) (F := F) S φ) hg).symm.trans
    (nativeLieSubalgebraIntegrate_exponential S φ w)

theorem nativeLieSubalgebraIntegrate_continuous
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) (φ : S →ₗ⁅ℝ⁆ GroupLieAlgebra J K) :
    Continuous (nativeLieSubalgebraIntegrate (E := E) (F := F) S φ) := by
  have hc := (nativeLieSubalgebraModelHom (E := E) (F := F) S φ).continuous_of_finiteDimensional
  exact ((nativeLieExponential_contMDiff (I := J) (G := K)).continuous.comp
    (hc.comp (nativeLieSubalgebraExponentialHomeomorph (E := E) S).symm.continuous)).congr
      (fun g => (nativeLieSubalgebraIntegrate_formula S φ g).symm)

end Hindman168
