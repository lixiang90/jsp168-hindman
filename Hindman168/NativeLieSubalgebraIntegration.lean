import Hindman168.NativeLieSubalgebraGraphProjection

/-! Integrate an actual Lie homomorphism on an original native Lie
subalgebra by inverting the genuine graph projection. The resulting map
is an actual group homomorphism and has the original exponential values. -/

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

noncomputable def nativeLieSubalgebraGraphEquiv
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) (φ : S →ₗ⁅ℝ⁆ GroupLieAlgebra J K) :
    nativeLieSubalgebraGraphSubgroup (E := E) (F := F) S φ ≃*
      nativeLieSubalgebraSubgroup (E := E) S :=
  MulEquiv.ofBijective (nativeLieSubalgebraGraphProjection (E := E) (F := F) S φ)
    (nativeLieSubalgebraGraphProjection_bijective S φ)

noncomputable def nativeLieSubalgebraIntegrate
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) (φ : S →ₗ⁅ℝ⁆ GroupLieAlgebra J K) :
    nativeLieSubalgebraSubgroup (E := E) S →* K :=
  (MonoidHom.snd G K).comp
    ((nativeLieSubalgebraGraphSubgroup (E := E) (F := F) S φ).subtype.comp
      (nativeLieSubalgebraGraphEquiv (E := E) (F := F) S φ).symm.toMonoidHom)

theorem nativeLieSubalgebraIntegrate_exponential
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) (φ : S →ₗ⁅ℝ⁆ GroupLieAlgebra J K) (v : S) :
    nativeLieSubalgebraIntegrate (E := E) (F := F) S φ
        ⟨nativeLieExponential (I := I) (G := G) v.val, ⟨v.val, v.property, rfl⟩⟩ =
      nativeLieExponential (I := J) (G := K) (φ v) := by
  let q : nativeLieSubalgebraSubgroup (E := E) S :=
    ⟨nativeLieExponential (I := I) (G := G) v.val, ⟨v.val, v.property, rfl⟩⟩
  let p : nativeLieSubalgebraGraphSubgroup (E := E) (F := F) S φ :=
    ⟨(nativeLieExponential (I := I) (G := G) v.val,
      nativeLieExponential (I := J) (G := K) (φ v)),
      (nativeLieSubalgebraGraphSubgroup_mem_iff S φ _).mpr ⟨v, rfl⟩⟩
  let e := nativeLieSubalgebraGraphEquiv (E := E) (F := F) S φ
  have hp : e p = q := rfl
  have hq : e.symm q = p := (congrArg e.symm hp).symm.trans (e.symm_apply_apply p)
  change (e.symm q).val.2 = nativeLieExponential (I := J) (G := K) (φ v)
  exact congrArg (fun z : nativeLieSubalgebraGraphSubgroup (E := E) (F := F) S φ => z.val.2) hq

theorem nativeLieSubalgebraIntegrate_unique
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) (φ : S →ₗ⁅ℝ⁆ GroupLieAlgebra J K)
    (f : nativeLieSubalgebraSubgroup (E := E) S →* K)
    (hf : ∀ v : S, f ⟨nativeLieExponential (I := I) (G := G) v.val,
      ⟨v.val, v.property, rfl⟩⟩ = nativeLieExponential (I := J) (G := K) (φ v)) :
    f = nativeLieSubalgebraIntegrate (E := E) (F := F) S φ := by
  ext g
  obtain ⟨v, hv, hvg⟩ := (nativeLieSubalgebraSubgroup_mem_iff S g.val).mp g.property
  let w : S := ⟨v, hv⟩
  have hg : (⟨nativeLieExponential (I := I) (G := G) v, ⟨v, hv, rfl⟩⟩ :
      nativeLieSubalgebraSubgroup (E := E) S) = g := Subtype.ext hvg
  exact (congrArg f hg).symm.trans
    ((hf w).trans ((nativeLieSubalgebraIntegrate_exponential S φ w).symm.trans
      (congrArg (nativeLieSubalgebraIntegrate (E := E) (F := F) S φ) hg)))

end Hindman168
