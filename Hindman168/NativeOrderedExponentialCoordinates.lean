import Hindman168.NativeCenterQuotientNativeExponential
import Hindman168.NativeLieRationalPowerMembership
import Mathlib.Algebra.BigOperators.Group.List.Basic

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeOrderedExponentialCoordinates {m : ℕ}
    (v : Fin m → E) (x : Fin m → ℝ) : G :=
  (List.ofFn (fun i => nativeLieExponential (I := I) (G := G) (x i • v i))).prod

omit [Group.IsNilpotent G] [FiniteDimensional ℝ E] [ConnectedSpace G]
  [SimplyConnectedSpace G] in
theorem native_ordered_exponential_coordinates_integer_mem {m : ℕ}
    (Γ : Subgroup G) (v : Fin m → E)
    (hv : ∀ i, nativeLieExponential (I := I) (G := G) (v i) ∈ Γ)
    (x : Fin m → ℝ) (hx : ∀ i, ∃ n : ℤ, x i = (n : ℝ)) :
    nativeOrderedExponentialCoordinates (I := I) (G := G) v x ∈ Γ := by
  apply Γ.list_prod_mem
  intro g hg
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
  obtain ⟨n, hn⟩ := hx i
  rw [hn, nativeLieExponential_int_smul]
  exact Γ.zpow_mem (hv i) n

theorem native_ordered_exponential_coordinates_center_projection {m : ℕ}
    (u : Fin m → E) :
    letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
    letI := nativeCenterQuotient_t2Space (I := I) (G := G)
    letI := nativeCenterQuotient_lieGroup (I := I) (G := G)
    let F := E ⧸ nativeLieCenterModel (I := I) (G := G)
    let Q := G ⧸ Subgroup.center G
    ∀ x : Fin m → ℝ,
      QuotientGroup.mk (nativeOrderedExponentialCoordinates (I := I) (G := G) u x) =
        nativeOrderedExponentialCoordinates (I := 𝓘(ℝ, F)) (G := Q)
          (fun i => nativeCenterQuotientProjection (I := I) (G := G) (u i)) x := by
  letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
  letI := nativeCenterQuotient_t2Space (I := I) (G := G)
  letI := nativeCenterQuotient_lieGroup (I := I) (G := G)
  dsimp only
  intro x
  change (QuotientGroup.mk' (Subgroup.center G))
    (nativeOrderedExponentialCoordinates (I := I) (G := G) u x) = _
  simp only [nativeOrderedExponentialCoordinates, map_list_prod, List.map_ofFn,
    Function.comp_def]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext i
  simpa only [map_smul, QuotientGroup.mk'_apply] using
    nativeCenterQuotient_nativeExponential_projection (I := I) (G := G) (x i • u i)

end Hindman168
