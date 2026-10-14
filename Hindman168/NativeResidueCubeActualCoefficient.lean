import Hindman168.NativeResidueCubeSourcePolynomial

/-! The isolated escaping coefficient belongs to the horizontal projection
of the ACTUAL adapted rational-residue cube, with ORIGINAL source vertices. -/
namespace Hindman168
open Filter
open scoped Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem cube_taylor_face_scalar_degree {d : ℕ} (N j : ℕ)
    (c : ℕ → Finset (Fin d) → ℝ)
    (hTail : ∀ k, j < k → k < N → ∀ A : Finset (Fin d), A.card ≤ k → c k A = 0) :
    (cubeTaylorFaceScalarPolynomial N c).totalDegree ≤ j := by
  unfold cubeTaylorFaceScalarPolynomial
  apply MvPolynomial.totalDegree_finsetSum_le
  intro k hk
  apply MvPolynomial.totalDegree_finsetSum_le
  intro A _
  by_cases hkj : k ≤ j
  · exact (MvPolynomial.totalDegree_mul _ _).trans
      (by simpa only [MvPolynomial.totalDegree_C, Nat.zero_add] using
        (cube_binomial_face_degree k A).trans hkj)
  · by_cases hA : A.card ≤ k
    · rw [hTail k (by omega) (Finset.mem_range.mp hk) A hA, map_zero, zero_mul]
      exact Nat.zero_le _
    · rw [cube_binomial_face_eq_zero k A (by omega), mul_zero]
      exact Nat.zero_le _

theorem native_residue_cube_source_projection_degree {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (chi : (nativeResidueCubeData D F ρ hρ d n e).E →ₗ[ℝ] ℝ)
    (hChi : RoughNativeHorizontalFunctional (I := (nativeResidueCubeData D F ρ hρ d n e).I)
      (nativeResidueCubeData D F ρ hρ d n e).Γ chi) (j : ℕ)
    (hTail : ∀ k : ℕ, j < k → ∀ A : Finset (Fin d), A.card ≤ k →
      F.layer k ≤ (nativeResidueCubeFaceFunctional D F ρ hρ d n e chi A).ker) :
    (roughVectorMvProjection chi (nativeResidueCubeSourcePolynomial D F ρ hρ d n e p hp)).totalDegree ≤ j := by
  rw [native_residue_cube_source_projection D F ρ hρ d n e p hp chi hChi]
  apply cube_taylor_face_scalar_degree (ℓ+1) j
  intro k hk _ A hA
  have hr := native_rational_subgroup_taylor_residual_properties D F p hp k
  exact hTail k hk A hA
    (native_rational_subgroup_taylor_initial_value_layer D F _ hr.1 k hr.2)

theorem native_residue_cube_actual_coefficient_escape {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (chi : (nativeResidueCubeData D F ρ hρ d n e).E →ₗ[ℝ] ℝ)
    (hChi : RoughNativeHorizontalFunctional (I := (nativeResidueCubeData D F ρ hρ d n e).I)
      (nativeResidueCubeData D F ρ hρ d n e).Γ chi)
    (L : ℕ → ℝ) (p : ℕ → RoughVectorMvPolynomial Unit D.E)
    (hp : ∀ m, RoughVectorMvWeightedDegree F.layer (p m) 0)
    (hIrr : NativeSubgroupSequentialIrrational D F L p) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ ℓ ∧ ∃ A : Finset (Fin d), A.card ≤ j ∧
      NativeSubgroupRationalLevelCharacter D F j (nativeResidueCubeFaceFunctional D F ρ hρ d n e chi A) ∧
      (∀ m, (roughVectorMvProjection chi
        (nativeResidueCubeSourcePolynomial D F ρ hρ d n e (p m) (hp m))).totalDegree ≤ j) ∧
      (∀ m, MvPolynomial.coeff (cubeIsolatedMonomial j A)
        (roughVectorMvProjection chi (nativeResidueCubeSourcePolynomial D F ρ hρ d n e (p m) (hp m))) =
          nativeResidueCubeFaceFunctional D F ρ hρ d n e chi A
            (roughVectorMvEval (adaptedTaylorResidual D (p m) j) (fun _ => (j : ℝ))) /
              ((j - A.card).factorial : ℝ)) ∧
      ∀ q : ℚ, q ≠ 0 → Tendsto (fun m => (L m)^j *
        ‖(((q : ℝ) * MvPolynomial.coeff (cubeIsolatedMonomial j A)
          (roughVectorMvProjection chi (nativeResidueCubeSourcePolynomial D F ρ hρ d n e (p m) (hp m))) : ℝ) : UnitAddCircle)‖)
        atTop atTop := by
  obtain ⟨j,hj,hjTop,A,hA,hLevel,hTail,hEsc⟩ :=
    native_residue_cube_face_taylor_escape D F ρ hρ d n e chi hChi L p hIrr
  have hc (m : ℕ) : MvPolynomial.coeff (cubeIsolatedMonomial j A)
      (roughVectorMvProjection chi (nativeResidueCubeSourcePolynomial D F ρ hρ d n e (p m) (hp m))) =
        nativeResidueCubeFaceFunctional D F ρ hρ d n e chi A
          (roughVectorMvEval (adaptedTaylorResidual D (p m) j) (fun _ => (j : ℝ))) /
            ((j - A.card).factorial : ℝ) := by
    rw [native_residue_cube_source_projection D F ρ hρ d n e (p m) (hp m) chi hChi]
    apply cube_taylor_face_scalar_isolated_coefficient (ℓ+1) j A _ hA (by omega)
    intro k hk _ B hB
    have hr := native_rational_subgroup_taylor_residual_properties D F (p m) (hp m) k
    exact hTail k hk B hB
      (native_rational_subgroup_taylor_initial_value_layer D F _ hr.1 k hr.2)
  refine ⟨j,hj,hjTop,A,hA,hLevel,?_,hc,?_⟩
  · intro m
    exact native_residue_cube_source_projection_degree D F ρ hρ d n e (p m) (hp m) chi hChi j hTail
  · intro q hq
    simpa only [hc] using hEsc q hq

end Hindman168
