import Hindman168.NativeResidueCubeFaceEscape
import Hindman168.CubeTaylorNoCancellation

/-! The explicit scalar Taylor/face expansion has an escaping coefficient
for each actual residue-cube horizontal obstruction. The equality with the
horizontal projection of the actual group-valued cube still needs proof. -/
namespace Hindman168
open Filter
open scoped Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeResidueCubeTaylorScalarPolynomial {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (chi : (nativeResidueCubeData D F ρ hρ d n e).E →ₗ[ℝ] ℝ)
    (p : RoughVectorMvPolynomial Unit D.E) : MvPolynomial (Option (Fin d)) ℝ :=
  cubeTaylorFaceScalarPolynomial (ℓ+1) (fun k A =>
    nativeResidueCubeFaceFunctional D F ρ hρ d n e chi A
      (roughVectorMvEval (adaptedTaylorResidual D p k) (fun _ => (k : ℝ))))

theorem native_residue_cube_scalar_coefficient_escape {s ℓ : ℕ}
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
      (∀ m, MvPolynomial.coeff (cubeIsolatedMonomial j A)
        (nativeResidueCubeTaylorScalarPolynomial D F ρ hρ d n e chi (p m)) =
          nativeResidueCubeFaceFunctional D F ρ hρ d n e chi A
            (roughVectorMvEval (adaptedTaylorResidual D (p m) j) (fun _ => (j : ℝ))) /
              ((j - A.card).factorial : ℝ)) ∧
      ∀ q : ℚ, q ≠ 0 → Tendsto (fun m => (L m)^j *
        ‖(((q : ℝ) * MvPolynomial.coeff (cubeIsolatedMonomial j A)
          (nativeResidueCubeTaylorScalarPolynomial D F ρ hρ d n e chi (p m)) : ℝ) : UnitAddCircle)‖)
        atTop atTop := by
  obtain ⟨j,hj,hjTop,A,hA,hLevel,hTail,hEsc⟩ :=
    native_residue_cube_face_taylor_escape D F ρ hρ d n e chi hChi L p hIrr
  have hc (m : ℕ) : MvPolynomial.coeff (cubeIsolatedMonomial j A)
      (nativeResidueCubeTaylorScalarPolynomial D F ρ hρ d n e chi (p m)) =
        nativeResidueCubeFaceFunctional D F ρ hρ d n e chi A
          (roughVectorMvEval (adaptedTaylorResidual D (p m) j) (fun _ => (j : ℝ))) /
            ((j - A.card).factorial : ℝ) := by
    apply cube_taylor_face_scalar_isolated_coefficient (ℓ+1) j A _ hA (by omega)
    intro k hk _ B hB
    have hr := native_rational_subgroup_taylor_residual_properties D F (p m) (hp m) k
    exact hTail k hk B hB
      (native_rational_subgroup_taylor_initial_value_layer D F _ hr.1 k hr.2)
  refine ⟨j,hj,hjTop,A,hA,hLevel,hc,?_⟩
  intro q hq
  simpa only [hc] using hEsc q hq

end Hindman168
