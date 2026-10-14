import Hindman168.NativeResidueCubeSpatialSource

/-! A single threshold excludes every character in a fixed finite obstruction
list, uniformly in translations and the unused parameter, at any fixed rational step. -/
namespace Hindman168
open Filter
open scoped Manifold ContDiff Topology BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_residue_cube_finite_affine_escape {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (L : ℕ → ℝ) (p : ℕ → RoughVectorMvPolynomial Unit D.E)
    (hp : ∀ m, RoughVectorMvWeightedDegree F.layer (p m) 0)
    (hIrr : NativeSubgroupSequentialIrrational D F L p)
    (S : Finset ((nativeResidueCubeData D F ρ hρ d n e).E →ₗ[ℝ] ℝ))
    (hS : ∀ chi ∈ S, RoughNativeHorizontalFunctional (I := (nativeResidueCubeData D F ρ hρ d n e).I)
      (nativeResidueCubeData D F ρ hρ d n e).Γ chi)
    (t : ℚ) (ht : t ≠ 0) (C : ℝ) :
    ∀ᶠ m in atTop, ∀ chi ∈ S, ∃ J : Fin (d+1) → ℕ,
      0 < (∑ i, J i) ∧ (∑ i, J i) ≤ ℓ ∧ ∀ z : ℝ, ∀ b : Fin (d+1) → ℝ,
        C < (L m)^(∑ i, J i) *
          ‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm J)
            (roughMvAffineSubstitution b (fun _ => (t : ℝ))
              (roughScalarSpatialProjection chi
                (nativeResidueCubeSpatialPolynomial D F ρ hρ d n e (p m) (hp m)) z)) : ℝ) : UnitAddCircle)‖ := by
  classical
  apply (Filter.eventually_all_finset S).mpr
  intro chi hchi
  obtain ⟨j,hj,hjTop,A,hA,_hLevel,hdeg,_hc,hEsc⟩ :=
    native_residue_cube_actual_coefficient_escape D F ρ hρ d n e chi (hS chi hchi) L p hp hIrr
  have hE := hEsc (t^j) (pow_ne_zero _ ht)
  filter_upwards [hE.eventually_gt_atTop C] with m hm
  have hweight := cube_spatial_monomial_weight j A hA
  have hindex : Finsupp.equivFunOnFinite.symm (fun i => cubeSpatialMonomial j A i) =
      cubeSpatialMonomial j A := by ext i; simp
  refine ⟨fun i => cubeSpatialMonomial j A i, by rw [hweight]; omega,
    by rw [hweight]; exact hjTop, ?_⟩
  intro z b
  rw [hweight, hindex, native_residue_cube_spatial_top_coefficient D F ρ hρ d n e
    (p m) (hp m) chi j A hA (hdeg m) z b (t : ℝ)]
  simpa only [Rat.cast_pow] using hm

end Hindman168
