import Hindman168.NativeFourierPairObservable

/-! The ACTUAL same-frequency conjugate pair is invariant under ORIGINAL
diagonal center action, from true original eigencharacters of modulus one. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u

theorem native_fourier_pair_diagonal_invariant {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (k : nativeNilmanifoldCenterIndex D → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (F : C(D.G ⧸ D.Γ, ℂ)) (z : Subgroup.center D.G)
      (q : (D.G × D.G) ⧸ D.Γ.prod D.Γ),
      nativeFourierPairObservable D k F (((z : D.G),(z : D.G)) • q) = nativeFourierPairObservable D k F q := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F z q
  rw [native_fourier_pair_observable_apply,native_fourier_pair_observable_apply,
    product_coset_map_diagonal_action]
  rw [← native_nilmanifold_central_action_mk D z,← native_nilmanifold_central_action_mk D z,
    native_central_fourier_projection_equivariant,native_central_fourier_projection_equivariant]
  let c := UnitAddTorus.mFourier k (nativeCenterTorusProjection (I := D.I) D.Γ z)
  have hc : c * star c = 1 := by
    rw [Complex.star_def,Complex.mul_conj',unit_torus_fourier_point_norm]
    norm_num
  change (c * _) * star (c * _) = _
  rw [star_mul]
  calc
    _ = (c * star c) * (nativeCentralFourierProjection D k F (productCosetMap D.Γ D.Γ q).1 *
      star (nativeCentralFourierProjection D k F (productCosetMap D.Γ D.Γ q).2)) := by ring
    _ = _ := by rw [hc,one_mul]

theorem native_fourier_pair_subgroup_invariant {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (k : nativeNilmanifoldCenterIndex D → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (F : C(D.G ⧸ D.Γ, ℂ)) (z : diagonalCenterSubgroup D.G)
      (q : (D.G × D.G) ⧸ D.Γ.prod D.Γ),
      nativeFourierPairObservable D k F ((z : D.G × D.G) • q) = nativeFourierPairObservable D k F q := by
  intro F z q
  obtain ⟨a,ha⟩ := (diagonal_center_mem_iff D.G (z : D.G × D.G)).mp z.property
  rw [ha]
  exact native_fourier_pair_diagonal_invariant D k F a q

end Hindman168
