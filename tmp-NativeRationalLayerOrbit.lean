import Hindman168.NativeRationalSubgroupFiltration
import Hindman168.RoughNativeSubgroupNilmanifold
import Hindman168.RoughNativeSubgroupLogPolynomial

/-! Actual rational layer orbits for the final section-7 filtration.
The source group and its lattice are the ORIGINAL subgroup and the
intersection with the ORIGINAL conjugated lattice, with native geometry. -/
namespace Hindman168
open Set
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRationalLayerOrbitData {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (i : ℕ) (rho : D.G)
    (hRat : rho ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ) :
    NativeNilmanifoldData.{u} s :=
  roughNativeSubgroupNilmanifold D (nativeRationalSubgroupLayerAlgebra D F i) (F.rational i)
    (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) rho)
    ((nativeSubgroupRationalHull_mem_iff (E := D.E) (I := D.I) D.Γ rho).mp hRat)

theorem native_rational_layer_orbit_data_group {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (i : ℕ) (rho : D.G) (hRat : rho ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ) :
    (nativeRationalLayerOrbitData D F i rho hRat).G = nativeRationalSubgroupLayer D F i := rfl

theorem native_rational_layer_orbit_data_lattice {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (i : ℕ) (rho : D.G) (hRat : rho ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ) :
    (nativeRationalLayerOrbitData D F i rho hRat).Γ =
      (roughConjugateSubgroup D.Γ rho).comap (nativeRationalSubgroupLayer D F i).subtype := by
  change (roughConjugateSubgroup D.Γ
    (nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) rho))).comap _ = _
  rw [nativeLieExponential_globalLogarithm]
  rfl

theorem native_rational_layer_orbit_compact {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (i : ℕ) (rho : D.G) (hRat : rho ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ) :
    CompactSpace ((nativeRationalSubgroupLayer D F i) ⧸
      (roughConjugateSubgroup D.Γ rho).comap (nativeRationalSubgroupLayer D F i).subtype) := by
  have h := (nativeRationalLayerOrbitData D F i rho hRat).quotientCompact
  rw [native_rational_layer_orbit_data_lattice] at h
  exact h

noncomputable def nativeRationalSubgroupPolynomialOrbit {s ℓ : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (p : RoughVectorMvPolynomial σ D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (x : σ → ℝ) : nativeRationalSubgroupLayer D F 0 :=
  ⟨nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) p x),
    native_rational_subgroup_layer_exp_mem D F 0
      (rough_vector_weighted_eval (E := D.E) F.layer F.antitone hp x)⟩

theorem native_rational_subgroup_polynomial_orbit_original {s ℓ : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (p : RoughVectorMvPolynomial σ D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (x : σ → ℝ) :
    (nativeRationalSubgroupPolynomialOrbit D F p hp x : D.G) =
      nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) p x) := rfl

theorem native_rational_subgroup_polynomial_orbit_logarithm {s ℓ : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (p : RoughVectorMvPolynomial σ D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (x : σ → ℝ) :
    nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
      (nativeRationalSubgroupPolynomialOrbit D F p hp x : D.G) = roughVectorMvEval (E := D.E) p x := by
  rw [native_rational_subgroup_polynomial_orbit_original]
  exact nativeLieGlobalLogarithm_exponential (E := D.E) (I := D.I) (G := D.G) _

end Hindman168
