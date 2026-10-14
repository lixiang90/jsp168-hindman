import Hindman168.RoughNativeSubgroupLogPolynomial

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_nilmanifold_log_transfer {σ : Type*} {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (S : LieSubalgebra ℝ (GroupLieAlgebra D.I D.G))
    (hS : nativeLatticeRationalSubspace (E := D.E) (I := D.I) D.Γ (nativeLieSubalgebraModel S))
    (v : D.E) (hv : v ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ)
    (p : RoughVectorMvPolynomial σ D.E) (d : ℕ) (hd : RoughVectorMvDegreeLE p d) :
    let N := roughNativeSubgroupNilmanifold D S hS v hv
    ∀ Q : (σ → ℝ) → N.G,
      (∀ x, roughVectorMvEval p x = nativeLieGlobalLogarithm (E := D.E) (I := D.I)
        (G := D.G) (Q x).val) →
      ∃ q : RoughVectorMvPolynomial σ N.E, RoughVectorMvDegreeLE q d ∧
        ∀ x, roughVectorMvEval q x = nativeLieGlobalLogarithm (E := N.E) (I := N.I) (Q x) := by
  intro N Q hp
  refine ⟨roughNativeSubgroupLogPolynomial S p, roughNativeSubgroupLogPolynomial_degree S hd, ?_⟩
  exact roughNativeSubgroupLogPolynomial_eval S p Q hp

theorem rough_native_nilmanifold_scalar_coordinates {σ : Type*} {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (S : LieSubalgebra ℝ (GroupLieAlgebra D.I D.G))
    (hS : nativeLatticeRationalSubspace (E := D.E) (I := D.I) D.Γ (nativeLieSubalgebraModel S))
    (v : D.E) (hv : v ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ)
    (p : RoughVectorMvPolynomial σ D.E) (d : ℕ) (hd : RoughVectorMvDegreeLE p d) :
    let N := roughNativeSubgroupNilmanifold D S hS v hv
    ∀ Q : (σ → ℝ) → N.G,
      (∀ x, roughVectorMvEval p x = nativeLieGlobalLogarithm (E := D.E) (I := D.I)
        (G := D.G) (Q x).val) →
      ∀ ell : N.E →ₗ[ℝ] ℝ, ∃ q : MvPolynomial σ ℝ, q.totalDegree ≤ d ∧
        ∀ x, MvPolynomial.eval x q = ell (nativeLieGlobalLogarithm (E := N.E) (I := N.I) (Q x)) := by
  intro N Q hp ell
  obtain ⟨q, hq, he⟩ := rough_native_nilmanifold_log_transfer D S hS v hv p d hd Q hp
  refine ⟨roughVectorMvProjection ell q, roughVectorMvProjection_degree ell hq, ?_⟩
  intro x
  rw [roughVectorMvProjection_eval, he x]

end Hindman168
