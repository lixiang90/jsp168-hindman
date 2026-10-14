import Hindman168.NativeRationalSubgroupFiltration
import Hindman168.NativeRationalLayerOrbit

/-! Weighted degree permits high-degree terms with zero vector coefficient.
Actual filtering removes exactly such terms, with an all-real equality and
unchanged weighted membership, before applying the ordinary-degree inverse. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def roughVectorMvDegreeTruncate {σ E : Type*}
    (p : RoughVectorMvPolynomial σ E) (d : ℕ) : RoughVectorMvPolynomial σ E :=
  p.filter (fun a => a.1.totalDegree ≤ d)

theorem rough_vector_degree_truncate_degree {σ E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (p : RoughVectorMvPolynomial σ E) (d : ℕ) :
    RoughVectorMvDegreeLE (roughVectorMvDegreeTruncate p d) d := by
  intro a ha
  exact of_decide_eq_true (List.mem_filter.mp ha).2

theorem rough_vector_degree_truncate_eval {σ E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (p : RoughVectorMvPolynomial σ E) (d : ℕ)
    (hz : ∀ a ∈ p, d < a.1.totalDegree → a.2 = 0) (x : σ → ℝ) :
    roughVectorMvEval (roughVectorMvDegreeTruncate p d) x = roughVectorMvEval p x := by
  induction p with
  | nil => rfl
  | cons a p ih =>
      have htail : ∀ b ∈ p, d < b.1.totalDegree → b.2 = 0 :=
        fun b hb hd => hz b (List.mem_cons_of_mem a hb) hd
      have he := ih htail
      by_cases ha : a.1.totalDegree ≤ d
      · simpa [roughVectorMvDegreeTruncate,roughVectorMvEval,ha] using
          congrArg (fun v => MvPolynomial.eval x a.1 • a.2 + v) he
      · have ha0 := hz a List.mem_cons_self (by omega)
        simpa [roughVectorMvDegreeTruncate,roughVectorMvEval,ha,ha0] using he

theorem native_weighted_term_zero_above_terminal {s ℓ : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (p : RoughVectorMvPolynomial σ D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0) :
    ∀ a ∈ p, ℓ < a.1.totalDegree → a.2 = 0 := by
  intro a ha hd
  have hm : a.2 ∈ F.layer (ℓ+1) := F.antitone (by omega) (hp a ha)
  rwa [F.terminal,Submodule.mem_bot] at hm

theorem native_weighted_degree_truncate_eval {s ℓ : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (p : RoughVectorMvPolynomial σ D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (x : σ → ℝ) :
    roughVectorMvEval (roughVectorMvDegreeTruncate p ℓ) x = roughVectorMvEval (E := D.E) p x :=
  rough_vector_degree_truncate_eval p ℓ (native_weighted_term_zero_above_terminal D F p hp) x

theorem native_weighted_degree_truncate_weighted {s ℓ : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (p : RoughVectorMvPolynomial σ D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0) :
    RoughVectorMvWeightedDegree F.layer (roughVectorMvDegreeTruncate p ℓ) 0 := by
  intro a ha
  exact hp a (List.mem_filter.mp ha).1

theorem native_actual_subgroup_polynomial_log_coordinates {s ℓ : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (rho : D.G) (hRat : rho ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (p : RoughVectorMvPolynomial σ D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0) :
    ∃ q : RoughVectorMvPolynomial σ (nativeRationalLayerOrbitData D F 0 rho hRat).E,
      RoughVectorMvDegreeLE q ℓ ∧ ∀ x : σ → ℝ,
        nativeLieGlobalLogarithm (E := (nativeRationalLayerOrbitData D F 0 rho hRat).E)
          (I := (nativeRationalLayerOrbitData D F 0 rho hRat).I)
          (G := (nativeRationalLayerOrbitData D F 0 rho hRat).G)
          (nativeRationalSubgroupPolynomialOrbit D F p hp x) = roughVectorMvEval q x := by
  let S := nativeRationalSubgroupLayerAlgebra D F 0
  let t := roughVectorMvDegreeTruncate p ℓ
  let Q := nativeRationalSubgroupPolynomialOrbit D F p hp
  have hQ : ∀ x : σ → ℝ, roughVectorMvEval (E := D.E) t x =
      nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) (Q x).val := by
    intro x
    rw [native_rational_subgroup_polynomial_orbit_logarithm]
    exact native_weighted_degree_truncate_eval D F p hp x
  refine ⟨roughNativeSubgroupLogPolynomial S t,?_,?_⟩
  · exact roughNativeSubgroupLogPolynomial_degree S (rough_vector_degree_truncate_degree p ℓ)
  · intro x
    exact (roughNativeSubgroupLogPolynomial_eval S t Q hQ x).symm

end Hindman168
