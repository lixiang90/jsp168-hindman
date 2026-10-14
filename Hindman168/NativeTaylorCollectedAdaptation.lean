import Hindman168.NativeTaylorDescentCorrection
import Hindman168.RoughVectorMonomialCollection
import Hindman168.RoughVectorCoefficientEvaluationEquality

/-! Recover a genuine weighted source from actual ordered Taylor-layer
memberships. The recovered source is the collected ORIGINAL logarithmic
polynomial; cancellation of list terms is retained rather than assumed
termwise. This is the bridge needed after single-level kernel correction. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeTaylorOrderedLog {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) :
    ℕ → RoughVectorMvPolynomial Unit D.E
  | 0 => []
  | j+1 => roughNativeProductMvPolynomial (I := D.I) (G := D.G)
      (nativeTaylorOrderedLog D p j)
      (nativeTaylorBinomialVector D j 1
        (roughVectorMvEval (adaptedTaylorResidual D p j) (fun _ => (j : ℝ))))

theorem native_taylor_ordered_log_exponential {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) (b : ℝ) (n : ℕ) :
    nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) (nativeTaylorOrderedLog D p n) (fun _ => b)) =
      adaptedTaylorOrderedProduct D p b n := by
  induction n with
  | zero =>
      simp only [nativeTaylorOrderedLog, roughVectorMvEval, List.map_nil, List.sum_nil,
        adaptedTaylorOrderedProduct]
      exact nativeLieExponential_zero (E := D.E) (I := D.I) (G := D.G)
  | succ n ih =>
      rw [nativeTaylorOrderedLog, roughNativeProductMvPolynomial_eval,
        nativeLieExponential_globalLogarithm, ih, native_taylor_binomial_vector_eval]
      simp only [one_mul, adaptedTaylorOrderedProduct, adaptedTaylorFactor]

theorem native_taylor_ordered_log_weighted {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (n : ℕ)
    (h : ∀ j : ℕ, j < n → roughVectorMvEval (adaptedTaylorResidual D p j)
      (fun _ => (j : ℝ)) ∈ F.layer j) :
    RoughVectorMvWeightedDegree F.layer (nativeTaylorOrderedLog D p n) 0 := by
  induction n with
  | zero => exact fun _ ha => False.elim (List.not_mem_nil ha)
  | succ n ih =>
      exact native_rational_subgroup_product_weighted D F
        (ih (fun j hj => h j (by omega)))
        (native_taylor_binomial_vector_weighted D F n 1 (h n (by omega)))

theorem native_taylor_collected_adaptation_of_layers {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F J : NativeRationalSubgroupFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (h : ∀ j : ℕ, j ≤ ℓ → roughVectorMvEval (adaptedTaylorResidual D p j)
      (fun _ => (j : ℝ)) ∈ J.layer j) :
    RoughVectorMvWeightedDegree J.layer (roughVectorMvCollect p) 0 := by
  have hw := native_taylor_ordered_log_weighted D J p (ℓ+1) (fun j hj => h j (by omega))
  have he : ∀ x : Unit → ℝ, roughVectorMvEval (nativeTaylorOrderedLog D p (ℓ+1)) x =
      roughVectorMvEval p x := by
    intro x
    have hx : x = (fun _ => x ()) := by funext t; cases t; rfl
    rw [hx]
    apply nativeLieExponential_injective (E := D.E) (I := D.I) (G := D.G)
    exact (native_taylor_ordered_log_exponential D p (x ()) (ℓ+1)).trans
      (native_rational_subgroup_taylor_ordered_representation D F p hp (x ())).symm
  have hc (I : Unit →₀ ℕ) : roughVectorMvCoefficient (nativeTaylorOrderedLog D p (ℓ+1)) I =
      roughVectorMvCoefficient p I := by
    have hc' := rough_vector_coefficient_difference_of_eval (nativeTaylorOrderedLog D p (ℓ+1)) p []
      (fun x => by simpa only [roughVectorMvEval, List.map_nil, List.sum_nil, sub_zero] using he x) I
    simpa only [roughVectorMvCoefficient, List.map_nil, List.sum_nil, sub_zero] using hc'
  intro a ha
  obtain ⟨I, _, rfl⟩ := List.mem_map.mp ha
  rw [MvPolynomial.totalDegree_monomial I one_ne_zero, ← hc I]
  exact rough_vector_weighted_coefficient J.layer J.antitone hw I

end Hindman168
