import Hindman168.NativeTaylorDescentCoefficient
import Hindman168.NativeRationalSubgroupDescentBounds

/-! Actual one-step adaptation to the new SINGLE-LEVEL kernel filtration,
including j=1. The output is the collected, genuinely corrected source.
The integer/error decomposition is explicit; no sequence extraction or
bounded-error estimate is claimed here. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_taylor_kernel_corrected_source_adapted {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (hz : roughVectorMvEval p (fun _ => (0 : ℝ)) = 0)
    (j : ℕ) (hj : 1 ≤ j) (phi : D.E →ₗ[ℝ] ℝ)
    (hNext : F.layer (j+1) ≤ phi.ker)
    (hBracket : ∀ a b : ℕ, 0 < a → 0 < b → a+b=j →
      ∀ v ∈ F.layer a, ∀ w ∈ F.layer b,
        phi (nativeLieAdjointDifferential (I := D.I) (G := D.G) v w) = 0)
    (hRat : ∀ v ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ,
      ∃ q : ℚ, phi v = (q : ℝ))
    (epsilon : ℝ) (m : ℤ) {V : D.E} (hV : V ∈ F.layer j) (hphiV : phi V = 1)
    (hDecomp : phi (roughVectorMvEval (adaptedTaylorResidual D p j) (fun _ => (j : ℝ))) =
      (m : ℝ) + epsilon) :
    RoughVectorMvWeightedDegree
      (nativeRationalSubgroupLevelKernel D F j hj phi hNext hBracket hRat).layer
      (roughVectorMvCollect (nativeTaylorDescentCorrection D p j epsilon m V)) 0 := by
  let q := nativeTaylorDescentCorrection D p j epsilon m V
  have hq := native_taylor_descent_correction_weighted D F p hp j epsilon m hV
  apply native_taylor_collected_adaptation_of_layers D F _ q hq
  intro k _
  have hr := native_rational_subgroup_taylor_residual_properties D F q hq k
  have hc := native_rational_subgroup_taylor_initial_value_layer D F _ hr.1 k hr.2
  rw [native_rational_subgroup_level_kernel_layer]
  by_cases hk : k=j ∨ (j=1 ∧ k=0)
  · rw [if_pos hk]
    refine ⟨hc, ?_⟩
    change phi (roughVectorMvEval (adaptedTaylorResidual D q k) (fun _ => (k : ℝ))) = 0
    rcases hk with hk | ⟨_, hk⟩
    · subst k
      have he := native_taylor_descent_order_j_character D F p hp j phi hNext epsilon m hV hphiV
      rw [hDecomp] at he
      change phi (roughVectorMvEval (adaptedTaylorResidual D q j) (fun _ => (j : ℝ))) =
        (m : ℝ) + epsilon - epsilon - (m : ℝ) at he
      exact he.trans (by ring)
    · subst k
      have hcast : roughVectorMvEval p (fun _ => ((0 : ℕ) : ℝ)) = 0 := by
        simpa only [Nat.cast_zero] using hz
      have hq0 := (native_taylor_descent_correction_initial_values D p j epsilon m V
        (by omega : 0 < j)).trans hcast
      simp only [Nat.cast_zero] at hq0
      simp only [adaptedTaylorResidual, Nat.cast_zero]
      exact (congrArg phi hq0).trans phi.map_zero
  · rw [if_neg hk]
    exact hc

theorem native_taylor_kernel_corrected_source_normalized {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E)
    (hz : roughVectorMvEval p (fun _ => (0 : ℝ)) = 0)
    (j : ℕ) (hj : 1 ≤ j) (epsilon : ℝ) (m : ℤ) (V : D.E) :
    roughVectorMvEval (roughVectorMvCollect (nativeTaylorDescentCorrection D p j epsilon m V))
      (fun _ => (0 : ℝ)) = 0 := by
  rw [rough_vector_collect_eval]
  have hcast : roughVectorMvEval p (fun _ => ((0 : ℕ) : ℝ)) = 0 := by
    simpa only [Nat.cast_zero] using hz
  simpa only [Nat.cast_zero] using
    (native_taylor_descent_correction_initial_values D p j epsilon m V (by omega : 0 < j)).trans hcast

end Hindman168
