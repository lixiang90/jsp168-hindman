import Hindman168.NativeLinearStepPolynomial
import Hindman168.NativeCentralPolynomialProjection
import Hindman168.NativeCompactCosetRepresentatives
import Mathlib.Topology.Order.Compact

/-! Exact original nonnormal coset samples and ONE FIXED compact bounded
set for the true first value P(1), after an actual right lattice correction. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_linear_step_zero_exponential {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) (γ : D.G) :
    nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) (nativeLinearStepPolynomial D p γ) (fun _ => 0)) =
        nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
          (roughVectorMvEval (E := D.E) p (fun _ => 0)) := by
  simpa only [Int.cast_zero,neg_zero,zpow_zero,mul_one] using
    native_linear_step_integer_exponential D p γ 0

theorem native_linear_step_one_exponential {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) (a γ : D.G)
    (h : nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) p (fun _ => 1)) = a*γ) :
    nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) (nativeLinearStepPolynomial D p γ) (fun _ => 1)) = a := by
  have he := native_linear_step_integer_exponential D p γ 1
  simpa only [Int.cast_one,zpow_neg_one,h,mul_inv_cancel_right] using he

theorem native_linear_step_original_orbit {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) (γ : D.Γ) (x : Unit → ℤ) :
    nativeMvPolynomialOrbit D (nativeLinearStepPolynomial D p γ) x = nativeMvPolynomialOrbit D p x := by
  have hx : (fun _ : Unit => (x () : ℝ)) = (fun j => (x j : ℝ)) :=
    funext (fun j => congrArg (fun k => (x k : ℝ)) (Subsingleton.elim () j))
  have he := native_linear_step_integer_exponential D p γ (x ())
  rw [hx] at he
  change (QuotientGroup.mk (nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
    (roughVectorMvEval (E := D.E) (nativeLinearStepPolynomial D p γ) (fun j => (x j : ℝ)))) : D.G ⧸ D.Γ) = _
  rw [he]
  apply QuotientGroup.eq.mpr
  rw [mul_inv_rev,mul_assoc,inv_mul_cancel,mul_one]
  exact D.Γ.inv_mem (D.Γ.zpow_mem γ.property (-x ()))

theorem native_linear_step_fixed_compact_representatives {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) :
    ∃ K : Set D.G, IsCompact K ∧ ∃ B : ℝ, 0 ≤ B ∧
      (∀ a ∈ K, ‖nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) a‖ ≤ B) ∧
      ∀ p : RoughVectorMvPolynomial Unit D.E, ∃ a ∈ K, ∃ γ : D.Γ,
        nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
          (roughVectorMvEval (E := D.E) p (fun _ => 1)) = a*γ ∧
        nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
          (roughVectorMvEval (E := D.E) (nativeLinearStepPolynomial D p γ) (fun _ => 1)) = a := by
  obtain ⟨K,hK,hRep⟩ := native_exists_compact_coset_representatives D
  obtain ⟨b,hb⟩ := hK.bddAbove_image
    ((nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)).continuous.norm.continuousOn)
  refine ⟨K,hK,max b 0,le_max_right _ _,?_,?_⟩
  · intro a ha
    exact (hb (Set.mem_image_of_mem _ ha)).trans (le_max_left _ _)
  · intro p
    obtain ⟨a,ha,γ,he⟩ := hRep
      (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) p (fun _ => 1)))
    exact ⟨a,ha,γ,he,native_linear_step_one_exponential D p a γ he⟩

end Hindman168
