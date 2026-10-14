import Hindman168.RoughVectorCoefficientSubmodule
import Hindman168.ScalarUnitPolynomial
import Hindman168.NativeOriginalLinearOrbitAdapted

/-! The Taylor-coordinate layer argument in 07_cube_limits.tex 246--256.
Initial integer zeros force the entire residual into the next genuine
layer. Scalar projection to the quotient verifies this without assuming
a Taylor representation or group-valued finite difference identity. -/
namespace Hindman168
open Polynomial
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem rough_vector_weighted_initial_zeros_mem {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℕ → Submodule ℝ E) (hF : Antitone F)
    (p : RoughVectorMvPolynomial Unit E) (hp : RoughVectorMvWeightedDegree F p 0)
    (j : ℕ) (hj : 0 < j)
    (hz : ∀ m : ℕ, m < j → roughVectorMvEval p (fun _ => (m : ℝ)) = 0)
    (b : ℝ) : roughVectorMvEval p (fun _ => b) ∈ F j := by
  apply (Submodule.Quotient.mk_eq_zero (F j)).mp
  apply (Module.forall_dual_apply_eq_zero_iff ℝ _).mp
  intro φ
  let ell : E →ₗ[ℝ] ℝ := φ.comp (F j).mkQ
  let P := scalarUnitPolynomial (roughVectorMvProjection ell p)
  have hc : ∀ k : ℕ, j ≤ k → P.coeff k = 0 := by
    intro k hk
    rw [scalar_unit_polynomial_coefficient, ← rough_vector_coefficient_projection]
    have h := rough_vector_weighted_coefficient F hF hp (Finsupp.single () k)
    have hs : (Finsupp.single () k).sum (fun _ m => m) = k := by simp
    rw [hs, Nat.add_zero] at h
    have hm := hF hk h
    change φ ((F j).mkQ (roughVectorMvCoefficient p (Finsupp.single () k))) = 0
    have hq : (F j).mkQ (roughVectorMvCoefficient p (Finsupp.single () k)) = 0 :=
      (Submodule.Quotient.mk_eq_zero (F j)).mpr hm
    rw [hq, map_zero]
  have hd : P.natDegree ≤ j-1 := Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    (fun k hk => hc k (by omega))
  have hi : Function.Injective (fun k : Fin j => (k.val : ℝ)) := by
    intro k l h
    apply Fin.ext
    exact Nat.cast_injective h
  have hv : ∀ k : Fin j, P.eval (k.val : ℝ) = 0 := by
    intro k
    rw [scalar_unit_polynomial_eval, roughVectorMvProjection_eval, hz k.val k.isLt, map_zero]
  have hzero : P = 0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P hi hv
    (by simpa only [Fintype.card_fin] using (hd.trans_lt (by omega : j-1 < j)))
  change ell (roughVectorMvEval p (fun _ => b)) = 0
  rw [← roughVectorMvProjection_eval, ← scalar_unit_polynomial_eval]
  change P.eval b = 0
  rw [hzero, Polynomial.eval_zero]

theorem native_original_adapted_initial_zeros_mem {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E)
    (hp : RoughVectorMvWeightedDegree
      (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) 1) p 0)
    (j : ℕ) (hj : 0 < j)
    (hz : ∀ m : ℕ, m < j →
      roughVectorMvEval p (fun _ => (m : ℝ)) = 0) (b : ℝ) :
    nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) p (fun _ => b)) ∈ nilLowerCentralFiltration D.G j := by
  have hm := rough_vector_weighted_initial_zeros_mem _
    (rough_native_stretched_lie_antitone 1 (by omega)) p hp j hj hz b
  have he := (rough_native_stretched_filtration_exp_mem_iff (I := D.I) 1 j _).mpr hm
  rwa [native_original_unstretched_group_layer] at he

end Hindman168
