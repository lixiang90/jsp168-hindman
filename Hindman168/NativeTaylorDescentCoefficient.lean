import Hindman168.NativeTaylorCollectedAdaptation
import Hindman168.NativeSubgroupLevelAffine

/-! The corrected order-j coefficient's EXACT real character value.
Lower Taylor factors are conjugated explicitly; their error lies in the
next layer. No small circle norm is used to infer real cancellation. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_taylor_descent_ordered_prefix_unchanged {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E)
    (j : ℕ) (epsilon : ℝ) (m : ℤ) (V : D.E) (b : ℝ) (n : ℕ) (hn : n ≤ j) :
    adaptedTaylorOrderedProduct D (nativeTaylorDescentCorrection D p j epsilon m V) b n =
      adaptedTaylorOrderedProduct D p b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hnj : n < j := by omega
      have hc := native_taylor_descent_lower_coefficients_unchanged D p j epsilon m V hnj
      have hf : adaptedTaylorFactor D
          (adaptedTaylorResidual D (nativeTaylorDescentCorrection D p j epsilon m V) n) n b =
        adaptedTaylorFactor D (adaptedTaylorResidual D p n) n b := by
        exact congrArg (fun v : D.E => nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
          (MvPolynomial.eval (fun _ => b) (adaptedTaylorBinomial n) • v)) hc
      exact congrArg₂ (fun a c : D.G => a*c) (ih (by omega)) hf

theorem native_taylor_ordered_prefix_mem {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (b : ℝ) (n : ℕ) : adaptedTaylorOrderedProduct D p b n ∈ nativeRationalSubgroupLayer D F 0 := by
  induction n with
  | zero => exact (nativeRationalSubgroupLayer D F 0).one_mem
  | succ n ih =>
      have hr := native_rational_subgroup_taylor_residual_properties D F p hp n
      have hc := native_rational_subgroup_taylor_initial_value_layer D F _ hr.1 n hr.2
      exact (nativeRationalSubgroupLayer D F 0).mul_mem ih
        (native_rational_subgroup_layer_exp_mem D F 0
          ((F.layer 0).smul_mem _ (F.antitone (Nat.zero_le n) hc)))

theorem native_taylor_descent_order_j_character {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (j : ℕ) (phi : D.E →ₗ[ℝ] ℝ) (hNext : F.layer (j+1) ≤ phi.ker)
    (epsilon : ℝ) (m : ℤ) {V : D.E} (hV : V ∈ F.layer j) (hphiV : phi V = 1) :
    phi (roughVectorMvEval (adaptedTaylorResidual D
      (nativeTaylorDescentCorrection D p j epsilon m V) j) (fun _ => (j : ℝ))) =
      phi (roughVectorMvEval (adaptedTaylorResidual D p j) (fun _ => (j : ℝ))) - epsilon - (m : ℝ) := by
  let exp : D.E → D.G := nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
  let log : D.G → D.E := nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
  let q := nativeTaylorDescentCorrection D p j epsilon m V
  let H := adaptedTaylorOrderedProduct D p (j : ℝ) j
  let a := roughVectorMvEval (adaptedTaylorResidual D p j) (fun _ => (j : ℝ))
  let a' := roughVectorMvEval (adaptedTaylorResidual D q j) (fun _ => (j : ℝ))
  let u := (-epsilon) • V
  let w := (-(m : ℝ)) • V
  let C := H⁻¹ * exp u * H
  have hu : u ∈ F.layer j := (F.layer j).smul_mem _ hV
  have hw : w ∈ F.layer j := (F.layer j).smul_mem _ hV
  have hr := native_rational_subgroup_taylor_residual_properties D F p hp j
  have ha : a ∈ F.layer j := native_rational_subgroup_taylor_initial_value_layer D F _ hr.1 j hr.2
  have hH : log H ∈ F.layer 0 := (native_rational_subgroup_layer_logarithm_iff D F 0 H).mp
    (native_taylor_ordered_prefix_mem D F p hp (j : ℝ) j)
  have hC := native_subgroup_level_conjugate_character D F j phi hNext hH hu
  change log C ∈ F.layer j ∧ phi (log C) = phi u at hC
  have hRec := adapted_taylor_ordered_reconstruction D q (j : ℝ) j
  have hPrefix := native_taylor_descent_ordered_prefix_unchanged D p j epsilon m V (j : ℝ) j le_rfl
  rw [hPrefix] at hRec
  have hOld := adapted_taylor_ordered_reconstruction D p (j : ℝ) j
  have hCorr := native_taylor_descent_correction_exponential D p j epsilon m V (j : ℝ)
  simp only [adapted_taylor_binomial_eval_nat, Nat.choose_self, Nat.cast_one, mul_one] at hCorr
  have hProd : H * exp a' = exp u * (H * exp a) * exp w :=
    hRec.symm.trans (hCorr.trans (congrArg (fun g : D.G => exp u * g * exp w) hOld))
  have hExp : exp a' = C * exp a * exp w := by
    calc
      exp a' = H⁻¹ * (H * exp a') := by group
      _ = H⁻¹ * (exp u * (H * exp a) * exp w) := congrArg (fun g : D.G => H⁻¹*g) hProd
      _ = C * exp a * exp w := by dsimp only [C]; group
  have haLog : log (exp a) = a := nativeLieGlobalLogarithm_exponential (E := D.E) (I := D.I) (G := D.G) a
  have hwLog : log (exp w) = w := nativeLieGlobalLogarithm_exponential (E := D.E) (I := D.I) (G := D.G) w
  have hA : log (exp a) ∈ F.layer j := by rw [haLog]; exact ha
  have hW : log (exp w) ∈ F.layer j := by rw [hwLog]; exact hw
  have hFirst := native_subgroup_level_character_mul D F j phi hNext
    (F.antitone (Nat.zero_le j) hC.1) hA
  have hFirstMem : log (C * exp a) ∈ F.layer 0 := by
    apply (native_rational_subgroup_layer_logarithm_iff D F 0 _).mp
    exact (nativeRationalSubgroupLayer D F 0).mul_mem
      ((native_rational_subgroup_layer_logarithm_iff D F 0 C).mpr (F.antitone (Nat.zero_le j) hC.1))
      (native_rational_subgroup_layer_exp_mem D F 0 (F.antitone (Nat.zero_le j) ha))
  have hSecond := native_subgroup_level_character_mul D F j phi hNext hFirstMem hW
  have hValue : a' = log (C * exp a * exp w) :=
    (nativeLieGlobalLogarithm_exponential (E := D.E) (I := D.I) (G := D.G) a').symm.trans (congrArg log hExp)
  change phi a' = phi a - epsilon - (m : ℝ)
  rw [hValue]
  change phi (log (C * exp a * exp w)) = phi (log (C * exp a)) + phi (log (exp w)) at hSecond
  change phi (log (C * exp a)) = phi (log C) + phi (log (exp a)) at hFirst
  rw [hSecond, hFirst, hC.2, haLog, hwLog]
  simp only [u, w, map_smul, hphiV, smul_eq_mul, mul_one]
  ring

end Hindman168
