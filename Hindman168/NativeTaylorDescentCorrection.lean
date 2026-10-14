import Hindman168.NativeRationalSubgroupTaylorCoordinates

/-! Actual two-sided corrections from (7. filtration-descent), preserving the
OLD filtration and every lower Taylor coefficient. Membership in the new
kernel filtration still requires the order-j cancellation proof. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeTaylorBinomialVector {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (j : ℕ) (r : ℝ) (V : D.E) :
    RoughVectorMvPolynomial Unit D.E := [(adaptedTaylorBinomial j, r • V)]

theorem native_taylor_binomial_vector_eval {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (j : ℕ) (r : ℝ) (V : D.E) (b : ℝ) :
    roughVectorMvEval (E := D.E) (nativeTaylorBinomialVector D j r V) (fun _ => b) =
      (r * MvPolynomial.eval (fun _ => b) (adaptedTaylorBinomial j)) • V := by
  simp only [nativeTaylorBinomialVector, roughVectorMvEval, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, smul_smul, mul_comm]

theorem native_taylor_binomial_vector_weighted {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (j : ℕ) (r : ℝ) {V : D.E} (hV : V ∈ F.layer j) :
    RoughVectorMvWeightedDegree F.layer (nativeTaylorBinomialVector D j r V) 0 := by
  intro z hz
  obtain rfl := List.mem_singleton.mp hz
  apply F.antitone (by simpa only [Nat.add_zero] using adapted_taylor_binomial_degree j)
  exact (F.layer j).smul_mem r hV

noncomputable def nativeTaylorDescentCorrection {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E)
    (j : ℕ) (epsilon : ℝ) (m : ℤ) (V : D.E) : RoughVectorMvPolynomial Unit D.E :=
  roughVectorMvZeroTrim (roughNativeProductMvPolynomial (I := D.I) (G := D.G)
    (roughNativeProductMvPolynomial (I := D.I) (G := D.G)
      (nativeTaylorBinomialVector D j (-epsilon) V) p)
    (nativeTaylorBinomialVector D j (-(m : ℝ)) V))

theorem native_taylor_descent_correction_weighted {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (j : ℕ) (epsilon : ℝ) (m : ℤ) {V : D.E} (hV : V ∈ F.layer j) :
    RoughVectorMvWeightedDegree F.layer (nativeTaylorDescentCorrection D p j epsilon m V) 0 :=
  rough_vector_zero_trim_weighted _ (native_rational_subgroup_product_weighted D F
    (native_rational_subgroup_product_weighted D F
      (native_taylor_binomial_vector_weighted D F j (-epsilon) hV) hp)
    (native_taylor_binomial_vector_weighted D F j (-(m : ℝ)) hV))

theorem native_taylor_descent_correction_exponential {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E)
    (j : ℕ) (epsilon : ℝ) (m : ℤ) (V : D.E) (b : ℝ) :
    nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) (nativeTaylorDescentCorrection D p j epsilon m V) (fun _ => b)) =
    nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      ((-epsilon * MvPolynomial.eval (fun _ => b) (adaptedTaylorBinomial j)) • V) *
    nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) p (fun _ => b)) *
    nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      ((-(m : ℝ) * MvPolynomial.eval (fun _ => b) (adaptedTaylorBinomial j)) • V) := by
  rw [nativeTaylorDescentCorrection, rough_vector_zero_trim_eval,
    roughNativeProductMvPolynomial_eval, nativeLieExponential_globalLogarithm,
    roughNativeProductMvPolynomial_eval, nativeLieExponential_globalLogarithm,
    native_taylor_binomial_vector_eval, native_taylor_binomial_vector_eval]

theorem native_taylor_descent_correction_initial_values {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E)
    (j : ℕ) (epsilon : ℝ) (m : ℤ) (V : D.E) {n : ℕ} (hn : n < j) :
    roughVectorMvEval (E := D.E) (nativeTaylorDescentCorrection D p j epsilon m V) (fun _ => (n : ℝ)) =
      roughVectorMvEval p (fun _ => (n : ℝ)) := by
  apply nativeLieExponential_injective (E := D.E) (I := D.I) (G := D.G)
  change nativeLieExponential (E := D.E) (I := D.I) (G := D.G) _ =
    nativeLieExponential (E := D.E) (I := D.I) (G := D.G) _
  let exp := nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
  have hb : MvPolynomial.eval (fun _ => (n : ℝ)) (adaptedTaylorBinomial j) = 0 := by
    rw [adapted_taylor_binomial_eval_nat, Nat.choose_eq_zero_of_lt hn, Nat.cast_zero]
  have ha (r : ℝ) : (r * MvPolynomial.eval (fun _ => (n : ℝ)) (adaptedTaylorBinomial j)) • V = 0 := by
    rw [hb, mul_zero, zero_smul]
  have he0 : exp (0 : D.E) = 1 := nativeLieExponential_zero (E := D.E) (I := D.I) (G := D.G)
  have he1 := (congrArg exp (ha (-epsilon))).trans he0
  have he2 := (congrArg exp (ha (-(m : ℝ)))).trans he0
  have hg := congrArg₂ (fun z w : D.G => z * exp (roughVectorMvEval (E := D.E) p (fun _ => (n : ℝ))) * w) he1 he2
  exact (native_taylor_descent_correction_exponential D p j epsilon m V (n : ℝ)).trans
    (hg.trans (by simp only [one_mul, mul_one]; rfl))

theorem adapted_taylor_residual_initial_values_congr {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p q : RoughVectorMvPolynomial Unit D.E) (j : ℕ)
    (he : ∀ n : ℕ, n < j → roughVectorMvEval p (fun _ => (n : ℝ)) =
      roughVectorMvEval q (fun _ => (n : ℝ))) (k : ℕ) (hk : k ≤ j) :
    ∀ n : ℕ, n < j → roughVectorMvEval (adaptedTaylorResidual D p k) (fun _ => (n : ℝ)) =
      roughVectorMvEval (adaptedTaylorResidual D q k) (fun _ => (n : ℝ)) := by
  induction k with
  | zero => exact he
  | succ k ih =>
      intro n hn
      have hk' : k ≤ j := by omega
      have hkj : k < j := by omega
      simp only [adaptedTaylorResidual, adapted_taylor_removal_eval,
        ih hk' n hn, ih hk' k hkj]

theorem native_taylor_descent_lower_coefficients_unchanged {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E)
    (j : ℕ) (epsilon : ℝ) (m : ℤ) (V : D.E) {k : ℕ} (hk : k < j) :
    roughVectorMvEval (adaptedTaylorResidual D
      (nativeTaylorDescentCorrection D p j epsilon m V) k) (fun _ => (k : ℝ)) =
      roughVectorMvEval (adaptedTaylorResidual D p k) (fun _ => (k : ℝ)) :=
  adapted_taylor_residual_initial_values_congr D _ p j
    (fun _ hn => native_taylor_descent_correction_initial_values D p j epsilon m V hn)
    k (by omega) k hk

end Hindman168
