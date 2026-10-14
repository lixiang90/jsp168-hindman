import Hindman168.AdaptedTaylorInitialZeros
import Hindman168.AdaptedTaylorBinomial

/-! An actual Taylor removal, with proved original layer membership,
all-real product identity, unchanged original step, and one further integer
zero. It is a constructor, not a Taylor-factorization assumption. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def adaptedTaylorCorrection {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) (j : ℕ) :
    RoughVectorMvPolynomial Unit D.E :=
  [(adaptedTaylorBinomial j, -roughVectorMvEval p (fun _ => (j : ℝ)))]

noncomputable def adaptedTaylorRemoval {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) (j : ℕ) :
    RoughVectorMvPolynomial Unit D.E :=
  roughVectorMvZeroTrim (roughNativeProductMvPolynomial (I := D.I) (G := D.G)
    (adaptedTaylorCorrection D p j) p)

theorem adapted_taylor_initial_value_layer {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E)
    (hp : RoughVectorMvWeightedDegree
      (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) 1) p 0) (j : ℕ)
    (hz : ∀ m : ℕ, m < j → roughVectorMvEval p (fun _ => (m : ℝ)) = 0) :
    roughVectorMvEval p (fun _ => (j : ℝ)) ∈
      roughNativeStretchedLieFiltration (I := D.I) (G := D.G) 1 j := by
  by_cases hj : j = 0
  · subst j
    exact rough_vector_weighted_eval _ (rough_native_stretched_lie_antitone 1 (by omega)) hp _
  · exact rough_vector_weighted_initial_zeros_mem _
      (rough_native_stretched_lie_antitone 1 (by omega)) p hp j (by omega) hz _

theorem adapted_taylor_correction_weighted {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E)
    (hp : RoughVectorMvWeightedDegree
      (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) 1) p 0) (j : ℕ)
    (hz : ∀ m : ℕ, m < j → roughVectorMvEval p (fun _ => (m : ℝ)) = 0) :
    RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) 1)
      (adaptedTaylorCorrection D p j) 0 := by
  intro z h
  obtain rfl := List.mem_singleton.mp h
  apply rough_native_stretched_lie_antitone 1 (by omega)
    (by simpa only [Nat.add_zero] using adapted_taylor_binomial_degree j)
  exact Submodule.neg_mem _ (adapted_taylor_initial_value_layer D p hp j hz)

theorem adapted_taylor_removal_weighted {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E)
    (hp : RoughVectorMvWeightedDegree
      (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) 1) p 0) (j : ℕ)
    (hz : ∀ m : ℕ, m < j → roughVectorMvEval p (fun _ => (m : ℝ)) = 0) :
    RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) 1)
      (adaptedTaylorRemoval D p j) 0 :=
  rough_vector_zero_trim_weighted _ (rough_native_product_polynomial_weighted 1 (by omega)
    (adapted_taylor_correction_weighted D p hp j hz) hp)

theorem adapted_taylor_removal_eval {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) (j : ℕ)
    (x : Unit → ℝ) :
    roughVectorMvEval (E := D.E) (adaptedTaylorRemoval D p j) x =
      nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
        (nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
          (-(MvPolynomial.eval x (adaptedTaylorBinomial j)) •
            roughVectorMvEval p (fun _ => (j : ℝ))) *
          nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) p x)) := by
  rw [adaptedTaylorRemoval, rough_vector_zero_trim_eval, roughNativeProductMvPolynomial_eval]
  simp only [adaptedTaylorCorrection, roughVectorMvEval, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, smul_neg, neg_smul]

theorem adapted_taylor_removal_initial_zeros {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) (j : ℕ)
    (hz : ∀ m : ℕ, m < j → roughVectorMvEval p (fun _ => (m : ℝ)) = 0) :
    ∀ m : ℕ, m < j+1 → roughVectorMvEval (adaptedTaylorRemoval D p j) (fun _ => (m : ℝ)) = 0 := by
  intro m hm
  rw [adapted_taylor_removal_eval, adapted_taylor_binomial_eval_nat]
  let exp := nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
  let log := nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
  let value := roughVectorMvEval p (fun _ => (j : ℝ))
  by_cases hj : m < j
  · have ha : -(m.choose j : ℝ) • value = 0 := by
      rw [Nat.choose_eq_zero_of_lt hj, Nat.cast_zero, neg_zero, zero_smul]
    have he0 : exp (0 : D.E) = 1 := nativeLieExponential_zero (E := D.E) (I := D.I) (G := D.G)
    have he1 := (congrArg exp ha).trans he0
    have he2 := (congrArg exp (hz m hj)).trans he0
    have hg := (congrArg₂ (fun z w : D.G => z*w) he1 he2).trans (one_mul (1 : D.G))
    exact (congrArg log hg).trans (nativeLieGlobalLogarithm_one (E := D.E) (I := D.I) (G := D.G))
  · have he : m = j := by omega
    subst m
    have ha : -(j.choose j : ℝ) • value = -value := by
      rw [Nat.choose_self, Nat.cast_one, neg_one_smul]
    have hi : exp (-value) = (exp value)⁻¹ :=
      nativeLieExponential_neg (E := D.E) (I := D.I) (G := D.G) value
    have hg := (congrArg (fun z : D.G => z*exp value) ((congrArg exp ha).trans hi)).trans
      (inv_mul_cancel (exp value))
    exact (congrArg log hg).trans (nativeLieGlobalLogarithm_one (E := D.E) (I := D.I) (G := D.G))

end Hindman168
