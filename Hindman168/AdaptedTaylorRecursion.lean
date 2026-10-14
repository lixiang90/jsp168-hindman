import Hindman168.AdaptedTaylorRemoval

/-! Genuine finite ordered Taylor elimination in the original native group.
Each constructed residual has the same original filtration and one more
initial integer zero. Original nilpotence forces the final residual to
vanish at EVERY real input, closing the Taylor-coordinate argument. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def adaptedTaylorResidual {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) :
    ℕ → RoughVectorMvPolynomial Unit D.E
  | 0 => p
  | j+1 => adaptedTaylorRemoval D (adaptedTaylorResidual D p j) j

theorem adapted_taylor_residual_properties {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E)
    (hp : RoughVectorMvWeightedDegree
      (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) 1) p 0) (j : ℕ) :
    RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) 1)
      (adaptedTaylorResidual D p j) 0 ∧
      ∀ m : ℕ, m < j → roughVectorMvEval (adaptedTaylorResidual D p j) (fun _ => (m : ℝ)) = 0 := by
  induction j with
  | zero => exact ⟨hp, fun m hm => False.elim (Nat.not_lt_zero m hm)⟩
  | succ j ih =>
      exact ⟨adapted_taylor_removal_weighted D _ ih.1 j ih.2,
        adapted_taylor_removal_initial_zeros D _ j ih.2⟩

theorem adapted_taylor_residual_terminal {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E)
    (hp : RoughVectorMvWeightedDegree
      (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) 1) p 0) (b : ℝ) :
    roughVectorMvEval (adaptedTaylorResidual D p (s+1)) (fun _ => b) = 0 := by
  have h := adapted_taylor_residual_properties D p hp (s+1)
  have hm := rough_vector_weighted_initial_zeros_mem _
    (rough_native_stretched_lie_antitone 1 (by omega)) _ h.1 (s+1) (by omega) h.2 b
  have ht : roughNativeStretchedLieFiltration (I := D.I) (G := D.G) 1 (s+1) = ⊥ := by
    simpa only [Nat.mul_one] using rough_native_stretched_lie_terminal 1 (by omega) D.step_le
  rwa [ht, Submodule.mem_bot] at hm

noncomputable def adaptedTaylorFactor {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) (j : ℕ) (b : ℝ) : D.G :=
  nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
    (MvPolynomial.eval (fun _ => b) (adaptedTaylorBinomial j) •
      roughVectorMvEval p (fun _ => (j : ℝ)))

noncomputable def adaptedTaylorOrderedProduct {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) (b : ℝ) : ℕ → D.G
  | 0 => 1
  | j+1 => adaptedTaylorOrderedProduct D p b j * adaptedTaylorFactor D (adaptedTaylorResidual D p j) j b

theorem adapted_taylor_removal_exponential {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) (j : ℕ) (b : ℝ) :
    nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) (adaptedTaylorRemoval D p j) (fun _ => b)) =
      (adaptedTaylorFactor D p j b)⁻¹ * nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
        (roughVectorMvEval (E := D.E) p (fun _ => b)) := by
  rw [adapted_taylor_removal_eval, nativeLieExponential_globalLogarithm]
  let r := MvPolynomial.eval (fun _ => b) (adaptedTaylorBinomial j)
  let value := roughVectorMvEval p (fun _ => (j : ℝ))
  let exp := nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
  have hi : exp ((-r) • value) = (exp (r • value))⁻¹ :=
    (congrArg exp (neg_smul r value)).trans
      (nativeLieExponential_neg (E := D.E) (I := D.I) (G := D.G) (r • value))
  exact congrArg (fun z : D.G => z * exp (roughVectorMvEval (E := D.E) p (fun _ => b))) hi

theorem adapted_taylor_ordered_reconstruction {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) (b : ℝ) (j : ℕ) :
    nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) p (fun _ => b)) =
      adaptedTaylorOrderedProduct D p b j * nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
        (roughVectorMvEval (E := D.E) (adaptedTaylorResidual D p j) (fun _ => b)) := by
  induction j with
  | zero => simp only [adaptedTaylorOrderedProduct, adaptedTaylorResidual, one_mul]
  | succ j ih =>
      rw [adaptedTaylorOrderedProduct, adaptedTaylorResidual, adapted_taylor_removal_exponential]
      rw [mul_assoc, ← mul_assoc (adaptedTaylorFactor D (adaptedTaylorResidual D p j) j b),
        mul_inv_cancel, one_mul]
      exact ih

theorem adapted_taylor_full_ordered_representation {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E)
    (hp : RoughVectorMvWeightedDegree
      (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) 1) p 0) (b : ℝ) :
    nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) p (fun _ => b)) = adaptedTaylorOrderedProduct D p b (s+1) := by
  have h := adapted_taylor_ordered_reconstruction D p b (s+1)
  have he := (congrArg (nativeLieExponential (E := D.E) (I := D.I) (G := D.G))
    (adapted_taylor_residual_terminal D p hp b)).trans
      (nativeLieExponential_zero (E := D.E) (I := D.I) (G := D.G))
  exact h.trans ((congrArg (fun z : D.G => adaptedTaylorOrderedProduct D p b (s+1) * z) he).trans (mul_one _))

theorem adapted_taylor_actual_coefficient_group_layer {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E)
    (hp : RoughVectorMvWeightedDegree
      (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) 1) p 0) (j : ℕ) :
    nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) (adaptedTaylorResidual D p j) (fun _ => (j : ℝ))) ∈
      nilLowerCentralFiltration D.G j := by
  have h := adapted_taylor_residual_properties D p hp j
  have hm := adapted_taylor_initial_value_layer D _ h.1 j h.2
  have he := (rough_native_stretched_filtration_exp_mem_iff (I := D.I) 1 j _).mpr hm
  rwa [native_original_unstretched_group_layer] at he

theorem adapted_taylor_factor_integer_power {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) (j m : ℕ) :
    adaptedTaylorFactor D p j (m : ℝ) =
      nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
        (roughVectorMvEval (E := D.E) p (fun _ => (j : ℝ))) ^ m.choose j := by
  rw [adaptedTaylorFactor, adapted_taylor_binomial_eval_nat, nativeLieExponential_nat_smul]

end Hindman168
