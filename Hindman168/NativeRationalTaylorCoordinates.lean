import Hindman168.AdaptedTaylorRecursion
import Hindman168.NativeRationalWeightedOperations

/-! The SAME actual ordered Taylor constructors work after genuine rational
filtration descent. The rational filtration is geometric data only; all
residual weights, zeros, termination and coefficient memberships are proved.
The length is the supplied genuine filtration terminal index ell, which is
the original s when applied to the original section-7 filtration. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_taylor_initial_value_layer {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (j : ℕ) (hz : ∀ m : ℕ, m < j → roughVectorMvEval p (fun _ => (m : ℝ)) = 0) :
    roughVectorMvEval p (fun _ => (j : ℝ)) ∈ F.layer j := by
  by_cases hj : j = 0
  · subst j
    exact rough_vector_weighted_eval F.layer F.antitone hp _
  · exact rough_vector_weighted_initial_zeros_mem F.layer F.antitone p hp j (by omega) hz _

theorem native_rational_taylor_correction_weighted {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (j : ℕ) (hz : ∀ m : ℕ, m < j → roughVectorMvEval p (fun _ => (m : ℝ)) = 0) :
    RoughVectorMvWeightedDegree F.layer (adaptedTaylorCorrection D p j) 0 := by
  intro z h
  obtain rfl := List.mem_singleton.mp h
  apply F.antitone (by simpa only [Nat.add_zero] using adapted_taylor_binomial_degree j)
  exact Submodule.neg_mem _ (native_rational_taylor_initial_value_layer D F p hp j hz)

theorem native_rational_taylor_removal_weighted {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (j : ℕ) (hz : ∀ m : ℕ, m < j → roughVectorMvEval p (fun _ => (m : ℝ)) = 0) :
    RoughVectorMvWeightedDegree F.layer (adaptedTaylorRemoval D p j) 0 :=
  rough_vector_zero_trim_weighted _ (native_rational_product_polynomial_weighted D F
    (native_rational_taylor_correction_weighted D F p hp j hz) hp)

theorem native_rational_taylor_residual_properties {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0) (j : ℕ) :
    RoughVectorMvWeightedDegree F.layer (adaptedTaylorResidual D p j) 0 ∧
      ∀ m : ℕ, m < j → roughVectorMvEval (adaptedTaylorResidual D p j) (fun _ => (m : ℝ)) = 0 := by
  induction j with
  | zero => exact ⟨hp, fun m hm => False.elim (Nat.not_lt_zero m hm)⟩
  | succ j ih =>
      exact ⟨native_rational_taylor_removal_weighted D F _ ih.1 j ih.2,
        adapted_taylor_removal_initial_zeros D _ j ih.2⟩

theorem native_rational_taylor_residual_terminal {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0) (b : ℝ) :
    roughVectorMvEval (adaptedTaylorResidual D p (ℓ+1)) (fun _ => b) = 0 := by
  have h := native_rational_taylor_residual_properties D F p hp (ℓ+1)
  have hm := rough_vector_weighted_initial_zeros_mem F.layer F.antitone _ h.1 (ℓ+1) (by omega) h.2 b
  rwa [F.terminal, Submodule.mem_bot] at hm

theorem native_rational_taylor_ordered_representation {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0) (b : ℝ) :
    nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) p (fun _ => b)) = adaptedTaylorOrderedProduct D p b (ℓ+1) := by
  have h := adapted_taylor_ordered_reconstruction D p b (ℓ+1)
  have he := (congrArg (nativeLieExponential (E := D.E) (I := D.I) (G := D.G))
    (native_rational_taylor_residual_terminal D F p hp b)).trans
      (nativeLieExponential_zero (E := D.E) (I := D.I) (G := D.G))
  exact h.trans ((congrArg (fun z : D.G => adaptedTaylorOrderedProduct D p b (ℓ+1) * z) he).trans (mul_one _))

theorem native_rational_taylor_actual_coefficient_layer {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0) (j : ℕ) :
    nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) (adaptedTaylorResidual D p j) (fun _ => (j : ℝ))) ∈
      nativeRationalFilteredGroupLayer D F j := by
  have h := native_rational_taylor_residual_properties D F p hp j
  have hm := native_rational_taylor_initial_value_layer D F _ h.1 j h.2
  exact ⟨_, hm, rfl⟩

end Hindman168
