import Hindman168.RoughVectorMvSubstitution
import Hindman168.NativeVectorPolynomialSource

/-! Isolate ONE removed factor as the parameter. Every other factor is
literally frozen, while all spatial variables remain free. This construction
proves the all-real joint log identity rather than assuming a source packet. -/
namespace Hindman168
open scoped Classical
universe u

noncomputable def roughRemovedFactorVariables {κ ι : Type*}
    (j : ι) (frozen : ι → ℝ) : Sum κ ι → MvPolynomial (Option κ) ℝ :=
  Sum.elim (fun a => MvPolynomial.X (some a))
    (fun a => if a=j then MvPolynomial.X none else MvPolynomial.C (frozen a))

theorem rough_removed_factor_variables_linear {κ ι : Type*} (j : ι) (frozen : ι → ℝ) :
    ∀ a : Sum κ ι, (roughRemovedFactorVariables j frozen a).totalDegree ≤ 1 := by
  intro a
  cases a with
  | inl a => simp [roughRemovedFactorVariables]
  | inr a =>
    simp only [roughRemovedFactorVariables,Sum.elim_inr]
    split_ifs <;> simp

noncomputable def roughRemovedFactorPolynomial {κ ι E : Type*}
    (j : ι) (frozen : ι → ℝ) (p : RoughVectorMvPolynomial (Sum κ ι) E) :
    RoughVectorMvPolynomial (Option κ) E :=
  roughVectorMvSubstitution (roughRemovedFactorVariables j frozen) p

theorem rough_removed_factor_polynomial_degree {κ ι E : Type*}
    (j : ι) (frozen : ι → ℝ) {p : RoughVectorMvPolynomial (Sum κ ι) E} {d : ℕ}
    (hp : RoughVectorMvDegreeLE p d) :
    RoughVectorMvDegreeLE (roughRemovedFactorPolynomial j frozen p) d :=
  rough_vector_mv_substitution_degree _ (rough_removed_factor_variables_linear j frozen) hp

theorem rough_removed_factor_polynomial_eval {κ ι E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq ι]
    (j : ι) (frozen : ι → ℝ) (p : RoughVectorMvPolynomial (Sum κ ι) E)
    (z : ℝ) (y : κ → ℝ) :
    roughVectorMvEval (roughRemovedFactorPolynomial j frozen p) (Option.elim · z y) =
      roughVectorMvEval p (Sum.elim y (Function.update frozen j z)) := by
  rw [roughRemovedFactorPolynomial,rough_vector_mv_substitution_eval]
  congr 1
  funext a
  cases a with
  | inl a => simp only [roughRemovedFactorVariables,Sum.elim_inl,MvPolynomial.eval_X,Option.elim_some]
  | inr a =>
    simp only [roughRemovedFactorVariables,Sum.elim_inr]
    by_cases ha : a=j
    · subst a
      simp
    · simp only [if_neg ha,MvPolynomial.eval_C,Function.update_of_ne ha]

theorem rough_removed_factor_native_source_log {κ ι : Type*} [DecidableEq ι] {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (j : ι) (frozen : ι → ℝ)
    (p : RoughVectorMvPolynomial (Sum κ ι) D.E) (z : ℝ) (y : κ → ℝ) :
    nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
      (nativeVectorPolynomialSource D (roughRemovedFactorPolynomial j frozen p) (Option.elim · z y)) =
      roughVectorMvEval p (Sum.elim y (Function.update frozen j z)) := by
  rw [native_vector_polynomial_source_log,rough_removed_factor_polynomial_eval]

theorem rough_removed_factor_polynomial_frozen_update {κ ι E : Type*}
    [DecidableEq ι]
    (j : ι) (frozen : ι → ℝ) (z : ℝ) (p : RoughVectorMvPolynomial (Sum κ ι) E) :
    roughRemovedFactorPolynomial j (Function.update frozen j z) p =
      roughRemovedFactorPolynomial j frozen p := by
  unfold roughRemovedFactorPolynomial
  apply congrArg (fun f => roughVectorMvSubstitution f p)
  funext a
  cases a with
  | inl a => rfl
  | inr a =>
    by_cases ha : a=j
    · simp only [roughRemovedFactorVariables,Sum.elim_inr,if_pos ha]
    · simp only [roughRemovedFactorVariables,Sum.elim_inr,if_neg ha,Function.update_of_ne ha]

end Hindman168
