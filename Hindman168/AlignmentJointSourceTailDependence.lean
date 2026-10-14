import Hindman168.AlignmentNativeModelLogEvalCongruence
import Hindman168.AlignmentJointParameterTailCongruence
import Hindman168.AlignmentJointRemovedNativeSource

/-! The ACTUAL joint source reads only tail factors. Its removed-factor
extension reads only the OTHER tail factors, so one source really is fixed
on each independent rest fiber; outside/pivot values do not change it. -/
namespace Hindman168
open Module
open scoped Manifold ContDiff BigOperators Classical
universe u

variable {ι : Type} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ]
  {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))
  (r : ι → ℕ) (b : ∀ ν, Basis (Fin (r ν)) ℝ (alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)).E)

omit [Fintype ι] [DecidableEq ι] in
theorem alignment_exposed_native_vector_tail_eval_congr
    (ν : ι) (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (x : Fin N → ℕ)
    (shift : AlignmentAddingPair N i → ℤ) (weight : κ → ℤ) (g a : (D ν).G)
    (z : Option κ → ℝ) (t t' : Fin N → ℝ) (h : ∀ j ∈ T, t j=t' j) :
    roughVectorMvEval (alignmentExposedNativeVectorPolynomial (D ν) (n ν) (v ν) (hv ν) (b ν)
      F q₀ w T x shift weight g a) (Sum.elim z t)=
    roughVectorMvEval (alignmentExposedNativeVectorPolynomial (D ν) (n ν) (v ν) (hv ν) (b ν)
      F q₀ w T x shift weight g a) (Sum.elim z t') := by
  letI := alignmentAddingPairFintype N i
  letI : LieGroup (D ν).I (minSmoothness ℝ 3) (D ν).G := lieGroup_smooth_min_three
  rw [alignmentExposedNativeVectorPolynomial,roughVectorMvFromBasis_eval,roughVectorMvFromBasis_eval]
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (fun c : ℝ => c • b ν j)
  unfold alignmentNativeExposedJointLogPolynomial
  apply alignment_native_model_log_eval_congr (D ν) (n ν) (v ν) g a
  · exact alignment_exposed_joint_base_tail_eval_congr F q₀ w i T x shift weight z t t' h
  · intro e
    exact alignment_exposed_joint_increment_tail_eval_congr F q₀ w i T x e z t t' h

theorem alignment_joint_exposed_native_vector_tail_eval_congr
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (x : Fin N → ℕ)
    (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G)
    (z : Option κ → ℝ) (t t' : Fin N → ℝ) (h : ∀ j ∈ T, t j=t' j) :
    roughVectorMvEval (alignmentJointExposedNativePolynomial D n v hv r b
      F q₀ w T x shift weight g a) (Sum.elim z t)=
    roughVectorMvEval (alignmentJointExposedNativePolynomial D n v hv r b
      F q₀ w T x shift weight g a) (Sum.elim z t') := by
  apply (nativeFinitePiModelEquiv (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).injective
  rw [alignmentJointExposedNativePolynomial,native_finite_pi_vector_polynomial_eval,
    native_finite_pi_vector_polynomial_eval]
  funext ν
  exact alignment_exposed_native_vector_tail_eval_congr D n v hv r b ν
    F q₀ w T x (shift ν) (weight ν) (g ν) (a ν) z t t' h

theorem alignment_joint_removed_native_source_tail_congr
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (x : Fin N → ℕ)
    (j : Fin N) (frozen frozen' : Fin N → ℝ)
    (h : ∀ k ∈ T, k ≠ j → frozen k=frozen' k)
    (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G) :
    alignmentJointRemovedNativeSource D n v hv r b F q₀ w T x j frozen shift weight g a=
      alignmentJointRemovedNativeSource D n v hv r b F q₀ w T x j frozen' shift weight g a := by
  funext z
  have hz : z=(Option.elim · (z none) (fun k => z (some k))) := by
    funext k; cases k <;> rfl
  unfold alignmentJointRemovedNativeSource
  apply native_vector_polynomial_source_sample
  rw [native_vector_polynomial_source_log,hz]
  simp only [alignmentJointRemovedNativePolynomial]
  rw [rough_removed_factor_polynomial_eval,rough_removed_factor_polynomial_eval]
  apply alignment_joint_exposed_native_vector_tail_eval_congr D n v hv r b
  intro k hk
  by_cases hkj : k=j
  · subst k; rw [Function.update_self,Function.update_self]
  · rw [Function.update_of_ne hkj,Function.update_of_ne hkj]
    exact h k hk hkj

end Hindman168
