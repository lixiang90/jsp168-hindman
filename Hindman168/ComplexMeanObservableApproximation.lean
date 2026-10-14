import Hindman168.FiniteComplexMassMean
import Mathlib.Topology.ContinuousMap.Compact

/-! Uniform observable approximation controls both original normalized means.
Empty finite sets retain their algebraic zero mean; no probability is asserted. -/
namespace Hindman168
open scoped BigOperators Classical

theorem finite_complex_set_mean_observable_difference {α : Type*} (S : Finset α)
    (f g : α → ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (hclose : ∀ x ∈ S, ‖f x-g x‖ ≤ ε) :
    ‖finiteComplexSetMean S f-finiteComplexSetMean S g‖ ≤ ε := by
  have he : finiteComplexSetMean S f-finiteComplexSetMean S g =
      finiteComplexSetMean S (fun x => f x-g x) := by
    unfold finiteComplexSetMean
    rw [Finset.sum_sub_distrib,sub_div]
  rw [he]
  exact finiteComplexSetMean_norm_bound S _ ε hε hclose

theorem complex_uniform_mean_observable_difference {α : Type*} (S : Finset α)
    (f g : α → ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (hclose : ∀ x ∈ S, ‖f x-g x‖ ≤ ε) :
    ‖FiniteMass.complexExpectation (FiniteMass.uniformFinsetMass S) f-
      FiniteMass.complexExpectation (FiniteMass.uniformFinsetMass S) g‖ ≤ ε := by
  rw [FiniteMass.complexExpectation_uniformFinset,FiniteMass.complexExpectation_uniformFinset]
  exact finite_complex_set_mean_observable_difference S f g ε hε hclose

theorem complex_two_uniform_means_observable_transfer {α : Type*} (S T : Finset α)
    (f g : α → ℂ) (ε η : ℝ) (hε : 0 ≤ ε)
    (hclose : ∀ x, ‖f x-g x‖ ≤ ε)
    (hbad : η ≤ ‖FiniteMass.complexExpectation (FiniteMass.uniformFinsetMass S) f-
      FiniteMass.complexExpectation (FiniteMass.uniformFinsetMass T) f‖) :
    η-2*ε ≤ ‖FiniteMass.complexExpectation (FiniteMass.uniformFinsetMass S) g-
      FiniteMass.complexExpectation (FiniteMass.uniformFinsetMass T) g‖ := by
  have hS := complex_uniform_mean_observable_difference S f g ε hε (fun x _ => hclose x)
  have hT := complex_uniform_mean_observable_difference T f g ε hε (fun x _ => hclose x)
  let a := FiniteMass.complexExpectation (FiniteMass.uniformFinsetMass S) f
  let b := FiniteMass.complexExpectation (FiniteMass.uniformFinsetMass T) f
  let c := FiniteMass.complexExpectation (FiniteMass.uniformFinsetMass S) g
  let d := FiniteMass.complexExpectation (FiniteMass.uniformFinsetMass T) g
  have he : a-b=(a-c)+(c-d)-(b-d) := by ring
  have hnorm : ‖a-b‖ ≤ ‖a-c‖+‖c-d‖+‖b-d‖ := by
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
  change ‖a-c‖ ≤ ε at hS
  change ‖b-d‖ ≤ ε at hT
  change η ≤ ‖a-b‖ at hbad
  change η-2*ε ≤ ‖c-d‖
  linarith

theorem complex_two_uniform_means_continuous_approximation {α X : Type*}
    [TopologicalSpace X] [CompactSpace X] (S T : Finset α) (x : α → X)
    (F G : C(X,ℂ)) (η : ℝ) (hη : 0 < η) (hclose : ‖F-G‖ < η/4)
    (hbad : η ≤ ‖FiniteMass.complexExpectation (FiniteMass.uniformFinsetMass S) (fun a => F (x a))-
      FiniteMass.complexExpectation (FiniteMass.uniformFinsetMass T) (fun a => F (x a))‖) :
    η/2 ≤ ‖FiniteMass.complexExpectation (FiniteMass.uniformFinsetMass S) (fun a => G (x a))-
      FiniteMass.complexExpectation (FiniteMass.uniformFinsetMass T) (fun a => G (x a))‖ := by
  have hh := complex_two_uniform_means_observable_transfer S T
    (fun a => F (x a)) (fun a => G (x a)) (η/4) η (by positivity)
    (fun a => (ContinuousMap.norm_coe_le_norm (F-G) (x a)).trans hclose.le) hbad
  linarith

end Hindman168
