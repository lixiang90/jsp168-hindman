import Hindman168.FiniteEventComparison
import Hindman168.FiniteWeightedErrors
import Hindman168.UnitCRTJointLaw

/-!
# Inserting translations in an actual independent coordinate law

The coefficient L1 error is bounded by the sum of coordinate errors.
Averaging over independent auxiliary choices preserves the bound and the
original outside mass. No independence or normalized conditional law is
introduced as an additional conclusion hypothesis.
-/

namespace Hindman168.FiniteMass

open scoped BigOperators Classical

theorem piMass_probability_distance_fintype {ι α : Type*} [Fintype ι]
    (μ ν : ι → Mass α) (hμ : ∀ i a, 0 ≤ μ i a) (hν : ∀ i a, 0 ≤ ν i a)
    (htμ : ∀ i, total (μ i) = 1) (htν : ∀ i, total (ν i) = 1) :
    distance (piMass μ) (piMass ν) ≤ ∑ i, distance (μ i) (ν i) := by
  let e := (Fintype.equivFin ι).symm
  have hi : Function.Injective (fun x : ι → α => fun j => x (e j)) := by
    intro x y h
    funext i
    obtain ⟨j, rfl⟩ := e.surjective i
    exact congrFun h j
  calc
    _ = distance (piMass (fun j => μ (e j))) (piMass (fun j => ν (e j))) := by
      rw [← piMass_reindex μ e, ← piMass_reindex ν e, distance_push_injective hi]
    _ ≤ ∑ j, distance (μ (e j)) (ν (e j)) :=
      piMass_probability_distance_sum _ _ _ (fun j => hμ (e j))
        (fun j => hν (e j)) (fun j => htμ (e j)) (fun j => htν (e j))
    _ = _ := Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem piMass_translation_distance {ι : Type*} [Fintype ι]
    (μ : ι → Mass ℤ) (u : ι → ℤ)
    (hμ : ∀ i a, 0 ≤ μ i a) (htμ : ∀ i, total (μ i) = 1) :
    distance ((piMass μ).mapDomain (fun z i => z i + u i)) (piMass μ) ≤
      ∑ i, distance ((μ i).mapDomain (fun z => z + u i)) (μ i) := by
  rw [piMass_map μ (fun i z => z + u i)]
  exact piMass_probability_distance_fintype _ _
    (fun i => push_nonneg _ _ (hμ i)) hμ
    (fun i => (total_push _ _).trans (htμ i)) htμ

theorem piMass_translation_expectation_bound {ι : Type*} [Fintype ι]
    (μ : ι → Mass ℤ) (u : ι → ℤ) (f : (ι → ℤ) → ℝ) {B : ℝ}
    (hμ : ∀ i a, 0 ≤ μ i a) (htμ : ∀ i, total (μ i) = 1)
    (hB : 0 ≤ B) (hf : ∀ z, |f z| ≤ B) :
    |expectation (piMass μ) (fun z => f (fun i => z i + u i)) -
      expectation (piMass μ) f| ≤
      B * ∑ i, distance ((μ i).mapDomain (fun z => z + u i)) (μ i) := by
  rw [← expectation_push]
  exact (expectation_difference_bound _ _ f B hf).trans
    (mul_le_mul_of_nonneg_left (piMass_translation_distance μ u hμ htμ) hB)

theorem averaged_piMass_translation_expectation_bound {ι β : Type*} [Fintype ι]
    (μ : ι → Mass ℤ) (ρ : Mass β) (u : β → ι → ℤ)
    (f : (ι → ℤ) → ℝ) {B δ : ℝ}
    (hμ : ∀ i a, 0 ≤ μ i a) (htμ : ∀ i, total (μ i) = 1)
    (hρ : ∀ v, 0 ≤ ρ v) (htρ : total ρ = 1)
    (hB : 0 ≤ B) (hf : ∀ z, |f z| ≤ B)
    (hδ : ∀ v ∈ ρ.support,
      ∑ i, distance ((μ i).mapDomain (fun z => z + u v i)) (μ i) ≤ δ) :
    |expectation ρ (fun v => expectation (piMass μ)
        (fun z => f (fun i => z i + u v i))) - expectation (piMass μ) f| ≤ B * δ := by
  have hc : expectation ρ (fun _ => expectation (piMass μ) f) =
      expectation (piMass μ) f := by
    unfold expectation
    rw [Finsupp.sum, ← Finset.sum_mul]
    change total ρ * _ = _
    rw [htρ, one_mul]
  rw [← hc]
  have hb := expectation_difference_support_bound ρ hρ
    (fun v => expectation (piMass μ) (fun z => f (fun i => z i + u v i)))
    (fun _ => expectation (piMass μ) f) (B * δ) (fun v hv =>
      (piMass_translation_expectation_bound μ (u v) f hμ htμ hB hf).trans
        (mul_le_mul_of_nonneg_left (hδ v hv) hB))
  simpa only [htρ, one_mul] using hb

end Hindman168.FiniteMass
