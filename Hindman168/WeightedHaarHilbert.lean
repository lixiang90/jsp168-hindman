import Hindman168.FiniteMassUltrafilterHilbert
import Hindman168.MixedDualConvexHull

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Classical Topology

/-- The supplied cell weights times normalized counting measure on the group. -/
noncomputable def weightedHaarMass {G κ : Type*} [Fintype G] [Fintype κ]
    (p : κ → ℝ) : Mass (κ × G) :=
  Finsupp.onFinset Finset.univ (fun z => p z.1 / Fintype.card G) (by simp)

theorem weightedHaarMass_apply {G κ : Type*} [Fintype G] [Fintype κ]
    (p : κ → ℝ) (z : κ × G) : weightedHaarMass (G := G) p z = p z.1 / Fintype.card G := rfl

theorem weightedHaarMass_nonneg {G κ : Type*} [Fintype G] [Fintype κ]
    (p : κ → ℝ) (hp : ∀ c, 0 ≤ p c) (z : κ × G) : 0 ≤ weightedHaarMass (G := G) p z :=
  div_nonneg (hp z.1) (Nat.cast_nonneg _)

theorem weightedHaarMass_expectation {G κ : Type*} [Fintype G] [Fintype κ]
    (p : κ → ℝ) (f : κ × G → ℝ) :
    expectation (weightedHaarMass (G := G) p) f =
      ∑ c, p c * finiteHaarMean (fun x => f (c, x)) := by
  rw [expectation, Finsupp.sum_of_support_subset _ (Finset.subset_univ _) _ (by simp)]
  rw [Fintype.sum_prod_type]
  simp only [weightedHaarMass_apply, finiteHaarMean, Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem weightedHaarMass_total {G κ : Type*} [Fintype G] [Nonempty G] [Fintype κ]
    (p : κ → ℝ) (hs : ∑ c, p c = 1) : total (weightedHaarMass (G := G) p) = 1 := by
  have h := weightedHaarMass_expectation (G := G) p (fun _ => 1)
  simpa [expectation, total, finiteHaarMean_const, hs] using h

instance weightedHaarMass_nonnegative {G κ : Type*} [Fintype G] [Fintype κ]
    (p : κ → ℝ) [hp : Fact (∀ c, 0 ≤ p c)] :
    Fact (∀ z, 0 ≤ weightedHaarMass (G := G) p z) :=
  ⟨weightedHaarMass_nonneg p hp.out⟩

variable {G κ : ℕ → Type*} [∀ w, Fintype (G w)] [∀ w, Nonempty (G w)]
  [∀ w, Fintype (κ w)] (p : ∀ w, κ w → ℝ) [∀ w, Fact (∀ c, 0 ≤ p w c)]

noncomputable def weightedHaarBoundedFamily (hs : ∀ w, ∑ c, p w c = 1)
    (f : ∀ w, κ w → G w → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ w c x, |f w c x| ≤ B) :
    boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) :=
  ⟨fun w z => f w z.1 z.2, B, hB, fun w =>
    finiteMassL2_norm_le _ (weightedHaarMass_total (p w) (hs w)) _ hB (fun z _ => hf w z.1 z.2)⟩

omit [∀ w, Nonempty (G w)] in
theorem weightedHaarHilbert_inner_tendsto (U : Ultrafilter ℕ)
    (f g : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w)))) :
    Tendsto (fun w => ∑ c, p w c * finiteHaarMean (fun x => f.val w (c, x) * g.val w (c, x)))
      (U : Filter ℕ) (𝓝 (inner ℝ (hilbertFamilyToCompletion _ U f) (hilbertFamilyToCompletion _ U g))) := by
  rw [hilbertFamilyToCompletion_inner]
  simpa only [finiteMassL2_inner, weightedHaarMass_expectation] using hilbertFamilyPairing_tendsto _ U f g

end Hindman168
