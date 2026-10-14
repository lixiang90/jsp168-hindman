import Hindman168.WeightedHaarHilbert
import Hindman168.WeightedDualApproximation

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Classical Topology

/-- A closed Hilbert subspace containing every selected actual unit family also
contains its internal finite average, even when the averaging type varies. -/
theorem weightedHaarHilbert_internal_average_closed
    {G κ A : ℕ → Type*} [∀ w, Fintype (G w)] [∀ w, Nonempty (G w)]
    [∀ w, Fintype (κ w)] [∀ w, Fintype (A w)] [∀ w, Nonempty (A w)]
    (p : ∀ w, κ w → ℝ) [∀ w, Fact (∀ c, 0 ≤ p w c)]
    (hs : ∀ w, ∑ c, p w c = 1) (U : Ultrafilter ℕ)
    (V : Submodule ℝ (UltrafilterHilbertSpace
      (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) U))
    (hV : IsClosed (V : Set (UltrafilterHilbertSpace
      (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) U)))
    (F : ∀ w, A w → κ w → G w → ℝ) (hF : ∀ w a c x, |F w a c x| ≤ 1)
    (hselected : ∀ a : ∀ w, A w,
      hilbertFamilyToCompletion _ U (weightedHaarBoundedFamily p hs
        (fun w c x => F w (a w) c x) 1 zero_le_one (fun w c x => hF w (a w) c x)) ∈ V)
    (g : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hg : ∀ w c x, g.val w (c, x) = finiteHaarMean (fun a => F w a c x)) :
    hilbertFamilyToCompletion _ U g ∈ V := by
  apply hV.closure_eq.subset
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sq_pos_of_pos hε)
  let m := n + 1
  have hm : 0 < m := Nat.succ_pos n
  have herr : 1 / (m : ℝ) < ε ^ 2 := by simpa only [m, Nat.cast_add, Nat.cast_one] using hn
  have hex (w : ℕ) := weightedHaar_exists_sample_L2 (p w) (Fact.out : ∀ c, 0 ≤ p w c)
    (hs w) (F w) (hF w) m hm
  choose sample hsample using hex
  let v := fun j : Fin m => weightedHaarBoundedFamily p hs
    (fun w c x => F w (sample w j) c x) 1 zero_le_one (fun w c x => hF w (sample w j) c x)
  let t := ∑ j, (1 / (m : ℝ)) • v j
  have ht : hilbertFamilyToCompletion _ U t ∈ V := by
    change (hilbertFamilyCompletionLinearMap _ U) t ∈ V
    simp only [t, map_sum, map_smul]
    exact V.sum_mem (fun j _ => V.smul_mem _ (hselected (fun w => sample w j)))
  have hval (w : ℕ) (c : κ w) (x : G w) :
      t.val w (c, x) = (∑ j, F w (sample w j) c x) / m := by
    simp only [t, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, v, weightedHaarBoundedFamily]
    change (∑ j : Fin m, (fun z : κ w × G w => (1 / (m : ℝ)) * F w (sample w j) z.1 z.2)) (c, x) = _
    simp only [Finset.sum_apply]
    rw [← Finset.mul_sum]
    ring
  have hb (w : ℕ) : ‖g.val w - t.val w‖ ^ 2 ≤ 1 / (m : ℝ) := by
    rw [norm_sub_rev, finiteMassL2_norm_sq, weightedHaarMass_expectation]
    change (∑ c, p w c * finiteHaarMean (fun x => (t.val w (c, x) - g.val w (c, x)) ^ 2)) ≤ _
    simp only [hg, hval]
    exact hsample w
  have hdist : ‖hilbertFamilyToCompletion _ U g - hilbertFamilyToCompletion _ U t‖ ^ 2 ≤ 1 / (m : ℝ) :=
    le_of_tendsto (hilbertFamilyToCompletion_norm_sub_sq_tendsto _ U g t) (Eventually.of_forall hb)
  refine ⟨hilbertFamilyToCompletion _ U t, ht, ?_⟩
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (hilbertFamilyToCompletion _ U g - hilbertFamilyToCompletion _ U t)]

end Hindman168
