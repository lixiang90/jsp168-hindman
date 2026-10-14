import Hindman168.FiniteProjectionBessel
import Hindman168.MixedDualProjectionPairOrthogonality

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Classical Topology

variable {G κ : ℕ → Type*} [∀ w, AddCommGroup (G w)] [∀ w, Fintype (G w)]
  [∀ w, Fintype (κ w)] {ι : Type*} [Fintype ι]
  (p : ∀ w, κ w → ℝ) [∀ w, Fact (∀ c, 0 ≤ p w c)]
  (U : Ultrafilter ℕ) (Q : ι → ∀ w, AddSubgroup (G w))
  [∀ i w, Fintype (Q i w)] [∀ i j w, Fintype (Q i w ⊔ Q j w : AddSubgroup (G w))]

/-- Full finite projection energy under the genuine off-diagonal
concatenated-factor orthogonality hypotheses, allowing different degrees. -/
theorem mixedDualHilbert_finite_bessel_energy
    (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ w, ∑ c, p w c = 1)
    (d : ι → ℕ) (hd : ∀ i, 0 < d i)
    (z : UltrafilterHilbertSpace (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) U)
    (hz : ∀ i j, i ≠ j → z ∈
      (mixedDualHilbertSubspace p (fun w => Q i w ⊔ Q j w) (d i + d j - 1) U)ᗮ) :
    ∑ i, ‖(mixedDualHilbertSubspace p (Q i) (d i) U).starProjection z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
  apply finiteProjection_bessel_energy
  intro i j hij
  exact mixedDualHilbert_pair_projections_orthogonal p U (Q i) (Q j)
    hU hs (d i) (d j) (hd i) (hd j) z (hz i j hij)

/-- For an actual unit-bounded family, vanishing off-diagonal sum Gowers
values bound the total energy of all its factor projections by one. -/
theorem mixedDualHilbert_finite_bessel_energy_le_one
    (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ w, ∑ c, p w c = 1)
    (d : ι → ℕ) (hd : ∀ i, 0 < d i)
    (g : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hg : ∀ w c x, |g.val w (c, x)| ≤ 1)
    (hz : ∀ i j, i ≠ j → Tendsto (fun w =>
      weightedSubgroupGowersValue (Q i w ⊔ Q j w) (p w) (d i + d j - 1)
        (fun c x => g.val w (c, x))) (U : Filter ℕ) (𝓝 0)) :
    ∑ i, ‖(mixedDualHilbertSubspace p (Q i) (d i) U).starProjection
      (hilbertFamilyToCompletion _ U g)‖ ^ 2 ≤ 1 := by
  have hb := mixedDualHilbert_finite_bessel_energy p U Q hU hs d hd
    (hilbertFamilyToCompletion _ U g) (fun i j hij =>
      mixedDualHilbert_orthogonal_of_gowers_zero p (fun w => Q i w ⊔ Q j w)
        (d i + d j - 1) U hs (by have := hd i; have := hd j; omega) g (hz i j hij))
  have hn : ‖hilbertFamilyToCompletion _ U g‖ ≤ 1 := by
    apply hilbertFamilyToCompletion_norm_le _ U g zero_le_one
    intro w
    exact finiteMassL2_norm_le _ (weightedHaarMass_total (p w) (hs w)) _ zero_le_one
      (fun z _ => hg w z.1 z.2)
  exact hb.trans (by nlinarith [norm_nonneg (hilbertFamilyToCompletion _ U g)])

end Hindman168
