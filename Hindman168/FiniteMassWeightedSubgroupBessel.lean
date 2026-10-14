import Hindman168.WeightedSubgroupQualitativeBessel
import Hindman168.FiniteCountableExpectations

namespace Hindman168
open FiniteMass
open scoped BigOperators Classical

/-- The qualitative subgroup Bessel bound for an original finite mass
on an arbitrary index type, including infinite ambient index types.
Restricting to its genuine support retains each coefficient exactly. -/
theorem finiteMass_weighted_subgroup_qualitative_bessel
    {G κ A : Type} [AddCommGroup G] [Fintype G] [Fintype κ]
    (p : κ → ℝ) (hp : ∀ c, 0 ≤ p c) (hs : ∑ c, p c = 1)
    (μ : Mass A) (hμ : ∀ a, 0 ≤ μ a) (ht : total μ = 1)
    (Q : A → AddSubgroup G) (g : κ → G → ℝ) (hg : ∀ c x, |g c x| ≤ 1)
    (d : ℕ) (hd : 0 < d) (δ : ℝ)
    (hpair : expectation (tensor μ μ) (fun ab =>
      weightedSubgroupGowersValue (Q ab.1 ⊔ Q ab.2) p (d + d - 1) g) ≤ δ) :
    expectation μ (fun a => weightedSubgroupGowersValue (Q a) p d g) ≤
      finiteWeightedBesselModulus d δ := by
  have hE (f : A → ℝ) : expectation μ f = ∑ a : μ.support, μ a * f a := by
    rw [Finset.sum_coe_sort μ.support (fun a : A => μ a * f a)]
    rfl
  have ht' : (∑ a : μ.support, μ a) = 1 := by
    rw [Finset.sum_coe_sort μ.support (fun a : A => μ a)]
    exact ht
  have hp' : (∑ a : μ.support, ∑ b : μ.support, μ a * μ b *
      weightedSubgroupGowersValue (Q a ⊔ Q b) p (d + d - 1) g) ≤ δ := by
    rw [expectation_tensor] at hpair
    simpa only [hE, Finset.mul_sum, mul_assoc] using hpair
  rw [hE]
  exact weighted_subgroup_qualitative_bessel p hp hs (fun a : μ.support => μ a)
    (fun a => hμ a) ht' (fun a => Q a) g hg d hd δ hp'

end Hindman168
