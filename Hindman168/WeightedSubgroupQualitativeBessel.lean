import Hindman168.FiniteWeightedBesselModulus

namespace Hindman168
open scoped BigOperators Classical

/-- The full qualitative Bessel bound for the actual finite subgroup
weighted Haar model. The same nondecreasing null modulus is used for
every finite group, cell law, direction law and unit input. -/
theorem weighted_subgroup_qualitative_bessel
    {G κ A : Type} [AddCommGroup G] [Fintype G] [Fintype κ] [Fintype A]
    (p : κ → ℝ) (hp : ∀ c, 0 ≤ p c) (hs : ∑ c, p c = 1)
    (α : A → ℝ) (hα : ∀ a, 0 ≤ α a) (hαs : ∑ a, α a = 1)
    (Q : A → AddSubgroup G) (g : κ → G → ℝ) (hg : ∀ c x, |g c x| ≤ 1)
    (d : ℕ) (hd : 0 < d) (δ : ℝ)
    (hpair : (∑ a, ∑ b, α a * α b *
      weightedSubgroupGowersValue (Q a ⊔ Q b) p (d + d - 1) g) ≤ δ) :
    (∑ a, α a * weightedSubgroupGowersValue (Q a) p d g) ≤
      finiteWeightedBesselModulus d δ := by
  let S : FiniteWeightedSubgroupSystem.{0} :=
    { G := G, addCommGroup := inferInstance, finiteGroup := inferInstance,
      κ := κ, finiteCells := inferInstance, A := A, finiteIndices := inferInstance,
      p := p, p_nonneg := hp, p_total := hs,
      α := α, α_nonneg := hα, α_total := hαs,
      Q := Q, g := g, g_unit := hg }
  exact finiteWeightedSubgroupMean_le_besselModulus S d hd δ hpair

end Hindman168
