import Hindman168.HaarIndependentDensities
import Hindman168.DensityCubeGowersBound

namespace Hindman168
open scoped BigOperators
variable {G : Type*} [AddCommGroup G] [Fintype G] (Q : AddSubgroup G) [Fintype Q]

theorem weightedIndependentDifferenceCube_bound {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ c, 0 ≤ p c) (hsum : ∑ c, p c = 1) (d : ℕ)
    (r : ι → Fin d → Q → ℝ) (hr : ∀ c j u, 0 ≤ r c j u)
    (ht : ∀ c j, finiteHaarMean (r c j) = 1) (C : ℝ) (hC : 0 < C)
    (hb : ∀ c j u, r c j u ≤ C) (h : ι → G → ℝ) (hh : ∀ c x, |h c x| ≤ 1) :
    |∑ c, p c * finiteHaarMean (fun x => finiteHaarMean (fun u : Fin d → Q =>
      finiteHaarMean (fun v : Fin d → Q => (∏ j, r c j (u j)) * (∏ j, r c j (v j)) *
        subgroupCubeProduct Q d (h c) x (v - u))))| ≤
      C ^ d * weightedSubgroupGowersValue Q p (2 ^ d) h := by
  simp only [independentDifferences_expectation]
  exact weightedDensityCube_gowers_bound Q p hp hsum d (C ^ d) (pow_pos hC d)
    (fun c a => ∏ j, finiteHaarDifferenceDensity (r c j) (a j))
    (fun c => independentDifferenceDensity_bound d (r c) (hr c) (ht c) C (hb c)) h hh

end Hindman168
