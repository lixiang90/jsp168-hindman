import Hindman168.ShortIntervalDensityBound
import Hindman168.IndependentDifferenceCubeBound

namespace Hindman168
open scoped BigOperators
variable {G : Type*} [AddCommGroup G] [Fintype G] (Q : AddSubgroup G) [Fintype Q]

theorem weightedShortIntervalDensityCube_bound {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ c, 0 ≤ p c) (hsum : ∑ c, p c = 1)
    (d J : ℕ) (hJ : 0 < J) (hL : 0 < Fintype.card Q / J)
    (e : ι → Fin d → Fin (Fintype.card Q / J) → Q)
    (he : ∀ c j, Function.Injective (e c j))
    (h : ι → G → ℝ) (hh : ∀ c x, |h c x| ≤ 1) :
    |∑ c, p c * finiteHaarMean (fun x => finiteHaarMean (fun u : Fin d → Q =>
      finiteHaarMean (fun v : Fin d → Q =>
        (∏ j, uniformImageHaarDensity (e c j) (u j)) *
        (∏ j, uniformImageHaarDensity (e c j) (v j)) *
        subgroupCubeProduct Q d (h c) x (v - u))))| ≤
      (2 * (J : ℝ)) ^ d * weightedSubgroupGowersValue Q p (2 ^ d) h := by
  letI : NeZero (Fintype.card Q / J) := ⟨Nat.ne_of_gt hL⟩
  apply weightedIndependentDifferenceCube_bound Q p hp hsum d
    (fun c j => uniformImageHaarDensity (e c j))
    (fun c j => uniformImageHaarDensity_nonneg (e c j))
    (fun c j => uniformImageHaarDensity_total (e c j) (he c j)) (2 * (J : ℝ))
  · positivity
  · exact fun c j => shortInterval_uniform_density_le J hJ hL (e c j)
  · exact hh

end Hindman168
