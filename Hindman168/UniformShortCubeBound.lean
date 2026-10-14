import Hindman168.UniformTupleExpectation
import Hindman168.ShortIntervalDifferenceCubeBound

namespace Hindman168
open scoped BigOperators
variable {G : Type*} [AddCommGroup G] [Fintype G] (Q : AddSubgroup G) [Fintype Q]

theorem weightedUniformShortCube_bound {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ c, 0 ≤ p c) (hsum : ∑ c, p c = 1)
    (d J : ℕ) (hJ : 0 < J) (hL : 0 < Fintype.card Q / J)
    (e : ι → Fin d → Fin (Fintype.card Q / J) → Q)
    (he : ∀ c j, Function.Injective (e c j))
    (h : ι → G → ℝ) (hh : ∀ c x, |h c x| ≤ 1) :
    |∑ c, p c * finiteHaarMean (fun x =>
      finiteHaarMean (fun u : Fin d → Fin (Fintype.card Q / J) =>
      finiteHaarMean (fun v : Fin d → Fin (Fintype.card Q / J) =>
        subgroupCubeProduct Q d (h c) x (fun j => e c j (v j) - e c j (u j)))))| ≤
      (2 * (J : ℝ)) ^ d * weightedSubgroupGowersValue Q p (2 ^ d) h := by
  letI : NeZero (Fintype.card Q / J) := ⟨Nat.ne_of_gt hL⟩
  have hb := weightedShortIntervalDensityCube_bound Q p hp hsum d J hJ hL e he h hh
  simpa only [uniformImageTuplePair_expectation d _ (he _), Pi.sub_def] using hb

end Hindman168

