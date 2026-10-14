import Hindman168.UniformTupleExpectation
import Hindman168.IndependentDifferenceCubeBound

namespace Hindman168
open scoped BigOperators
variable {G : Type*} [AddCommGroup G] [Fintype G] (Q : AddSubgroup G) [Fintype Q]

theorem weightedUniformImageCube_bound {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]
    (p : ι → ℝ) (hp : ∀ c, 0 ≤ p c) (hsum : ∑ c, p c = 1)
    (d : ℕ) (C : ℝ) (hC : 0 < C) (hsize : (Fintype.card Q : ℝ) / Fintype.card S ≤ C)
    (e : ι → Fin d → S → Q) (he : ∀ c j, Function.Injective (e c j))
    (h : ι → G → ℝ) (hh : ∀ c x, |h c x| ≤ 1) :
    |∑ c, p c * finiteHaarMean (fun x => finiteHaarMean (fun u : Fin d → S =>
      finiteHaarMean (fun v : Fin d → S =>
        subgroupCubeProduct Q d (h c) x (fun j => e c j (v j) - e c j (u j)))))| ≤
      C ^ d * weightedSubgroupGowersValue Q p (2 ^ d) h := by
  have hb := weightedIndependentDifferenceCube_bound Q p hp hsum d
    (fun c j => uniformImageHaarDensity (e c j))
    (fun c j => uniformImageHaarDensity_nonneg (e c j))
    (fun c j => uniformImageHaarDensity_total (e c j) (he c j)) C hC
    (fun c j a => (uniformImageHaarDensity_le (e c j) a).trans hsize) h hh
  simpa only [uniformImageTuplePair_expectation d _ (he _), Pi.sub_def] using hb

end Hindman168
