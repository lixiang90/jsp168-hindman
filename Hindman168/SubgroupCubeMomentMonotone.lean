import Hindman168.SubgroupCubePositive
import Hindman168.FiniteHaarCauchySchwarz

namespace Hindman168
variable {G : Type*} [AddCommGroup G] [Fintype G] (Q : AddSubgroup G) [Fintype Q]

theorem subgroupHaarMean_integral (h : G → ℝ) :
    finiteHaarMean (subgroupHaarMean Q h) = finiteHaarMean h := by
  unfold subgroupHaarMean
  rw [finiteHaarMean_comm]
  have ht (a : Q) : finiteHaarMean (fun x => h (x + a)) = finiteHaarMean h := by
    simpa only [add_comm] using finiteHaarMean_add_left h (a : G)
  simp only [ht, finiteHaarMean_const]

theorem subgroupCubeAverage_square_le_succ (d : ℕ) (h : G → ℝ) :
    subgroupCubeAverage Q d h ^ 2 ≤ subgroupCubeAverage Q (d + 1) h := by
  rw [subgroupCubeAverage_succ_square]
  have he : subgroupCubeAverage Q d h = finiteHaarMean (fun v : Fin d → Q =>
      finiteHaarMean (subgroupHaarMean Q (fun x => subgroupCubeProduct Q d h x v))) := by
    simp only [subgroupHaarMean_integral]
    exact finiteHaarMean_comm _
  rw [he]
  exact (finiteHaarMean_square_le _).trans
    (finiteHaarMean_mono _ _ (fun v => finiteHaarMean_square_le _))

end Hindman168
