import Hindman168.FiniteHaarIdentities
import Hindman168.SubgroupCubeAverage

/-! Exact square identity for first-order subgroup correlations. -/
namespace Hindman168

variable {G : Type*} [AddCommGroup G] [Fintype G] (Q : AddSubgroup G) [Fintype Q]

noncomputable def subgroupHaarMean (h : G → ℝ) (x : G) : ℝ :=
  finiteHaarMean (fun a : Q => h (x + a))

omit [Fintype G] in
theorem subgroupHaarMean_translate (h : G → ℝ) (x : G) (a : Q) :
    subgroupHaarMean Q h (x + a) = subgroupHaarMean Q h x := by
  simpa only [subgroupHaarMean, AddSubgroup.coe_add, add_assoc] using
    finiteHaarMean_add_left (fun b : Q => h (x + b)) a

theorem subgroupHaar_correlation_square (h : G → ℝ) :
    finiteHaarMean (fun x => finiteHaarMean (fun a : Q => h x * h (x + a))) =
      finiteHaarMean (fun x => (subgroupHaarMean Q h x) ^ 2) := by
  simp only [finiteHaarMean_const_mul]
  change finiteHaarMean (fun x => h x * subgroupHaarMean Q h x) = _
  have hshift (a : Q) :
      finiteHaarMean (fun x => h (x + a) * subgroupHaarMean Q h (x + a)) =
        finiteHaarMean (fun x => h x * subgroupHaarMean Q h x) := by
    simpa only [add_comm] using finiteHaarMean_add_left (fun x => h x * subgroupHaarMean Q h x) (a : G)
  calc
    _ = finiteHaarMean (fun a : Q => finiteHaarMean
        (fun x => h (x + a) * subgroupHaarMean Q h (x + a))) := by
      simp only [hshift, finiteHaarMean_const]
    _ = finiteHaarMean (fun x => finiteHaarMean
        (fun a : Q => h (x + a) * subgroupHaarMean Q h (x + a))) := finiteHaarMean_comm _
    _ = _ := by
      simp only [subgroupHaarMean_translate, finiteHaarMean_mul_const]
      simp only [pow_two, subgroupHaarMean]

theorem subgroupHaar_correlation_nonneg (h : G → ℝ) :
    0 ≤ finiteHaarMean (fun x => finiteHaarMean (fun a : Q => h x * h (x + a))) := by
  rw [subgroupHaar_correlation_square]
  exact finiteHaarMean_nonneg _ (fun x => sq_nonneg _)

end Hindman168

