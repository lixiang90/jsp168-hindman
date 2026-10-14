import Hindman168.RoughMonomialOscillation

namespace Hindman168

theorem rough_unit_product_difference {ι : Type*} (s : Finset ι) (p q : ι → ℝ)
    (hp : ∀ j ∈ s, |p j| ≤ 1) (hq : ∀ j ∈ s, |q j| ≤ 1) :
    |(∏ j ∈ s, p j) - ∏ j ∈ s, q j| ≤ ∑ j ∈ s, |p j - q j| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    have hps := fun i hi => hp i (Finset.mem_insert_of_mem hi)
    have hqs := fun i hi => hq i (Finset.mem_insert_of_mem hi)
    have hb : |∏ i ∈ s, q i| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one (fun _ _ => abs_nonneg _) hqs
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj]
    calc
      _ = |p j * ((∏ i ∈ s, p i) - ∏ i ∈ s, q i) +
        (p j - q j) * ∏ i ∈ s, q i| := by congr 1; ring
      _ ≤ |p j| * |(∏ i ∈ s, p i) - ∏ i ∈ s, q i| +
        |p j - q j| * |∏ i ∈ s, q i| := by
        simpa only [abs_mul] using abs_add_le
          (p j * ((∏ i ∈ s, p i) - ∏ i ∈ s, q i)) ((p j - q j) * ∏ i ∈ s, q i)
      _ ≤ ∑ i ∈ s, |p i - q i| + |p j - q j| := by
        have h1 := mul_le_mul (hp j (Finset.mem_insert_self _ _)) (ih hps hqs)
          (abs_nonneg _) (by positivity : (0 : ℝ) ≤ 1)
        have h2 := mul_le_mul_of_nonneg_left hb (abs_nonneg (p j - q j))
        simpa only [one_mul, mul_one] using add_le_add h1 h2
      _ = _ := add_comm _ _

theorem rough_unit_product_error {ι : Type*} [Fintype ι] (p q e : ι → ℝ)
    (hp : ∀ j, |p j| ≤ 1) (hq : ∀ j, |q j| ≤ 1)
    (he : ∀ j, |p j - q j| ≤ e j) :
    |(∏ j, p j) - ∏ j, q j| ≤ ∑ j, e j := by
  exact (rough_unit_product_difference Finset.univ p q (fun j _ => hp j) (fun j _ => hq j)).trans
    (Finset.sum_le_sum (fun j _ => he j))

end Hindman168
