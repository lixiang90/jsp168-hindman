import Hindman168.SubgroupCubePositive
import Hindman168.FiniteHaarCauchySchwarz

namespace Hindman168
open scoped BigOperators Classical

/-- Removing all nonroot unit factors bounds each face square by its
root square, including the zero-dimensional face. -/
theorem subgroupCubeProduct_sq_le_root_sq {G : Type*} [AddCommGroup G]
    (Q : AddSubgroup G) (d : ℕ) (f : G → ℝ) (hf : ∀ x, |f x| ≤ 1)
    (x : G) (v : Fin d → Q) :
    subgroupCubeProduct Q d f x v ^ 2 ≤ f x ^ 2 := by
  unfold subgroupCubeProduct
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (∅ : Finset (Fin d)))]
  simp only [Finset.sum_empty, add_zero, mul_pow]
  have hb : |∏ ω ∈ (Finset.univ : Finset (Finset (Fin d))).erase ∅,
      f (x + ∑ j ∈ ω, (v j : G))| ≤ 1 := by
    rw [Finset.abs_prod]
    exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun _ _ => hf _)
  have hs : (∏ ω ∈ (Finset.univ : Finset (Finset (Fin d))).erase ∅,
      f (x + ∑ j ∈ ω, (v j : G))) ^ 2 ≤ 1 := by
    nlinarith [abs_nonneg (∏ ω ∈ (Finset.univ : Finset (Finset (Fin d))).erase ∅,
      f (x + ∑ j ∈ ω, (v j : G))), sq_abs (∏ ω ∈
      (Finset.univ : Finset (Finset (Fin d))).erase ∅, f (x + ∑ j ∈ ω, (v j : G)))]
  exact (mul_le_mul_of_nonneg_left hs (sq_nonneg _)).trans_eq (mul_one _)

/-- Every positive-order genuine subgroup cube of a unit-bounded real
function is bounded by its ambient Haar L2 energy. -/
theorem subgroupCubeAverage_le_L2_energy {G : Type*} [AddCommGroup G] [Fintype G]
    (Q : AddSubgroup G) [Fintype Q] (d : ℕ) (hd : 0 < d)
    (f : G → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    subgroupCubeAverage Q d f ≤ finiteHaarMean (fun x => f x ^ 2) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  rw [subgroupCubeAverage_succ_square]
  refine (finiteHaarMean_mono _ (fun _ : Fin k → Q => finiteHaarMean (fun x => f x ^ 2)) ?_).trans_eq
    (finiteHaarMean_const _)
  intro v
  calc
    _ ≤ finiteHaarMean (fun x => finiteHaarMean (fun a : Q =>
        subgroupCubeProduct Q k f (x + a) v ^ 2)) :=
      finiteHaarMean_mono _ _ (fun x => finiteHaarMean_square_le
        (fun a : Q => subgroupCubeProduct Q k f (x + a) v))
    _ = finiteHaarMean (fun x => subgroupCubeProduct Q k f x v ^ 2) := by
      rw [finiteHaarMean_comm]
      have ht (a : Q) : finiteHaarMean (fun x => subgroupCubeProduct Q k f (x + a) v ^ 2) =
          finiteHaarMean (fun x => subgroupCubeProduct Q k f x v ^ 2) :=
        finiteHaarMean_equiv (Equiv.addRight (a : G)) (fun x => subgroupCubeProduct Q k f x v ^ 2)
      simp_rw [ht]
      exact finiteHaarMean_const _
    _ ≤ _ := finiteHaarMean_mono _ _ (fun x => subgroupCubeProduct_sq_le_root_sq Q k f hf x v)

/-- The cube-to-energy estimate integrates the original nonnegative cell
weights directly; no normalization or change of the cell law is needed. -/
theorem weightedSubgroupCubeAverage_le_L2_energy {G κ : Type*}
    [AddCommGroup G] [Fintype G] [Fintype κ]
    (Q : AddSubgroup G) [Fintype Q] (p : κ → ℝ) (hp : ∀ c, 0 ≤ p c)
    (d : ℕ) (hd : 0 < d) (f : κ → G → ℝ) (hf : ∀ c x, |f c x| ≤ 1) :
    weightedSubgroupCubeAverage p Q d f ≤ ∑ c, p c * finiteHaarMean (fun x => f c x ^ 2) := by
  exact Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left
    (subgroupCubeAverage_le_L2_energy Q d hd (f c) (hf c)) (hp c))

end Hindman168
