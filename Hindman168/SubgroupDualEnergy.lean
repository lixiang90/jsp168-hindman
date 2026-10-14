import Hindman168.SubgroupBesselEnergy

namespace Hindman168
open scoped BigOperators Classical

noncomputable def subgroupDualFunction {G : Type*} [AddCommGroup G]
    (Q : AddSubgroup G) [Fintype Q] (d : ℕ) (f : G → ℝ) (x : G) : ℝ :=
  finiteHaarMean (fun v : Fin d → Q =>
    ∏ ω ∈ (Finset.univ : Finset (Finset (Fin d))).erase ∅, f (x + ∑ j ∈ ω, (v j : G)))

theorem subgroupDualFunction_abs_le_one {G : Type*} [AddCommGroup G]
    (Q : AddSubgroup G) [Fintype Q] (d : ℕ) (f : G → ℝ) (hf : ∀ x, |f x| ≤ 1) (x : G) :
    |subgroupDualFunction Q d f x| ≤ 1 := by
  apply finiteHaarMean_abs_le_one
  intro v
  rw [Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun _ _ => hf _)

theorem subgroupCubeAverage_dual_correlation {G : Type*} [AddCommGroup G] [Fintype G]
    (Q : AddSubgroup G) [Fintype Q] (d : ℕ) (f : G → ℝ) :
    subgroupCubeAverage Q d f = finiteHaarMean (fun x => f x * subgroupDualFunction Q d f x) := by
  unfold subgroupCubeAverage subgroupDualFunction
  simp only [← finiteHaarMean_const_mul]
  congr 1
  funext x
  congr 1
  funext v
  unfold subgroupCubeProduct
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (∅ : Finset (Fin d)))]
  simp only [Finset.sum_empty, add_zero]

theorem subgroupDualFunction_one {G : Type*} [AddCommGroup G]
    (Q : AddSubgroup G) [Fintype Q] (f : G → ℝ) (x : G) :
    subgroupDualFunction Q 1 f x = subgroupHaarMean Q f x := by
  have he : (Finset.univ : Finset (Finset (Fin 1))).erase ∅ = {{0}} := by decide
  simp only [subgroupDualFunction, he, Finset.prod_singleton, Finset.sum_singleton]
  exact finiteHaarMean_equiv (Equiv.funUnique (Fin 1) Q) (fun a => f (x + a))

theorem finiteHaarMean_weighted_square {G ι : Type*} [Fintype G] [Fintype ι]
    (p : ι → ℝ) (g : ι → G → ℝ) :
    finiteHaarMean (fun x => (∑ i, p i * g i x) ^ 2) =
      ∑ i, ∑ j, p i * p j * finiteHaarMean (fun x => g i x * g j x) := by
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum, finiteHaarMean_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← finiteHaarMean_const_mul]
  congr 1
  funext x
  ring

theorem subgroup_dual_bessel_energy {G ι : Type*}
    [AddCommGroup G] [Fintype G] [Fintype ι]
    (Q : ι → AddSubgroup G) (p : ι → ℝ) (d : ℕ)
    (f : G → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    (∑ i, p i * subgroupCubeAverage (Q i) d f) ^ 2 ≤
      ∑ i, ∑ j, p i * p j * finiteHaarMean
        (fun x => subgroupDualFunction (Q i) d f x * subgroupDualFunction (Q j) d f x) := by
  have he : finiteHaarMean (fun x => f x * (∑ i, p i * subgroupDualFunction (Q i) d f x)) =
      ∑ i, p i * subgroupCubeAverage (Q i) d f := by
    simp only [Finset.mul_sum, finiteHaarMean_sum, subgroupCubeAverage_dual_correlation]
    apply Finset.sum_congr rfl
    intro i _
    rw [← finiteHaarMean_const_mul]
    congr 1
    funext x
    ring
  have hb := finiteHaarMean_discard_unit_factor f
    (fun x => ∑ i, p i * subgroupDualFunction (Q i) d f x) hf
  rwa [he, finiteHaarMean_weighted_square] at hb

theorem weighted_subgroup_dual_bessel_energy {G ι κ : Type*}
    [AddCommGroup G] [Fintype G] [Fintype ι] [Fintype κ]
    (Q : ι → AddSubgroup G) (p : ι → ℝ) (d : ℕ)
    (α : κ → ℝ) (hα : ∀ c, 0 ≤ α c) (hs : ∑ c, α c = 1)
    (f : κ → G → ℝ) (hf : ∀ c x, |f c x| ≤ 1) :
    (∑ i, p i * weightedSubgroupCubeAverage α (Q i) d f) ^ 2 ≤
      ∑ i, ∑ j, p i * p j * (∑ c, α c * finiteHaarMean
        (fun x => subgroupDualFunction (Q i) d (f c) x * subgroupDualFunction (Q j) d (f c) x)) := by
  have he : (∑ i, p i * weightedSubgroupCubeAverage α (Q i) d f) =
      ∑ c, α c * (∑ i, p i * subgroupCubeAverage (Q i) d (f c)) := by
    simp only [weightedSubgroupCubeAverage, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  refine (probability_weighted_square_le α _ hα hs).trans ?_
  calc
    _ ≤ ∑ c, α c * (∑ i, ∑ j, p i * p j * finiteHaarMean
        (fun x => subgroupDualFunction (Q i) d (f c) x * subgroupDualFunction (Q j) d (f c) x)) :=
      Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left
        (subgroup_dual_bessel_energy Q p d (f c) (hf c)) (hα c))
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro c _
      ring

end Hindman168
