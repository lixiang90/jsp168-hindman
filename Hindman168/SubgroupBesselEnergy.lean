import Hindman168.SubgroupHaarComposition
import Hindman168.FiniteHaarCauchySchwarz
import Mathlib.Algebra.BigOperators.Field
import Hindman168.SubgroupGowersRoot

namespace Hindman168
open scoped BigOperators Classical

theorem finiteHaarMean_sum {ι α : Type*} [Fintype ι] [Fintype α] (f : ι → α → ℝ) :
    finiteHaarMean (fun x => ∑ i, f i x) = ∑ i, finiteHaarMean (f i) := by
  simp only [finiteHaarMean, ← Finset.sum_div]
  rw [Finset.sum_comm]

theorem subgroupHaarMean_weighted_square {G ι : Type*}
    [AddCommGroup G] [Fintype G] [Fintype ι]
    (Q : ι → AddSubgroup G) (p : ι → ℝ) (f : G → ℝ) :
    finiteHaarMean (fun x => (∑ i, p i * subgroupHaarMean (Q i) f x) ^ 2) =
      ∑ i, ∑ j, p i * p j * subgroupCubeAverage (Q i ⊔ Q j) 1 f := by
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum, finiteHaarMean_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = finiteHaarMean (fun x => (p i * p j) *
        (subgroupHaarMean (Q i) f x * subgroupHaarMean (Q j) f x)) := by
      congr 1
      funext x
      ring
    _ = _ := by rw [finiteHaarMean_const_mul, subgroupHaarMean_pair_energy]

theorem subgroup_first_bessel_energy {G ι : Type*}
    [AddCommGroup G] [Fintype G] [Fintype ι]
    (Q : ι → AddSubgroup G) (p : ι → ℝ) (f : G → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    (∑ i, p i * subgroupCubeAverage (Q i) 1 f) ^ 2 ≤
      ∑ i, ∑ j, p i * p j * subgroupCubeAverage (Q i ⊔ Q j) 1 f := by
  have he : finiteHaarMean (fun x => f x * (∑ i, p i * subgroupHaarMean (Q i) f x)) =
      ∑ i, p i * subgroupCubeAverage (Q i) 1 f := by
    simp only [Finset.mul_sum, finiteHaarMean_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hc : subgroupCubeAverage (Q i) 1 f =
        finiteHaarMean (fun x => f x * subgroupHaarMean (Q i) f x) := by
      rw [subgroupCubeAverage_one_dimension, ← subgroupHaar_correlation_square]
      simp only [finiteHaarMean_const_mul, subgroupHaarMean]
    rw [hc, ← finiteHaarMean_const_mul]
    congr 1
    funext x
    ring
  have hb := finiteHaarMean_discard_unit_factor f
    (fun x => ∑ i, p i * subgroupHaarMean (Q i) f x) hf
  rwa [he, subgroupHaarMean_weighted_square] at hb

theorem probability_weighted_square_le {ι : Type*} [Fintype ι]
    (p f : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    (∑ i, p i * f i) ^ 2 ≤ ∑ i, p i * (f i) ^ 2 := by
  let m := ∑ i, p i * f i
  have hn : 0 ≤ ∑ i, p i * (f i - m) ^ 2 :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hp i) (sq_nonneg _))
  have he : (∑ i, p i * (f i - m) ^ 2) = (∑ i, p i * f i ^ 2) - m ^ 2 := by
    have hi (i : ι) : p i * (f i - m) ^ 2 = p i * f i ^ 2 - 2 * m * (p i * f i) + m ^ 2 * p i := by ring
    simp_rw [hi]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hs]
    change (∑ i, p i * f i ^ 2) - 2 * m * m + m ^ 2 * 1 = _
    ring
  rw [he] at hn
  exact sub_nonneg.mp hn

theorem weighted_subgroup_first_bessel_energy {G ι κ : Type*}
    [AddCommGroup G] [Fintype G] [Fintype ι] [Fintype κ]
    (Q : ι → AddSubgroup G) (p : ι → ℝ)
    (α : κ → ℝ) (hα : ∀ c, 0 ≤ α c) (hs : ∑ c, α c = 1)
    (f : κ → G → ℝ) (hf : ∀ c x, |f c x| ≤ 1) :
    (∑ i, p i * weightedSubgroupCubeAverage α (Q i) 1 f) ^ 2 ≤
      ∑ i, ∑ j, p i * p j * weightedSubgroupCubeAverage α (Q i ⊔ Q j) 1 f := by
  have he : (∑ i, p i * weightedSubgroupCubeAverage α (Q i) 1 f) =
      ∑ c, α c * (∑ i, p i * subgroupCubeAverage (Q i) 1 (f c)) := by
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
    _ ≤ ∑ c, α c * (∑ i, ∑ j, p i * p j * subgroupCubeAverage (Q i ⊔ Q j) 1 (f c)) :=
      Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left
        (subgroup_first_bessel_energy Q p (f c) (hf c)) (hα c))
    _ = _ := by
      simp only [weightedSubgroupCubeAverage, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro c _
      ring

theorem weighted_subgroup_first_bessel_quartic {G ι κ : Type*}
    [AddCommGroup G] [Fintype G] [Fintype ι] [Fintype κ]
    (Q : ι → AddSubgroup G) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (α : κ → ℝ) (hα : ∀ c, 0 ≤ α c) (hs : ∑ c, α c = 1)
    (f : κ → G → ℝ) (hf : ∀ c x, |f c x| ≤ 1) :
    (∑ i, p i * weightedSubgroupGowersValue (Q i) α 1 f) ^ 4 ≤
      ∑ i, ∑ j, p i * p j * weightedSubgroupGowersValue (Q i ⊔ Q j) α 1 f := by
  have he (R : AddSubgroup G) : weightedSubgroupGowersValue R α 1 f ^ 2 =
      weightedSubgroupCubeAverage α R 1 f := by
    unfold weightedSubgroupGowersValue
    exact Real.rpow_inv_natCast_pow (weightedSubgroupCubeAverage_nonneg R α hα 1 (by decide) f) (by decide)
  have ha := probability_weighted_square_le p (fun i => weightedSubgroupGowersValue (Q i) α 1 f) hp hpsum
  simp_rw [he] at ha
  calc
    _ = ((∑ i, p i * weightedSubgroupGowersValue (Q i) α 1 f) ^ 2) ^ 2 := by ring
    _ ≤ (∑ i, p i * weightedSubgroupCubeAverage α (Q i) 1 f) ^ 2 :=
      pow_le_pow_left₀ (sq_nonneg _) ha 2
    _ ≤ ∑ i, ∑ j, p i * p j * weightedSubgroupCubeAverage α (Q i ⊔ Q j) 1 f :=
      weighted_subgroup_first_bessel_energy Q p α hα hs f hf
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hp i) (hp j))
      rw [← he]
      have h0 := weightedSubgroupGowersValue_nonneg (Q i ⊔ Q j) α hα 1 (by decide) f
      have h1 := weightedSubgroupGowersValue_le_one (Q i ⊔ Q j) α hα hs 1 (by decide) f hf
      nlinarith

end Hindman168
