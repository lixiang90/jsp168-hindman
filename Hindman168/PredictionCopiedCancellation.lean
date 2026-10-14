import Hindman168.PredictionMajorantCancellation

/-!
# All copied root differences cancel under the common original law

The final prediction expression has many distinct copies of (nu-1), not
just one. Disjoint centered and retained row sets give a signed subset
expansion. Its common main term vanishes for any nonempty centered set,
even when that main term is an arbitrary varying event probability.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

noncomputable def centeredSubsetSign {ι : Type*} (Γ S : Finset ι) : ℝ :=
  ∏ _u ∈ Γ \ S, (-1 : ℝ)

theorem centeredSubsetSign_sum_zero {ι : Type*} (Γ : Finset ι) (hΓ : Γ.Nonempty) :
    ∑ S ∈ Γ.powerset, centeredSubsetSign Γ S = 0 := by
  have he := Finset.prod_add (fun _ : ι => (1 : ℝ)) (fun _ => (-1 : ℝ)) Γ
  simp only [Finset.prod_const_one, one_mul] at he
  have hz : (∏ u ∈ Γ, ((1 : ℝ) + -1)) = 0 := by
    obtain ⟨u, hu⟩ := hΓ
    exact Finset.prod_eq_zero hu (by norm_num)
  exact he.symm.trans hz

theorem centered_majorant_product_expansion {ι : Type*}
    (ν : ι → ℝ) (Γ U : Finset ι) (hdisjoint : Disjoint Γ U) :
    (∏ u ∈ Γ, (ν u - 1)) * (∏ u ∈ U, (1 + ν u)) =
      ∑ S ∈ Γ.powerset, ∑ T ∈ U.powerset,
        centeredSubsetSign Γ S * ∏ u ∈ S ∪ T, ν u := by
  simp only [sub_eq_add_neg]
  rw [Finset.prod_add, Finset.prod_one_add, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  have hST := hdisjoint.mono (Finset.mem_powerset.mp hS) (Finset.mem_powerset.mp hT)
  rw [Finset.prod_union hST]
  unfold centeredSubsetSign
  simp only [mul_assoc, mul_left_comm, mul_comm]

theorem conditionalFiniteAverage_mul_const {α β : Type*} (μ : Mass α)
    (base : α → Mass β) (E : α → Prop) (c : ℝ) (f : α → β → ℝ) :
    conditionalFiniteAverage μ base E (fun x y => c * f x y) =
      c * conditionalFiniteAverage μ base E f := by
  unfold conditionalFiniteAverage expectation Finsupp.sum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  dsimp only
  split_ifs <;> simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

theorem centered_majorant_average_expansion {α β ι : Type*}
    (μ : Mass α) (base : α → Mass β) (E : α → Prop)
    (ν : ι → α → β → ℝ) (Γ U : Finset ι) (hdisjoint : Disjoint Γ U) :
    conditionalFiniteAverage μ base E
      (fun x y => (∏ u ∈ Γ, (ν u x y - 1)) * ∏ u ∈ U, (1 + ν u x y)) =
      ∑ S ∈ Γ.powerset, ∑ T ∈ U.powerset,
        centeredSubsetSign Γ S * conditionalFiniteAverage μ base E
          (fun x y => ∏ u ∈ S ∪ T, ν u x y) := by
  have he : (fun x y => (∏ u ∈ Γ, (ν u x y - 1)) * ∏ u ∈ U, (1 + ν u x y)) =
      (fun x y => ∑ S ∈ Γ.powerset, ∑ T ∈ U.powerset,
        centeredSubsetSign Γ S * ∏ u ∈ S ∪ T, ν u x y) := by
    funext x y
    exact centered_majorant_product_expansion (fun u => ν u x y) Γ U hdisjoint
  rw [he, conditionalFiniteAverage_sum]
  simp_rw [conditionalFiniteAverage_sum, conditionalFiniteAverage_mul_const]

theorem centered_majorant_main_term_zero {ι : Type*} (Γ U : Finset ι)
    (hΓ : Γ.Nonempty) (k : ℝ) :
    (∑ S ∈ Γ.powerset, ∑ _T ∈ U.powerset, centeredSubsetSign Γ S * k) = 0 := by
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, centeredSubsetSign_sum_zero Γ hΓ, zero_mul,
    Finset.sum_const_zero]

theorem centered_majorant_average_error_expansion {α β ι : Type*}
    (μ : Mass α) (base : α → Mass β) (E : α → Prop)
    (ν : ι → α → β → ℝ) (Γ U : Finset ι) (hdisjoint : Disjoint Γ U)
    (hΓ : Γ.Nonempty) (k : ℝ) :
    conditionalFiniteAverage μ base E
      (fun x y => (∏ u ∈ Γ, (ν u x y - 1)) * ∏ u ∈ U, (1 + ν u x y)) =
      ∑ S ∈ Γ.powerset, ∑ T ∈ U.powerset,
        centeredSubsetSign Γ S * (conditionalFiniteAverage μ base E
          (fun x y => ∏ u ∈ S ∪ T, ν u x y) - k) := by
  rw [centered_majorant_average_expansion μ base E ν Γ U hdisjoint]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [centered_majorant_main_term_zero Γ U hΓ k, sub_zero]

theorem centered_majorant_average_tendsto_zero {α β ι : Type*}
    (μ : ℕ → Mass α) (base : ℕ → α → Mass β) (E : ℕ → α → Prop)
    (ν : ℕ → ι → α → β → ℝ) (Γ U : Finset ι) (hdisjoint : Disjoint Γ U)
    (hΓ : Γ.Nonempty) (k : ℕ → ℝ)
    (hmean : ∀ S : Finset ι, S ⊆ Γ ∪ U →
      Tendsto (fun w => conditionalFiniteAverage (μ w) (base w) (E w)
        (fun x y => ∏ u ∈ S, ν w u x y) - k w) atTop (𝓝 0)) :
    Tendsto (fun w => conditionalFiniteAverage (μ w) (base w) (E w)
      (fun x y => (∏ u ∈ Γ, (ν w u x y - 1)) * ∏ u ∈ U, (1 + ν w u x y)))
      atTop (𝓝 0) := by
  have he (w : ℕ) := centered_majorant_average_error_expansion
    (μ w) (base w) (E w) (ν w) Γ U hdisjoint hΓ (k w)
  simp_rw [he]
  have houter (S : Finset ι) (hS : S ∈ Γ.powerset) :
      Tendsto (fun w => ∑ T ∈ U.powerset, centeredSubsetSign Γ S *
        (conditionalFiniteAverage (μ w) (base w) (E w)
          (fun x y => ∏ u ∈ S ∪ T, ν w u x y) - k w)) atTop (𝓝 0) := by
    have hinner (T : Finset ι) (hT : T ∈ U.powerset) :
        Tendsto (fun w => centeredSubsetSign Γ S *
          (conditionalFiniteAverage (μ w) (base w) (E w)
            (fun x y => ∏ u ∈ S ∪ T, ν w u x y) - k w)) atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul
        (hmean (S ∪ T) (Finset.union_subset_union
          (Finset.mem_powerset.mp hS) (Finset.mem_powerset.mp hT)))
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum U.powerset hinner
  simpa only [Finset.sum_const_zero] using tendsto_finsetSum Γ.powerset houter


theorem retained_majorant_average_expansion {α β ι : Type*}
    (μ : Mass α) (base : α → Mass β) (E : α → Prop)
    (ν : ι → α → β → ℝ) (U : Finset ι) :
    conditionalFiniteAverage μ base E (fun x y => ∏ u ∈ U, (1 + ν u x y)) =
      ∑ S ∈ U.powerset, conditionalFiniteAverage μ base E (fun x y => ∏ u ∈ S, ν u x y) := by
  have he : (fun x y => ∏ u ∈ U, (1 + ν u x y)) =
      (fun x y => ∑ S ∈ U.powerset, ∏ u ∈ S, ν u x y) := by
    funext x y
    exact Finset.prod_one_add U
  rw [he, conditionalFiniteAverage_sum]

theorem retained_majorant_average_error_expansion {α β ι : Type*}
    (μ : Mass α) (base : α → Mass β) (E : α → Prop)
    (ν : ι → α → β → ℝ) (U : Finset ι) (k : ℝ) :
    conditionalFiniteAverage μ base E (fun x y => ∏ u ∈ U, (1 + ν u x y)) -
      ((2 ^ U.card : ℕ) : ℝ) * k =
      ∑ S ∈ U.powerset,
        (conditionalFiniteAverage μ base E (fun x y => ∏ u ∈ S, ν u x y) - k) := by
  rw [retained_majorant_average_expansion, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]

theorem retained_majorant_average_mean_one {α β ι : Type*}
    (μ : ℕ → Mass α) (base : ℕ → α → Mass β) (E : ℕ → α → Prop)
    (ν : ℕ → ι → α → β → ℝ) (U : Finset ι) (k : ℕ → ℝ)
    (hmean : ∀ S : Finset ι, S ⊆ U →
      Tendsto (fun w => conditionalFiniteAverage (μ w) (base w) (E w)
        (fun x y => ∏ u ∈ S, ν w u x y) - k w) atTop (𝓝 0)) :
    Tendsto (fun w => conditionalFiniteAverage (μ w) (base w) (E w)
      (fun x y => ∏ u ∈ U, (1 + ν w u x y)) - ((2 ^ U.card : ℕ) : ℝ) * k w)
      atTop (𝓝 0) := by
  have he (w : ℕ) := retained_majorant_average_error_expansion
    (μ w) (base w) (E w) (ν w) U (k w)
  simp_rw [he]
  simpa only [Finset.sum_const_zero] using tendsto_finsetSum U.powerset
    (fun S hS => hmean S (Finset.mem_powerset.mp hS))

theorem varying_event_mean_eventually_le {a k : ℕ → ℝ} (c : ℝ) (hc : 0 ≤ c)
    (hk : ∀ᶠ w in atTop, k w ≤ 1)
    (hmean : Tendsto (fun w => a w - c * k w) atTop (𝓝 0)) :
    ∀ᶠ w in atTop, a w ≤ c + 1 := by
  have he := hmean.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hk, he] with w hw hm
  have hbound : c * k w ≤ c := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hw hc
  change a w - c * k w < 1 at hm
  linarith

end Hindman168
