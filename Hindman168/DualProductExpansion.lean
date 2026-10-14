import Hindman168.DualProductApproximation

namespace Hindman168
open scoped BigOperators Classical

theorem finiteHaarMean_dependent_pi_prod {ι : Type*} [Fintype ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] (f : ∀ i, A i → ℝ) :
    finiteHaarMean (fun a : ∀ i, A i => ∏ i, f i (a i)) =
      ∏ i, finiteHaarMean (f i) := by
  simp only [finiteHaarMean, Finset.prod_div_distrib, ← Fintype.prod_sum,
    Fintype.card_pi, Nat.cast_prod]

theorem weighted_dual_product_correlation_expansion {G κ ι : Type*}
    [AddCommGroup G] [Fintype G] [Fintype κ] [Fintype ι]
    (Q : ι → AddSubgroup G) (d : ℕ) (p : κ → ℝ)
    (f : ι → κ → G → ℝ) (g : κ → G → ℝ) :
    (∑ c, p c * finiteHaarMean (fun x => g c x * ∏ i, subgroupDualFunction (Q i) d (f i c) x)) =
      finiteHaarMean (fun v : (i : ι) → (Fin d → Q i) =>
        ∑ c, p c * finiteHaarMean (fun x => g c x * ∏ i,
          ∏ ω ∈ (Finset.univ : Finset (Finset (Fin d))).erase ∅,
            f i c (x + ∑ j ∈ ω, (v i j : G)))) := by
  unfold subgroupDualFunction
  simp only [← finiteHaarMean_dependent_pi_prod, ← finiteHaarMean_const_mul]
  rw [finiteHaarMean_sum]
  apply Finset.sum_congr rfl
  intro c _
  exact finiteHaarMean_comm _

theorem weighted_dual_product_exists_translate_correlation {G κ ι : Type*}
    [AddCommGroup G] [Fintype G] [Fintype κ] [Fintype ι]
    (Q : ι → AddSubgroup G) (d : ℕ) (p : κ → ℝ)
    (f : ι → κ → G → ℝ) (g : κ → G → ℝ) :
    ∃ v : (i : ι) → (Fin d → Q i),
      (∑ c, p c * finiteHaarMean (fun x => g c x * ∏ i, subgroupDualFunction (Q i) d (f i c) x)) ≤
        ∑ c, p c * finiteHaarMean (fun x => g c x * ∏ i,
          ∏ ω ∈ (Finset.univ : Finset (Finset (Fin d))).erase ∅,
            f i c (x + ∑ j ∈ ω, (v i j : G))) := by
  rw [weighted_dual_product_correlation_expansion]
  let H := fun v : (i : ι) → (Fin d → Q i) =>
    ∑ c, p c * finiteHaarMean (fun x => g c x * ∏ i,
      ∏ ω ∈ (Finset.univ : Finset (Finset (Fin d))).erase ∅,
        f i c (x + ∑ j ∈ ω, (v i j : G)))
  obtain ⟨v, hv⟩ := finiteHaarMean_exists_le (fun v => -H v)
  refine ⟨v, ?_⟩
  have hn : finiteHaarMean (fun v => -H v) = -finiteHaarMean H := by
    simp only [finiteHaarMean, Finset.sum_neg_distrib, neg_div]
  rw [hn] at hv
  exact neg_le_neg_iff.mp hv

theorem empirical_dual_product_expansion {G κ ι : Type*}
    [AddCommGroup G] [Fintype G] [Fintype κ] [Fintype ι]
    (Q : ι → AddSubgroup G) (d m : ℕ)
    (s : (i : ι) → Fin m → (Fin d → Q i)) (f : ι → κ → G → ℝ) (c : κ) (x : G) :
    (∏ i, ((∑ j, ∏ ω ∈ (Finset.univ : Finset (Finset (Fin d))).erase ∅,
      f i c (x + ∑ k ∈ ω, (s i j k : G))) / m)) =
      finiteHaarMean (fun j : ι → Fin m => ∏ i,
        ∏ ω ∈ (Finset.univ : Finset (Finset (Fin d))).erase ∅,
          f i c (x + ∑ k ∈ ω, (s i (j i) k : G))) := by
  simpa only [finiteHaarMean, Fintype.card_fin] using
    (finiteHaarMean_dependent_pi_prod (fun (i : ι) (j : Fin m) =>
      ∏ ω ∈ (Finset.univ : Finset (Finset (Fin d))).erase ∅,
        f i c (x + ∑ k ∈ ω, (s i j k : G)))).symm

end Hindman168
