import Mathlib.Data.Finset.Max
import Mathlib.Tactic

namespace Hindman168
open scoped BigOperators Classical

/-- A genuine finite set of candidates with uniformly arbitrarily small
nonnegative errors contains one actual candidate with every error zero.
The finite minimum argument avoids division by a zero tolerance. -/
theorem finite_uniform_error_zero {α β : Type*} (s : Finset α) (hs : s.Nonempty)
    (I : Finset β) (f : α → β → ℝ) (hf : ∀ a ∈ s, ∀ i ∈ I, 0 ≤ f a i)
    (γ K : ℝ) (hγ : 0 < γ) (hK : 0 < K)
    (hsmall : ∀ ε : ℝ, 0 < ε → ε ≤ γ → ∃ a ∈ s, ∀ i ∈ I, f a i ≤ K*ε) :
    ∃ a ∈ s, ∀ i ∈ I, f a i = 0 := by
  obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image s (fun a => ∑ i ∈ I, f a i) hs
  have hsum0 : 0 ≤ ∑ i ∈ I, f a i := Finset.sum_nonneg (fun i hi => hf a ha i hi)
  have hzero : (∑ i ∈ I, f a i) = 0 := by
    by_contra hn
    have hpos : 0 < ∑ i ∈ I, f a i := lt_of_le_of_ne hsum0 (Ne.symm hn)
    have hIc : 0 < I.card := by
      by_contra hc
      have he : I=∅ := Finset.card_eq_zero.mp (by omega)
      simp only [he, Finset.sum_empty] at hpos
      exact (lt_irrefl 0) hpos
    have hIcr : (0 : ℝ) < I.card := by exact_mod_cast hIc
    let ε := min (γ/2) ((∑ i ∈ I, f a i)/(2*(I.card : ℝ)*K))
    have hε : 0 < ε := lt_min (by positivity) (by positivity)
    have hεγ : ε ≤ γ := (min_le_left _ _).trans (by linarith)
    obtain ⟨b, hb, herrors⟩ := hsmall ε hε hεγ
    have hsum : (∑ i ∈ I, f b i) ≤ (I.card : ℝ)*K*ε := by
      calc
        _ ≤ ∑ _i ∈ I, K*ε := Finset.sum_le_sum herrors
        _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
    have hεbound : ε*(2*(I.card : ℝ)*K) ≤ ∑ i ∈ I, f a i :=
      (le_div_iff₀ (by positivity : 0 < 2*(I.card : ℝ)*K)).mp (min_le_right _ _)
    have hm := hmin b hb
    nlinarith
  refine ⟨a, ha, ?_⟩
  intro i hi
  have hh := Finset.single_le_sum (fun j hj => hf a ha j hj) hi
  rw [hzero] at hh
  exact le_antisymm hh (hf a ha i hi)

end Hindman168
