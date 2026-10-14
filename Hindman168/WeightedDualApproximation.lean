import Hindman168.HaarSamplingVariance

namespace Hindman168
open scoped BigOperators Classical

theorem finiteHaarMean_sample_variance_le {A : Type*} [Fintype A] [Nonempty A]
    (h : A → ℝ) (hh : ∀ a, |h a| ≤ 1) (m : ℕ) (hm : 0 < m) :
    finiteHaarMean (fun s : Fin m → A => ((∑ j, h (s j)) / m - finiteHaarMean h) ^ 2) ≤
      1 / (m : ℝ) := by
  rw [finiteHaarMean_sample_variance h m hm]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg m)
  have hb : finiteHaarMean (fun a => h a ^ 2) ≤ 1 := by
    refine (finiteHaarMean_mono _ (fun _ : A => (1 : ℝ)) (fun a => ?_)).trans_eq (finiteHaarMean_const _)
    have ha := hh a
    have hn := abs_nonneg (h a)
    have he := sq_abs (h a)
    nlinarith
  nlinarith [sq_nonneg (finiteHaarMean h)]

theorem weightedHaar_exists_sample_L2 {A X κ : Type*} [Fintype A] [Nonempty A]
    [Fintype X] [Nonempty X] [Fintype κ]
    (p : κ → ℝ) (hp : ∀ c, 0 ≤ p c) (hs : ∑ c, p c = 1)
    (F : A → κ → X → ℝ) (hF : ∀ a c x, |F a c x| ≤ 1) (m : ℕ) (hm : 0 < m) :
    ∃ s : Fin m → A, (∑ c, p c * finiteHaarMean (fun x =>
      ((∑ j, F (s j) c x) / m - finiteHaarMean (fun a => F a c x)) ^ 2)) ≤ 1 / (m : ℝ) := by
  let e := fun (s : Fin m → A) (c : κ) (x : X) =>
    ((∑ j, F (s j) c x) / m - finiteHaarMean (fun a => F a c x)) ^ 2
  obtain ⟨s, hsamp⟩ := finiteHaarMean_exists_le (fun s => ∑ c, p c * finiteHaarMean (e s c))
  refine ⟨s, hsamp.trans ?_⟩
  rw [finiteHaarMean_sum]
  simp only [finiteHaarMean_const_mul]
  calc
    _ ≤ ∑ c, p c * (1 / (m : ℝ)) := by
      apply Finset.sum_le_sum
      intro c _
      apply mul_le_mul_of_nonneg_left _ (hp c)
      rw [finiteHaarMean_comm]
      refine (finiteHaarMean_mono _ (fun _ : X => 1 / (m : ℝ)) (fun x => ?_)).trans_eq (finiteHaarMean_const _)
      exact finiteHaarMean_sample_variance_le (fun a => F a c x) (fun a => hF a c x) m hm
    _ = _ := by rw [← Finset.sum_mul, hs, one_mul]

theorem weightedHaar_discard_unit_factor {X κ : Type*} [Fintype X] [Nonempty X] [Fintype κ]
    (p : κ → ℝ) (hp : ∀ c, 0 ≤ p c) (hs : ∑ c, p c = 1)
    (g e : κ → X → ℝ) (hg : ∀ c x, |g c x| ≤ 1) :
    (∑ c, p c * finiteHaarMean (fun x => g c x * e c x)) ^ 2 ≤
      ∑ c, p c * finiteHaarMean (fun x => e c x ^ 2) := by
  refine (probability_weighted_square_le p _ hp hs).trans ?_
  exact Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left
    (finiteHaarMean_discard_unit_factor (g c) (e c) (hg c)) (hp c))

theorem weighted_subgroupDualFunction_exists_approximation {G κ : Type*}
    [AddCommGroup G] [Fintype G] [Fintype κ]
    (Q : AddSubgroup G) [Fintype Q] (d : ℕ)
    (p : κ → ℝ) (hp : ∀ c, 0 ≤ p c) (hs : ∑ c, p c = 1)
    (f : κ → G → ℝ) (hf : ∀ c x, |f c x| ≤ 1) (m : ℕ) (hm : 0 < m) :
    ∃ s : Fin m → (Fin d → Q),
      let a := fun (c : κ) (x : G) => (∑ j, ∏ ω ∈ (Finset.univ : Finset (Finset (Fin d))).erase ∅,
        f c (x + ∑ k ∈ ω, (s j k : G))) / m
      (∀ c x, |a c x| ≤ 1) ∧
      (∑ c, p c * finiteHaarMean (fun x => (a c x - subgroupDualFunction Q d (f c) x) ^ 2)) ≤
        1 / (m : ℝ) ∧
      ∀ g : κ → G → ℝ, (∀ c x, |g c x| ≤ 1) →
        (∑ c, p c * finiteHaarMean (fun x => g c x * (a c x - subgroupDualFunction Q d (f c) x))) ^ 2 ≤
          1 / (m : ℝ) := by
  let F := fun (v : Fin d → Q) (c : κ) (x : G) =>
    ∏ ω ∈ (Finset.univ : Finset (Finset (Fin d))).erase ∅, f c (x + ∑ k ∈ ω, (v k : G))
  have hF (v : Fin d → Q) (c : κ) (x : G) : |F v c x| ≤ 1 := by
    dsimp only [F]
    rw [Finset.abs_prod]
    exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun _ _ => hf c _)
  obtain ⟨s, he⟩ := weightedHaar_exists_sample_L2 p hp hs F hF m hm
  refine ⟨s, ?_, he, ?_⟩
  · intro c x
    letI : NeZero m := ⟨hm.ne'⟩
    simpa only [finiteHaarMean, Fintype.card_fin, F] using
      finiteHaarMean_abs_le_one (fun j : Fin m => F (s j) c x) (fun j => hF (s j) c x)
  · intro g hg
    exact (weightedHaar_discard_unit_factor p hp hs g _ hg).trans he

end Hindman168
