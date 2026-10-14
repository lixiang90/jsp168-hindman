import Hindman168.WeightedDualApproximation
import Hindman168.WeightedHaarTranslation

namespace Hindman168
open scoped BigOperators Classical

theorem weightedHaarMean_internal_comm {A X κ : Type*}
    [Fintype A] [Fintype X] [Fintype κ] (p : κ → ℝ) (F : A → κ → X → ℝ) :
    finiteHaarMean (fun a => ∑ c, p c * finiteHaarMean (F a c)) =
      ∑ c, p c * finiteHaarMean (fun x => finiteHaarMean (fun a => F a c x)) := by
  rw [finiteHaarMean_sum]
  simp only [finiteHaarMean_const_mul]
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  exact finiteHaarMean_comm _

theorem finiteHaarMean_square_eq_pair {A : Type*} [Fintype A] (f : A → ℝ) :
    finiteHaarMean f ^ 2 = finiteHaarMean (fun a => finiteHaarMean (fun b => f a * f b)) := by
  simp only [finiteHaarMean_const_mul, finiteHaarMean_mul_const, pow_two]

theorem weightedHaar_correlation_translate {G κ : Type*}
    [AddCommGroup G] [Fintype G] [Fintype κ] (p : κ → ℝ)
    (f g : κ → G → ℝ) (s : κ → G) :
    (∑ c, p c * finiteHaarMean (fun x => f c (x + s c) * g c (x + s c))) =
      ∑ c, p c * finiteHaarMean (fun x => f c x * g c x) := by
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  exact finiteHaarMean_equiv (Equiv.addRight (s c)) (fun x => f c x * g c x)

/-- The original cell probabilities are unchanged in the correlation
duplication estimate for an actual translated recursive representation.
Only the core functions require unit bounds. -/
theorem weightedHaar_recursive_correlation_square_le
    {G κ A B : Type*} [AddCommGroup G] [Fintype G] [Fintype κ]
    [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (p : κ → ℝ) (hp : ∀ c, 0 ≤ p c) (hs : ∑ c, p c = 1)
    (f g : κ → G → ℝ) (s : A → κ → G)
    (C : A → B → κ → G → ℝ) (H : B → κ → G → ℝ)
    (hH : ∀ b c x, |H b c x| ≤ 1)
    (hexp : ∀ a c x, f c (x + s a c) = finiteHaarMean (fun b => C a b c x * H b c x)) :
    (∑ c, p c * finiteHaarMean (fun x => f c x * g c x)) ^ 2 ≤
      finiteHaarMean (fun b => finiteHaarMean (fun a => finiteHaarMean (fun a' =>
        |∑ c, p c * finiteHaarMean (fun x =>
          C a b c x * C a' b c x * (g c (x + s a c) * g c (x + s a' c)))|))) := by
  let W := fun a b c x => C a b c x * g c (x + s a c)
  have he (a : A) : (∑ c, p c * finiteHaarMean (fun x => f c (x + s a c) * g c (x + s a c))) =
      finiteHaarMean (fun b => ∑ c, p c * finiteHaarMean (fun x => H b c x * W a b c x)) := by
    rw [weightedHaarMean_internal_comm]
    apply Finset.sum_congr rfl
    intro c _
    congr 1
    congr 1
    funext x
    rw [hexp, ← finiteHaarMean_mul_const]
    congr 1
    funext b
    dsimp only [W]
    ring
  have hrep : (∑ c, p c * finiteHaarMean (fun x => f c x * g c x)) =
      finiteHaarMean (fun b => ∑ c, p c * finiteHaarMean (fun x =>
        H b c x * finiteHaarMean (fun a => W a b c x))) := by
    calc
      _ = finiteHaarMean (fun a : A => ∑ c, p c * finiteHaarMean
          (fun x => f c (x + s a c) * g c (x + s a c))) := by
        simp only [weightedHaar_correlation_translate, finiteHaarMean_const]
      _ = finiteHaarMean (fun a : A => finiteHaarMean (fun b => ∑ c, p c *
          finiteHaarMean (fun x => H b c x * W a b c x))) := by simp only [he]
      _ = _ := by
        rw [finiteHaarMean_comm]
        congr 1
        funext b
        rw [weightedHaarMean_internal_comm]
        simp only [finiteHaarMean_const_mul]
  rw [hrep]
  calc
    _ ≤ finiteHaarMean (fun b => (∑ c, p c * finiteHaarMean
        (fun x => H b c x * finiteHaarMean (fun a => W a b c x))) ^ 2) :=
      finiteHaarMean_square_le _
    _ ≤ finiteHaarMean (fun b => ∑ c, p c * finiteHaarMean
        (fun x => finiteHaarMean (fun a => W a b c x) ^ 2)) := by
      apply finiteHaarMean_mono
      intro b
      exact weightedHaar_discard_unit_factor p hp hs (H b) _ (hH b)
    _ = finiteHaarMean (fun b => finiteHaarMean (fun a => finiteHaarMean (fun a' =>
        ∑ c, p c * finiteHaarMean (fun x => W a b c x * W a' b c x)))) := by
      congr 1
      funext b
      simp_rw [weightedHaarMean_internal_comm, ← finiteHaarMean_square_eq_pair]
    _ ≤ _ := by
      apply finiteHaarMean_mono
      intro b
      apply finiteHaarMean_mono
      intro a
      apply finiteHaarMean_mono
      intro a'
      have hpoint : (∑ c, p c * finiteHaarMean (fun x => W a b c x * W a' b c x)) =
          ∑ c, p c * finiteHaarMean (fun x =>
            C a b c x * C a' b c x * (g c (x + s a c) * g c (x + s a' c))) := by
        apply Finset.sum_congr rfl
        intro c _
        congr 1
        congr 1
        funext x
        dsimp only [W]
        ring
      rw [hpoint]
      exact le_abs_self _

end Hindman168
