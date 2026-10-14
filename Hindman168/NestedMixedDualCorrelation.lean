import Hindman168.WeightedHaarRecursiveCauchySchwarz
import Hindman168.SubgroupSumPairMoment
import Hindman168.NestedMixedDualRecursion

namespace Hindman168
open scoped BigOperators Classical

theorem weightedHaarMean_abs_le_one {X κ : Type*}
    [Fintype X] [Nonempty X] [Fintype κ] (p : κ → ℝ)
    (hp : ∀ c, 0 ≤ p c) (hs : ∑ c, p c = 1) (F : κ → X → ℝ)
    (hF : ∀ c x, |F c x| ≤ 1) :
    |∑ c, p c * finiteHaarMean (F c)| ≤ 1 := by
  calc
    _ ≤ ∑ c, |p c * finiteHaarMean (F c)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ c, p c * |finiteHaarMean (F c)| := by
      apply Finset.sum_congr rfl
      intro c _
      rw [abs_mul, abs_of_nonneg (hp c)]
    _ ≤ ∑ c, p c * 1 := Finset.sum_le_sum (fun c _ =>
      mul_le_mul_of_nonneg_left (finiteHaarMean_abs_le_one (F c) (hF c)) (hp c))
    _ = 1 := by simp only [mul_one, hs]

/-- Exact correlation duplication for a genuine two-level actual dual. -/
theorem weightedHaar_nested_dual_correlation_square_le
    {G κ : Type*} [AddCommGroup G] [Fintype G] [Fintype κ]
    (Q R : AddSubgroup G) [Fintype Q] [Fintype R]
    (p : κ → ℝ) (hp : ∀ c, 0 ≤ p c) (hs : ∑ c, p c = 1) (d e : ℕ)
    (f : κ → Finset (Fin (d + 1)) → G → ℝ)
    (u : κ → Finset (Fin (e + 1)) → G → ℝ) (g : κ → G → ℝ)
    (hu : ∀ c x, |u c {0} x| ≤ 1)
    (hroot : ∀ c y, f c {0} y = subgroupMixedDualFunction R (e + 1) (u c) y) :
    let C := fun (a b : Q × R) c x => subgroupNestedMixedDualCoefficient Q R d e
      (f c) (u c) a.1 a.2 b.1 b.2 x
    (∑ c, p c * finiteHaarMean (fun x => subgroupMixedDualFunction Q (d + 1) (f c) x * g c x)) ^ 2 ≤
      finiteHaarMean (fun b : Q × R => finiteHaarMean (fun a : Q × R => finiteHaarMean (fun a' : Q × R =>
        |∑ c, p c * finiteHaarMean (fun x => C a b c x * C a' b c x *
          (g c (x + ((a.1 : G) + a.2)) * g c (x + ((a'.1 : G) + a'.2))))|))) := by
  apply weightedHaar_recursive_correlation_square_le (A := Q × R) (B := Q × R) p hp hs
    (fun c x => subgroupMixedDualFunction Q (d + 1) (f c) x) g
    (fun (a : Q × R) (_c : κ) => (a.1 : G) + a.2)
    (fun (a b : Q × R) c x => subgroupNestedMixedDualCoefficient Q R d e (f c) (u c) a.1 a.2 b.1 b.2 x)
    (fun (b : Q × R) c x => u c {0} (x + b.1 + b.2)) (fun _b c _x => hu c _)
  intro a c x
  simpa only [finiteHaarMean_prod, ← add_assoc] using
    subgroupMixedDualFunction_nested_translate_expansion Q R d e (f c) (u c) (hroot c) a.1 a.2 x

/-- Uniform testing of the paired coefficients controls the original
correlation by the genuine next-order Gowers moment on the subgroup sum. -/
theorem weightedHaar_nested_dual_correlation_bound
    {G κ : Type*} [AddCommGroup G] [Fintype G] [Fintype κ]
    (Q R : AddSubgroup G) [Fintype Q] [Fintype R] [Fintype (Q ⊔ R : AddSubgroup G)]
    (p : κ → ℝ) (hp : ∀ c, 0 ≤ p c) (hs : ∑ c, p c = 1) (d e k : ℕ) (hk : 0 < k)
    (f : κ → Finset (Fin (d + 1)) → G → ℝ)
    (u : κ → Finset (Fin (e + 1)) → G → ℝ) (g : κ → G → ℝ)
    (hf : ∀ c ω, ω ≠ ∅ → ∀ x, |f c ω x| ≤ 1)
    (hu : ∀ c ω, ω ≠ ∅ → ∀ x, |u c ω x| ≤ 1) (hg : ∀ c x, |g c x| ≤ 1)
    (hroot : ∀ c y, f c {0} y = subgroupMixedDualFunction R (e + 1) (u c) y)
    (ε δ : ℝ) (hε : 0 ≤ ε) (hδ : 0 < δ)
    (hsmall : ∀ (b a a' : Q × R), weightedSubgroupGowersValue (Q ⊔ R) p k
      (fun c x => g c (x + ((a.1 : G) + a.2)) * g c (x + ((a'.1 : G) + a'.2))) ≤ δ →
        |∑ c, p c * finiteHaarMean (fun x =>
          subgroupNestedMixedDualCoefficient Q R d e (f c) (u c) a.1 a.2 b.1 b.2 x *
            subgroupNestedMixedDualCoefficient Q R d e (f c) (u c) a'.1 a'.2 b.1 b.2 x *
              (g c (x + ((a.1 : G) + a.2)) * g c (x + ((a'.1 : G) + a'.2))))| ≤ ε) :
    (∑ c, p c * finiteHaarMean (fun x => subgroupMixedDualFunction Q (d + 1) (f c) x * g c x)) ^ 2 ≤
      ε + weightedSubgroupGowersValue (Q ⊔ R) p (k + 1) g ^ (2 ^ (k + 1)) / δ ^ (2 ^ k) := by
  let C := fun (a b : Q × R) c x => subgroupNestedMixedDualCoefficient Q R d e
    (f c) (u c) a.1 a.2 b.1 b.2 x
  let r := fun (b a a' : Q × R) => ∑ c, p c * finiteHaarMean (fun x =>
    C a b c x * C a' b c x *
      (g c (x + ((a.1 : G) + a.2)) * g c (x + ((a'.1 : G) + a'.2))))
  have hprod (v t : ℝ) (hv : |v| ≤ 1) (ht : |t| ≤ 1) : |v * t| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul hv ht (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hC (a b : Q × R) (c : κ) (x : G) : |C a b c x| ≤ 1 :=
    subgroupNestedMixedDualCoefficient_abs_le_one Q R d e (f c) (u c) (hf c) (hu c) _ _ _ _ x
  have hr : ∀ b a a', |r b a a'| ≤ 1 := by
    intro b a a'
    apply weightedHaarMean_abs_le_one p hp hs
    intro c x
    exact hprod _ _ (hprod _ _ (hC a b c x) (hC a' b c x)) (hprod _ _ (hg c _) (hg c _))
  calc
    _ ≤ finiteHaarMean (fun b : Q × R => finiteHaarMean (fun a : Q × R =>
        finiteHaarMean (fun a' : Q × R => |r b a a'|))) :=
      weightedHaar_nested_dual_correlation_square_le Q R p hp hs d e f u g
        (fun c x => hu c {0} (by simp) x) hroot
    _ ≤ finiteHaarMean (fun _b : Q × R => ε +
        weightedSubgroupGowersValue (Q ⊔ R) p (k + 1) g ^ (2 ^ (k + 1)) / δ ^ (2 ^ k)) := by
      apply finiteHaarMean_mono
      intro b
      exact weightedSubgroupGowersValue_sum_pair_test_bound Q R p hp k hk g (r b)
        (hr b) ε δ hε hδ (hsmall b)
    _ = _ := finiteHaarMean_const _

end Hindman168
