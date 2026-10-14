import Hindman168.AveragedShortCubeWrapping
import Hindman168.CyclicShortCubeBound

namespace Hindman168
open scoped BigOperators

theorem shortCube_product_length (a n J : ℕ) (ha : 0 < a) :
    a * n / (J * a) = n / J := by
  rw [Nat.mul_comm J a, Nat.mul_div_mul_left n J ha]

theorem weighted_integerCell_shortCube_gowers_bound {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ c, 0 ≤ p c) (hs : ∑ c, p c = 1)
    (M a n d J : ℕ) (ha : 0 < a) (hn : 0 < n) [NeZero (a * n)]
    [Fintype (multipleAddSubgroup (ZMod (a * n)) a)]
    (hJ : 0 < J) (hL : 0 < n / J)
    (k : ι → ℤ) (r : ι → Fin M) (f : ι → ℤ → ℝ) (hf : ∀ c y, |f c y| ≤ 1) :
    |∑ c, p c * finiteHaarMean (fun z : ZMod (a * n) =>
      finiteHaarMean (fun u : Fin d → Fin (n / J) =>
        finiteHaarMean (fun v : Fin d → Fin (n / J) =>
          ∏ ω : Finset (Fin d), f c (k c * (M * (a * n) : ℕ) + (r c).val + (M : ℤ) * z.val +
            M * ((a : ℤ) * ∑ j ∈ ω, (((v j).val : ℤ) - (u j).val))))))| ≤
      (2 * (J : ℝ)) ^ d * weightedSubgroupGowersValue (multipleAddSubgroup (ZMod (a * n)) a)
        p (2 ^ d) (fun c z => f c (k c * (M * (a * n) : ℕ) + (r c).val + (M : ℤ) * z.val)) +
      4 * (d : ℝ) / J := by
  let g := fun c (z : ZMod (a * n)) => f c (k c * (M * (a * n) : ℕ) + (r c).val + (M : ℤ) * z.val)
  have hg : ∀ c z, |g c z| ≤ 1 := fun c z => hf c _
  have hlength : 0 < a * n / (J * a) := by rw [shortCube_product_length a n J ha]; exact hL
  have hw := weighted_cyclicCell_shortCube_wrap_error p hp hs M (a * n) d J a hJ hlength k r f hf
  rw [shortCube_product_length a n J ha] at hw
  have hb := weightedCyclicShortCube_vertices_bound a n ha hn p hp hs d J hJ hL g hg
  have hc : ∀ (z : ZMod (a * n)) (u v : Fin d → Fin (n / J)) (ω : Finset (Fin d)),
      z + (((a : ℤ) * ∑ j ∈ ω, (((v j).val : ℤ) - (u j).val) : ℤ) : ZMod (a * n)) =
        z + (a : ZMod (a * n)) * ∑ j ∈ ω, ((v j).val : ZMod (a * n)) -
          (a : ZMod (a * n)) * ∑ j ∈ ω, ((u j).val : ZMod (a * n)) := by
    intro z u v ω
    simp only [Int.cast_mul, Int.cast_natCast, Int.cast_sum, Int.cast_sub,
      Finset.sum_sub_distrib, mul_sub, add_sub_assoc]
  simp_rw [hc] at hw
  dsimp [g] at hb
  simp only [Nat.cast_mul] at hw ⊢
  have ht := abs_le.mp hw
  have hb' := abs_le.mp hb
  rw [abs_le]
  constructor <;> linarith

end Hindman168
