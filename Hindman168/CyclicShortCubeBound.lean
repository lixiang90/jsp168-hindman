import Hindman168.UniformImageCubeBound
import Hindman168.MultipleCyclicIntervalEmbedding

namespace Hindman168
open scoped BigOperators

theorem multipleDivisorSubgroup_card (m q : ℕ) (hm : 0 < m) (hq : 0 < q)
    (hqm : q ∣ m) [Fintype (multipleAddSubgroup (ZMod m) q)] :
    Fintype.card (multipleAddSubgroup (ZMod m) q) = m / q := by
  obtain ⟨n, rfl⟩ := hqm
  have hn : 0 < n := by nlinarith
  rw [multipleCyclicSubgroup_card q n hq hn, Nat.mul_div_cancel_left n hq]

theorem weightedCyclicShortCube_bound (q n : ℕ) (hq : 0 < q) (hn : 0 < n)
    [Fintype (ZMod (q * n))] [Fintype (multipleAddSubgroup (ZMod (q * n)) q)]
    {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ c, 0 ≤ p c) (hsum : ∑ c, p c = 1)
    (d J : ℕ) (hJ : 0 < J) (hL : 0 < n / J)
    (h : ι → ZMod (q * n) → ℝ) (hh : ∀ c x, |h c x| ≤ 1) :
    |∑ c, p c * finiteHaarMean (fun x => finiteHaarMean (fun u : Fin d → Fin (n / J) =>
      finiteHaarMean (fun v : Fin d → Fin (n / J) =>
        subgroupCubeProduct (multipleAddSubgroup (ZMod (q * n)) q) d (h c) x
          (fun j => multipleCyclicIntervalEmbedding q n (Fin.castLE (Nat.div_le_self n J) (v j)) -
            multipleCyclicIntervalEmbedding q n (Fin.castLE (Nat.div_le_self n J) (u j))))))| ≤
      (2 * (J : ℝ)) ^ d *
        weightedSubgroupGowersValue (multipleAddSubgroup (ZMod (q * n)) q) p (2 ^ d) h := by
  letI : NeZero (n / J) := ⟨Nat.ne_of_gt hL⟩
  have hsize : (Fintype.card (multipleAddSubgroup (ZMod (q * n)) q) : ℝ) /
      Fintype.card (Fin (n / J)) ≤ 2 * (J : ℝ) := by
    rw [multipleCyclicSubgroup_card q n hq hn, Fintype.card_fin]
    exact shortInterval_card_ratio n J hJ hL
  exact weightedUniformImageCube_bound (multipleAddSubgroup (ZMod (q * n)) q)
    p hp hsum d (2 * (J : ℝ)) (by positivity) hsize
    (fun _ _ u => multipleCyclicIntervalEmbedding q n (Fin.castLE (Nat.div_le_self n J) u))
    (fun _ _ => multipleCyclicShortInterval_injective q n (n / J) hq (Nat.div_le_self n J)) h hh

theorem multipleCyclicCubeProduct_vertices (q n d L : ℕ) (hL : L ≤ n)
    (h : ZMod (q * n) → ℝ) (x : ZMod (q * n)) (u v : Fin d → Fin L) :
    subgroupCubeProduct (multipleAddSubgroup (ZMod (q * n)) q) d h x
      (fun j => multipleCyclicIntervalEmbedding q n (Fin.castLE hL (v j)) -
        multipleCyclicIntervalEmbedding q n (Fin.castLE hL (u j))) =
      ∏ ω : Finset (Fin d), h (x + (q : ZMod (q * n)) *
        ∑ j ∈ ω, ((v j).val : ZMod (q * n)) - (q : ZMod (q * n)) *
          ∑ j ∈ ω, ((u j).val : ZMod (q * n))) := by
  simp only [subgroupCubeProduct, AddSubgroup.coe_sub, multipleCyclicIntervalEmbedding,
    Fin.val_castLE, nsmul_eq_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, add_sub_assoc]

theorem weightedCyclicShortCube_vertices_bound (q n : ℕ) (hq : 0 < q) (hn : 0 < n)
    [Fintype (ZMod (q * n))] [Fintype (multipleAddSubgroup (ZMod (q * n)) q)]
    {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ c, 0 ≤ p c) (hsum : ∑ c, p c = 1)
    (d J : ℕ) (hJ : 0 < J) (hL : 0 < n / J)
    (h : ι → ZMod (q * n) → ℝ) (hh : ∀ c x, |h c x| ≤ 1) :
    |∑ c, p c * finiteHaarMean (fun x => finiteHaarMean (fun u : Fin d → Fin (n / J) =>
      finiteHaarMean (fun v : Fin d → Fin (n / J) =>
        ∏ ω : Finset (Fin d), h c (x + (q : ZMod (q * n)) *
          ∑ j ∈ ω, ((v j).val : ZMod (q * n)) - (q : ZMod (q * n)) *
            ∑ j ∈ ω, ((u j).val : ZMod (q * n))))))| ≤
      (2 * (J : ℝ)) ^ d *
        weightedSubgroupGowersValue (multipleAddSubgroup (ZMod (q * n)) q) p (2 ^ d) h := by
  simpa only [multipleCyclicCubeProduct_vertices] using
    weightedCyclicShortCube_bound q n hq hn p hp hsum d J hJ hL h hh

end Hindman168
