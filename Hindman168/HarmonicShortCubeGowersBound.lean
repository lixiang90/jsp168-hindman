import Hindman168.WeightedHarmonicCyclicCells

namespace Hindman168
open scoped BigOperators

theorem weighted_harmonicCell_shortCube_gowers_bound {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ c, 0 ≤ p c) (hs : ∑ c, p c = 1)
    (X W M a n d J : ℕ) (hX : 0 < X) (hM : 0 < M) (hWM : W ∣ M)
    (hZ : 0 < harmonicNormalizer X W) (ha : 0 < a) (hn : 0 < n) [NeZero (a * n)]
    [Fintype (multipleAddSubgroup (ZMod (a * n)) a)] (hJ : 0 < J) (hL : 0 < n / J)
    (k : ι → ℤ) (r : ι → Fin M) (hr : ∀ c, (r c).val.Coprime W)
    (hlo : ∀ c, (X : ℤ) ≤ k c * (M * (a * n) : ℕ))
    (hhi : ∀ c, k c * (M * (a * n) : ℕ) + (M * (a * n) : ℕ) ≤ (X ^ 2 : ℕ))
    (f : ι → ℤ → ℝ) (hf : ∀ c y, |f c y| ≤ 1) :
    let t := fun c y => finiteHaarMean (fun u : Fin d → Fin (n / J) =>
      finiteHaarMean (fun v : Fin d → Fin (n / J) =>
        ∏ ω : Finset (Fin d), f c (y + M * ((a : ℤ) * ∑ j ∈ ω, (((v j).val : ℤ) - (u j).val)))))
    |∑ c, p c * ((∑ y ∈ intervalResidueSet (k c * (M * (a * n) : ℕ)) (M * (a * n)) M (r c).val,
        integerMass X W y * t c y) /
      (∑ y ∈ intervalResidueSet (k c * (M * (a * n) : ℕ)) (M * (a * n)) M (r c).val,
        integerMass X W y))| ≤
      (2 * (J : ℝ)) ^ d * weightedSubgroupGowersValue (multipleAddSubgroup (ZMod (a * n)) a)
        p (2 ^ d) (fun c z => f c (k c * (M * (a * n) : ℕ) + (r c).val + (M : ℤ) * z.val)) +
      4 * (d : ℝ) / J + (M * (a * n) : ℕ) / (X : ℝ) := by
  intro t
  letI : NeZero (n / J) := ⟨Nat.ne_of_gt hL⟩
  have ht : ∀ c y, |t c y| ≤ 1 := by
    intro c y
    apply finiteHaarMean_abs_le_one
    intro u
    apply finiteHaarMean_abs_le_one
    intro v
    rw [Finset.abs_prod]
    exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun _ _ => hf c _)
  have hw := weighted_completeCell_harmonic_cyclic_error p hp hs X W M (a * n) hX hM hWM
    hZ k r hr hlo hhi t ht
  have hb := weighted_integerCell_shortCube_gowers_bound p hp hs M a n d J ha hn hJ hL k r f hf
  dsimp only [t] at hw
  have hwe := abs_le.mp hw
  have hbe := abs_le.mp hb
  rw [abs_le]
  constructor <;> linarith

end Hindman168
