import Hindman168.HaarMeanTestError

namespace Hindman168
open scoped BigOperators

theorem cyclicCell_shortCube_average_wrap_error (k : ℤ) (M q d J a : ℕ) [NeZero q]
    (hJ : 0 < J) (hL : 0 < q / (J * a)) (r : Fin M)
    (f : ℤ → ℝ) (hf : ∀ y, |f y| ≤ 1) :
    |finiteHaarMean (fun z : ZMod q => finiteHaarMean (fun u : Fin d → Fin (q / (J * a)) => finiteHaarMean (fun v : Fin d → Fin (q / (J * a)) => ∏ ω : Finset (Fin d), f (k * (M * q : ℕ) + r.val + (M : ℤ) * (z + (((a : ℤ) * ∑ j ∈ ω, (((v j).val : ℤ) - (u j).val) : ℤ) : ZMod q)).val)))) -
      finiteHaarMean (fun z : ZMod q => finiteHaarMean (fun u : Fin d → Fin (q / (J * a)) => finiteHaarMean (fun v : Fin d → Fin (q / (J * a)) => ∏ ω : Finset (Fin d), f (k * (M * q : ℕ) + r.val + (M : ℤ) * z.val + M * ((a : ℤ) * ∑ j ∈ ω, (((v j).val : ℤ) - (u j).val))))))| ≤ 4 * (d : ℝ) / J := by
  letI : NeZero (q / (J * a)) := ⟨Nat.ne_of_gt hL⟩
  let C := fun (u v : Fin d → Fin (q / (J * a))) (z : ZMod q) => ∏ ω : Finset (Fin d), f (k * (M * q : ℕ) + r.val + (M : ℤ) * (z + (((a : ℤ) * ∑ j ∈ ω, (((v j).val : ℤ) - (u j).val) : ℤ) : ZMod q)).val)
  let I := fun (u v : Fin d → Fin (q / (J * a))) (z : ZMod q) => ∏ ω : Finset (Fin d), f (k * (M * q : ℕ) + r.val + (M : ℤ) * z.val + M * ((a : ℤ) * ∑ j ∈ ω, (((v j).val : ℤ) - (u j).val)))
  change |finiteHaarMean (fun z => finiteHaarMean (fun u => finiteHaarMean (fun v => C u v z))) -
    finiteHaarMean (fun z => finiteHaarMean (fun u => finiteHaarMean (fun v => I u v z)))| ≤ _
  rw [← finiteHaarMean_rotate C, ← finiteHaarMean_rotate I]
  apply finiteHaarMean_test_error
  intro u
  apply finiteHaarMean_test_error
  intro v
  exact cyclicCell_shortCube_wrap_error k M q d J a hJ r u v f hf

theorem weighted_cyclicCell_shortCube_wrap_error {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ c, 0 ≤ p c) (hs : ∑ c, p c = 1)
    (M q d J a : ℕ) [NeZero q] (hJ : 0 < J) (hL : 0 < q / (J * a))
    (k : ι → ℤ) (r : ι → Fin M) (f : ι → ℤ → ℝ) (hf : ∀ c y, |f c y| ≤ 1) :
    |(∑ c, p c * finiteHaarMean (fun z : ZMod q => finiteHaarMean (fun u : Fin d → Fin (q / (J * a)) => finiteHaarMean (fun v : Fin d → Fin (q / (J * a)) => ∏ ω : Finset (Fin d), f c (k c * (M * q : ℕ) + (r c).val + (M : ℤ) * (z + (((a : ℤ) * ∑ j ∈ ω, (((v j).val : ℤ) - (u j).val) : ℤ) : ZMod q)).val))))) -
      (∑ c, p c * finiteHaarMean (fun z : ZMod q => finiteHaarMean (fun u : Fin d → Fin (q / (J * a)) => finiteHaarMean (fun v : Fin d → Fin (q / (J * a)) => ∏ ω : Finset (Fin d), f c (k c * (M * q : ℕ) + (r c).val + (M : ℤ) * z.val + M * ((a : ℤ) * ∑ j ∈ ω, (((v j).val : ℤ) - (u j).val)))))))| ≤ 4 * (d : ℝ) / J := by
  apply weightedCell_test_error p _ _ hp hs
  intro c
  exact cyclicCell_shortCube_average_wrap_error (k c) M q d J a hJ hL (r c) (f c) (hf c)

end Hindman168
