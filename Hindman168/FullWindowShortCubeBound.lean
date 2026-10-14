import Hindman168.AlignedGlobalShortCubeBound

namespace Hindman168
open scoped BigOperators

theorem fullWindow_harmonic_shortCube_gowers_bound
    (X W M a n d J : ℕ) (hX : 0 < X) (hM : 0 < M) (hWM : W ∣ M)
    (hZ : 0 < harmonicNormalizer X W) (ha : 0 < a) (hn : 0 < n) [NeZero (a * n)]
    [Fintype (multipleAddSubgroup (ZMod (a * n)) a)] (hJ : 0 < J) (hL : 0 < n / J)
    (l u : ℤ) (hlo : (X : ℤ) ≤ l * (M * (a * n) : ℕ))
    (hhi : u * (M * (a * n) : ℕ) ≤ (X ^ 2 : ℕ))
    (hpos : 0 < ∑ y ∈ Finset.Ico (l * (M * (a * n) : ℕ)) (u * (M * (a * n) : ℕ)), integerMass X W y)
    (f : ℤ → ℝ) (hf : ∀ y, |f y| ≤ 1) :
    let R := M * (a * n)
    let I := Finset.Ico (l * R) (u * R)
    let C := (Finset.Ico l u).product ((Finset.univ : Finset (Fin M)).filter (fun r => r.val.Coprime W))
    let p := fun c : C => (∑ y ∈ intervalResidueSet (c.val.1 * R) R M c.val.2.val, integerMass X W y) /
      (∑ y ∈ I, integerMass X W y)
    let t := fun y => finiteHaarMean (fun v₀ : Fin d → Fin (n / J) =>
      finiteHaarMean (fun v₁ : Fin d → Fin (n / J) =>
        ∏ ω : Finset (Fin d), f (y + M * ((a : ℤ) * ∑ j ∈ ω, (((v₁ j).val : ℤ) - (v₀ j).val)))))
    |∑ y ∈ Finset.Ico (X : ℤ) (X ^ 2 : ℕ), integerMass X W y * t y| ≤
      (2 * (J : ℝ)) ^ d * weightedSubgroupGowersValue (multipleAddSubgroup (ZMod (a * n)) a)
        p (2 ^ d) (fun c z => f (c.val.1 * R + c.val.2.val + (M : ℤ) * z.val)) +
      4 * (d : ℝ) / J + (R : ℝ) / X + 2 * ∑ y ∈ Finset.Ico (X : ℤ) (X ^ 2 : ℕ) \ I, integerMass X W y := by
  intro R I C p t
  letI : NeZero (n / J) := ⟨Nat.ne_of_gt hL⟩
  have ht : ∀ y, |t y| ≤ 1 := by
    intro y
    apply finiteHaarMean_abs_le_one
    intro v₀
    apply finiteHaarMean_abs_le_one
    intro v₁
    rw [Finset.abs_prod]
    exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun _ _ => hf _)
  have hsub : I ⊆ Finset.Ico (X : ℤ) (X ^ 2 : ℕ) := by
    intro y hy
    obtain ⟨hl, hu⟩ := Finset.mem_Ico.mp hy
    exact Finset.mem_Ico.mpr ⟨hlo.trans hl, hu.trans_le hhi⟩
  have htotal : (∑ y ∈ Finset.Ico (X : ℤ) (X ^ 2 : ℕ), integerMass X W y) = 1 := by
    rw [integerMass_window_sum, integerMass_total hZ]
  have he := finite_retained_probability_test_error I _ hsub (integerMass X W) t
    (integerMass_nonnegative X W) ht htotal hpos
  have hb := alignedInterval_harmonic_shortCube_gowers_bound X W M a n d J hX hM hWM hZ ha hn hJ hL
    l u hlo hhi hpos f hf
  have hea := abs_le.mp he
  have hba := abs_le.mp hb
  rw [abs_le]
  constructor <;> linarith

end Hindman168
