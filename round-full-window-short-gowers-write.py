from pathlib import Path
s=Path('Hindman168/AlignedGlobalShortCubeBound.lean').read_text(encoding='utf-8').split(' := by',1)[0]
s=s.replace('import Hindman168.AlignedCellDisintegration','import Hindman168.AlignedGlobalShortCubeBound').replace('theorem alignedInterval_harmonic_shortCube_gowers_bound','theorem fullWindow_harmonic_shortCube_gowers_bound')
s=s.replace('|(∑ y ∈ I, integerMass X W y * t y) / (∑ y ∈ I, integerMass X W y)|','|∑ y ∈ Finset.Ico (X : ℤ) (X ^ 2 : ℕ), integerMass X W y * t y|')
s+=''' + 2 * ∑ y ∈ Finset.Ico (X : ℤ) (X ^ 2 : ℕ) \\ I, integerMass X W y := by
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
'''
Path('Hindman168/FullWindowShortCubeBound.lean').write_text(s,encoding='utf-8')
