import Hindman168.BalancedComplexResidueSelection

/-! All actual selected residue samples and anchors stay in ORIGINAL
0<=n<N and have TRUE distance <=2*N/K. -/
namespace Hindman168

theorem balanced_complex_residue_cell_original_range (N K P : ℕ) (hK : 0 < K)
    (i : Fin K) (b : Fin P) (n : ℤ) (hn : n ∈ balancedComplexResidueCell N K P i b) :
    0 ≤ n ∧ n < (N : ℤ) := by
  obtain ⟨hnL,hnR,_hMod⟩ := (balanced_complex_residue_cell_mem N K P i b n).mp hn
  have hL := rough_balanced_cut_contained 0 (N : ℤ) K i.val (by positivity) hK i.isLt.le
  have hR := rough_balanced_cut_contained 0 (N : ℤ) K (i.val+1) (by positivity) hK (by omega)
  exact ⟨hL.1.trans hnL,hnR.trans_le hR.2⟩

theorem balanced_complex_residue_cell_close (N K P : ℕ) (hK : 0 < K) (hLarge : 2*K ≤ N)
    (i : Fin K) (b : Fin P) (a n : ℤ)
    (ha : a ∈ balancedComplexResidueCell N K P i b) (hn : n ∈ balancedComplexResidueCell N K P i b) :
    |(n : ℝ)-(a : ℝ)| ≤ 2*(N : ℝ)/(K : ℝ) := by
  obtain ⟨haL,haR,_hAMod⟩ := (balanced_complex_residue_cell_mem N K P i b a).mp ha
  obtain ⟨hnL,hnR,_hNMod⟩ := (balanced_complex_residue_cell_mem N K P i b n).mp hn
  have hTwo : 2*(K : ℤ) ≤ (N : ℤ) := by exact_mod_cast hLarge
  have hSides := rough_balanced_cut_real_bounds 0 (N : ℤ) K i.val hK (by simpa only [sub_zero] using hTwo)
  have hLeftA : (roughBalancedCut 0 N K i.val : ℝ) ≤ a := by exact_mod_cast haL
  have hRightA : (a : ℝ) ≤ roughBalancedCut 0 N K (i.val+1) := by exact_mod_cast haR.le
  have hLeftN : (roughBalancedCut 0 N K i.val : ℝ) ≤ n := by exact_mod_cast hnL
  have hRightN : (n : ℝ) ≤ roughBalancedCut 0 N K (i.val+1) := by exact_mod_cast hnR.le
  have hWidth : (roughBalancedCut 0 N K (i.val+1) : ℝ)-roughBalancedCut 0 N K i.val ≤
      2*(N : ℝ)/(K : ℝ) := by simpa only [Int.cast_natCast,Int.cast_zero,sub_zero] using hSides.2
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem balanced_complex_residue_cell_congruent (N K P : ℕ) (i : Fin K) (b : Fin P) (a n : ℤ)
    (ha : a ∈ balancedComplexResidueCell N K P i b) (hn : n ∈ balancedComplexResidueCell N K P i b) :
    Int.ModEq (P : ℤ) a n := by
  exact ((balanced_complex_residue_cell_mem N K P i b a).mp ha).2.2.trans
    ((balanced_complex_residue_cell_mem N K P i b n).mp hn).2.2.symm

end Hindman168
