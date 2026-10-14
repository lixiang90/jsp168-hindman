import Hindman168.FiniteComplexFiberSelection
import Hindman168.RoughIntervalPartition
import Hindman168.IntervalResidueCount

/-! TRUE balanced interval / residue partition selects an ACTUAL complex
mean at least the original mean, with original-scale positive cell length
and a genuine short-interval bound. No discarded-tail signal is assumed. -/
namespace Hindman168
open scoped Classical

def balancedComplexResidueCell (N K P : ℕ) (i : Fin K) (b : Fin P) : Finset ℤ :=
  intervalResidueSet (roughBalancedCut 0 N K i.val)
    (roughBalancedCut 0 N K (i.val+1)-roughBalancedCut 0 N K i.val).toNat P b.val

noncomputable def balancedComplexResidueLabel (N K P : ℕ) (hK : 0 < K) (hP : 0 < P) (n : ℤ) :
    Fin K × Fin P :=
  (roughIntervalLabel 0 N K hK n,⟨(n%(P : ℤ)).toNat,by
    have hp : (0 : ℤ) < P := by exact_mod_cast hP
    have hn := Int.emod_nonneg n hp.ne'
    have hm := Int.emod_lt_of_pos n hp
    omega⟩)

theorem balanced_complex_residue_cell_mem (N K P : ℕ) (i : Fin K) (b : Fin P) (n : ℤ) :
    n ∈ balancedComplexResidueCell N K P i b ↔
      roughBalancedCut 0 N K i.val ≤ n ∧ n < roughBalancedCut 0 N K (i.val+1) ∧ n%(P : ℤ)=(b.val : ℤ) := by
  have hm := rough_balanced_cut_mono 0 (N : ℤ) K (show i.val ≤ i.val+1 by omega)
  have he : roughBalancedCut 0 N K i.val+
      ((roughBalancedCut 0 N K (i.val+1)-roughBalancedCut 0 N K i.val).toNat : ℤ)=
        roughBalancedCut 0 N K (i.val+1) := by rw [Int.toNat_of_nonneg (sub_nonneg.mpr hm)]; omega
  simp only [balancedComplexResidueCell,intervalResidueSet,integerWindow,Finset.mem_filter,Finset.mem_Ico,he]
  tauto

theorem balanced_complex_residue_cell_fiber (N K P : ℕ) (hK : 0 < K) (hP : 0 < P)
    (i : Fin K) (b : Fin P) :
    (Finset.Ico 0 (N : ℤ)).filter (fun n => balancedComplexResidueLabel N K P hK hP n=(i,b))=
      balancedComplexResidueCell N K P i b := by
  ext n
  have hL := rough_balanced_cut_contained 0 (N : ℤ) K i.val (by positivity) hK i.isLt.le
  have hR := rough_balanced_cut_contained 0 (N : ℤ) K (i.val+1) (by positivity) hK (by omega)
  simp only [Finset.mem_filter,Finset.mem_Ico,balanced_complex_residue_cell_mem]
  constructor
  · rintro ⟨hn,he⟩
    have hi := (Prod.mk.inj he).1
    have hb := congrArg Fin.val (Prod.mk.inj he).2
    have hp : (0 : ℤ) < P := by exact_mod_cast hP
    have hmod := Int.emod_nonneg n hp.ne'
    refine ⟨?_,?_,?_⟩
    · exact ((rough_interval_label_iff 0 (N : ℤ) K hK (by positivity) n hn i).mp hi).1
    · exact ((rough_interval_label_iff 0 (N : ℤ) K hK (by positivity) n hn i).mp hi).2
    · change (n%(P : ℤ)).toNat=b.val at hb
      rw [← hb,Int.toNat_of_nonneg hmod]
  · rintro ⟨hnL,hnR,hnMod⟩
    have hn : 0 ≤ n ∧ n < (N : ℤ) := ⟨hL.1.trans hnL,hnR.trans_le hR.2⟩
    refine ⟨hn,Prod.ext ?_ ?_⟩
    · exact (rough_interval_label_iff 0 (N : ℤ) K hK (by positivity) n hn i).mpr ⟨hnL,hnR⟩
    · apply Fin.ext
      change (n%(P : ℤ)).toNat=b.val
      rw [hnMod,Int.toNat_natCast]

theorem balanced_complex_residue_cell_card_lower (N K P : ℕ) (hK : 0 < K) (hP : 0 < P)
    (hLarge : 4*K*P ≤ N) (i : Fin K) (b : Fin P) :
    (N : ℝ)/(4*(K : ℝ)*(P : ℝ)) ≤ (balancedComplexResidueCell N K P i b).card := by
  have hTwo : 2*(K : ℤ) ≤ (N : ℤ) := by
    have hp : 1 ≤ P := hP
    exact_mod_cast (show 2*K ≤ N by nlinarith)
  have hSides := rough_balanced_cut_real_bounds 0 (N : ℤ) K i.val hK (by simpa only [sub_zero] using hTwo)
  have hCount := interval_residue_count (roughBalancedCut 0 N K i.val)
    (roughBalancedCut 0 N K (i.val+1)-roughBalancedCut 0 N K i.val).toNat hP b.isLt
  have hCut := rough_balanced_cut_mono 0 (N : ℤ) K (show i.val ≤ i.val+1 by omega)
  have hT : ((roughBalancedCut 0 N K (i.val+1)-roughBalancedCut 0 N K i.val).toNat : ℝ)=
      (roughBalancedCut 0 N K (i.val+1) : ℝ)-roughBalancedCut 0 N K i.val := by
    exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr hCut)
  rw [hT] at hCount
  change |((balancedComplexResidueCell N K P i b).card : ℝ)-
    ((roughBalancedCut 0 N K (i.val+1) : ℝ)-roughBalancedCut 0 N K i.val)/(P : ℝ)| ≤ 1 at hCount
  have hk : (0 : ℝ) < K := by exact_mod_cast hK
  have hp : (0 : ℝ) < P := by exact_mod_cast hP
  have hN : 4*(K : ℝ)*(P : ℝ) ≤ N := by exact_mod_cast hLarge
  have hLower := (abs_le.mp hCount).1
  have hWidth := (div_le_iff₀ (by positivity : 0 < 2*(K : ℝ))).mp
    (by simpa only [Int.cast_natCast,Int.cast_zero,sub_zero] using hSides.1)
  have hCard := (div_le_iff₀ hp).mp (show ((roughBalancedCut 0 N K (i.val+1) : ℝ)-
      roughBalancedCut 0 N K i.val)/(P : ℝ) ≤ (balancedComplexResidueCell N K P i b).card+1 by linarith)
  apply (div_le_iff₀ (by positivity : 0 < 4*(K : ℝ)*(P : ℝ))).mpr
  nlinarith

theorem balanced_complex_residue_mean_selection (N K P : ℕ) (hK : 0 < K) (hP : 0 < P)
    (hLarge : 4*K*P ≤ N) (f : ℤ → ℂ) :
    ∃ (i : Fin K) (b : Fin P), (balancedComplexResidueCell N K P i b).Nonempty ∧
      (N : ℝ)/(4*(K : ℝ)*(P : ℝ)) ≤ (balancedComplexResidueCell N K P i b).card ∧
      ‖finiteComplexSetMean (Finset.Ico 0 (N : ℤ)) f‖ ≤
        ‖finiteComplexSetMean (balancedComplexResidueCell N K P i b) f‖ := by
  have hN : 0 < N := (show 0 < 4*K*P by positivity).trans_le hLarge
  have hS : (Finset.Ico 0 (N : ℤ)).Nonempty := Finset.nonempty_Ico.mpr (by exact_mod_cast hN)
  obtain ⟨⟨i,b⟩,_hi,hFiber,hMean⟩ := finite_complex_fiber_mean_selection
    (Finset.Ico 0 (N : ℤ)) hS (balancedComplexResidueLabel N K P hK hP) f
  rw [balanced_complex_residue_cell_fiber] at hFiber hMean
  exact ⟨i,b,hFiber,balanced_complex_residue_cell_card_lower N K P hK hP hLarge i b,hMean⟩

end Hindman168
