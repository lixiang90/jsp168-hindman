import Hindman168.RealMeshResiduePartition
import Hindman168.FiniteComplexCellMassError

/-! Actual residue-cell masses and means give an explicit whole-window
complex error bound; the remaining mass term tends to zero at fixed mesh. -/
namespace Hindman168
open scoped BigOperators Classical

theorem real_mesh_residue_mass (L : ℝ) (hL : 0 < L) (N M : ℕ) (hN : 0 < N) (hM : 0 < M)
    (i : Fin N) (r : Fin M) :
    |((realMeshResidueCell L N M i r).card : ℝ)/L-1/((N : ℝ)*M)| ≤ 2/L := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hab : (i.val : ℝ)/(N : ℝ)*L ≤ ((i.val : ℝ)+1)/(N : ℝ)*L := by
    apply mul_le_mul_of_nonneg_right _ hL.le
    apply div_le_div_of_nonneg_right _ hNR.le
    linarith
  have he := real_interval_residue_count _ _ hab M hM r
  have hw : (((i.val : ℝ)+1)/(N : ℝ)*L)-((i.val : ℝ)/(N : ℝ)*L) = L/(N : ℝ) := by ring
  rw [hw] at he
  change |((realMeshResidueCell L N M i r).card : ℝ)-(L/(N : ℝ))/M| ≤ _ at he
  have htwo : 1+1/(M : ℝ) ≤ 2 := by
    have := (div_le_one hMR).mpr hM1
    linarith
  have hid : ((realMeshResidueCell L N M i r).card : ℝ)/L-1/((N : ℝ)*M) =
      (((realMeshResidueCell L N M i r).card : ℝ)-(L/(N : ℝ))/M)/L := by
    field_simp
  rw [hid, abs_div, abs_of_pos hL]
  exact div_le_div_of_nonneg_right (he.trans htwo) hL.le

theorem real_mesh_complex_average_error (L : ℝ) (hL : 0 < L) (N M : ℕ) (hN : 0 < N) (hM : 0 < M)
    (a : ℤ → ℂ) (g : Fin N × Fin M → ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (hmean : ∀ z, ‖finiteComplexSetMean (realMeshResidueCell L N M z.1 z.2) a-g z‖ ≤ ε)
    (hg : ∀ z, ‖g z‖ ≤ 1) :
    ‖(∑ z ∈ Finset.Ico 0 ⌈L⌉, a z)/(L : ℂ)-finiteComplexMean g‖ ≤
      ε+2*(N : ℝ)*M*(ε+1)/L := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hb := finite_complex_cell_mass_error (fun z : Fin N × Fin M => realMeshResidueCell L N M z.1 z.2)
    a g L (1/((N : ℝ)*M)) ε (2/L) hL hε hmean
    (fun z => real_mesh_residue_mass L hL N M hN hM z.1 z.2) hg
  have hs : (∑ z : Fin N × Fin M, ∑ k ∈ realMeshResidueCell L N M z.1 z.2, a k) =
      ∑ z ∈ Finset.Ico 0 ⌈L⌉, a z := by
    rw [Fintype.sum_prod_type]
    exact real_mesh_residue_sum L hL.le N M hN hM a
  have ht : (∑ z : Fin N × Fin M, ((1/((N : ℝ)*M) : ℝ) : ℂ)*g z) = finiteComplexMean g := by
    rw [← Finset.mul_sum]
    simp only [finiteComplexMean, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    push_cast
    ring
  rw [hs,ht] at hb
  simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul] at hb
  have he : (N : ℝ)*M*((1/((N : ℝ)*M)+2/L)*ε+2/L) = ε+2*(N : ℝ)*M*(ε+1)/L := by
    field_simp
    ring
  rwa [he] at hb

end Hindman168
