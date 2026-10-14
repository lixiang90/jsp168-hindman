import Hindman168.IntervalResidueCount
import Hindman168.HarmonicCellUniformity
import Mathlib.Tactic.Ring

namespace Hindman168

def completeResidueCellPoint (k : ℤ) (M q : ℕ) (r : Fin M) (t : Fin q) : ℤ :=
  k * (M * q : ℕ) + r.val + (M : ℤ) * t.val

theorem completeResidueCellPoint_bounds (k : ℤ) (M q : ℕ) (hM : 0 < M)
    (r : Fin M) (t : Fin q) :
    k * (M * q : ℕ) ≤ completeResidueCellPoint k M q r t ∧
      completeResidueCellPoint k M q r t < k * (M * q : ℕ) + (M * q : ℕ) := by
  have hr : (r.val : ℤ) < M := by exact_mod_cast r.isLt
  have ht : (t.val : ℤ) < q := by exact_mod_cast t.isLt
  have hMp : (0 : ℤ) < M := by exact_mod_cast hM
  simp only [completeResidueCellPoint, Nat.cast_mul]
  constructor <;> nlinarith [Int.natCast_nonneg r.val, Int.natCast_nonneg t.val]

theorem completeResidueCellPoint_residue (k : ℤ) (M q : ℕ)
    (r : Fin M) (t : Fin q) : completeResidueCellPoint k M q r t % M = r.val := by
  have hr : (r.val : ℤ) < M := by exact_mod_cast r.isLt
  have he : completeResidueCellPoint k M q r t =
      ((k * q + t.val) * M) + r.val := by unfold completeResidueCellPoint; push_cast; ring
  rw [he]
  simp [Int.add_emod, Int.emod_eq_of_lt (Int.natCast_nonneg r.val) hr]

theorem completeResidueCellPoint_mem (k : ℤ) (M q : ℕ) (hM : 0 < M)
    (r : Fin M) (t : Fin q) :
    completeResidueCellPoint k M q r t ∈ intervalResidueSet (k * (M * q : ℕ)) (M * q) M r.val := by
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_Ico.mpr (completeResidueCellPoint_bounds k M q hM r t),
    completeResidueCellPoint_residue k M q r t⟩

theorem completeResidueCellPoint_injective (k : ℤ) (M q : ℕ) (hM : 0 < M) (r : Fin M) :
    Function.Injective (completeResidueCellPoint k M q r) := by
  intro t u htu
  apply Fin.ext
  have hMp : (0 : ℤ) < M := by exact_mod_cast hM
  have he : (t.val : ℤ) = u.val := by
    dsimp [completeResidueCellPoint] at htu
    nlinarith
  exact_mod_cast he

theorem completeResidueCellPoint_surjective (k : ℤ) (M q : ℕ) (hM : 0 < M) (r : Fin M)
    (y : ℤ) (hy : y ∈ intervalResidueSet (k * (M * q : ℕ)) (M * q) M r.val) :
    ∃ t : Fin q, completeResidueCellPoint k M q r t = y := by
  obtain ⟨hwin, hres⟩ := Finset.mem_filter.mp hy
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hwin
  have hMp : (0 : ℤ) < M := by exact_mod_cast hM
  have hr : (r.val : ℤ) < M := by exact_mod_cast r.isLt
  let t : ℤ := y / M - k * q
  have he : y = k * (M * q : ℕ) + r.val + (M : ℤ) * t := by
    have hd := Int.mul_ediv_add_emod y (M : ℤ)
    rw [hres] at hd
    dsimp [t]
    nlinarith
  have ht0 : 0 ≤ t := by
    by_contra hneg
    have ht : t ≤ -1 := by omega
    have hm := mul_le_mul_of_nonneg_left ht hMp.le
    nlinarith
  have htq : t < q := by
    by_contra hneg
    have ht : (q : ℤ) ≤ t := by omega
    have hm := mul_le_mul_of_nonneg_left ht hMp.le
    push_cast at hhi he
    nlinarith [Int.natCast_nonneg r.val]
  have htn : t.toNat < q := by
    have htcast : (t.toNat : ℤ) < q := by simpa only [Int.toNat_of_nonneg ht0] using htq
    exact_mod_cast htcast
  refine ⟨⟨t.toNat, htn⟩, ?_⟩
  simpa only [completeResidueCellPoint, Int.toNat_of_nonneg ht0] using he.symm

theorem completeResidueCell_card (k : ℤ) (M q : ℕ) (hM : 0 < M) (r : Fin M) :
    (intervalResidueSet (k * (M * q : ℕ)) (M * q) M r.val).card = q := by
  have he := Finset.card_bij
    (s := (Finset.univ : Finset (Fin q)))
    (t := intervalResidueSet (k * (M * q : ℕ)) (M * q) M r.val)
    (fun t _ => completeResidueCellPoint k M q r t)
    (fun t _ => completeResidueCellPoint_mem k M q hM r t)
    (fun t _ u _ htu => completeResidueCellPoint_injective k M q hM r htu)
    (fun y hy => by
      obtain ⟨t, ht⟩ := completeResidueCellPoint_surjective k M q hM r y hy
      exact ⟨t, Finset.mem_univ _, ht⟩)
  simpa only [Finset.card_univ, Fintype.card_fin] using he.symm

end Hindman168
