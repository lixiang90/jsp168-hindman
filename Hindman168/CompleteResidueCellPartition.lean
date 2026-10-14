import Hindman168.CompleteResidueCellMassAggregate
import Hindman168.NilPieceCubeGeometry

namespace Hindman168
open scoped BigOperators

theorem mem_intervalResidueSet_iff_piece (R M : ℕ) (hR : 0 < R)
    (k : ℤ) (r : Fin M) (y : ℤ) :
    y ∈ intervalResidueSet (k * R) R M r.val ↔
      intervalResiduePiece R M y = (k, (r.val : ℤ)) := by
  have hp : (0 : ℤ) < R := by exact_mod_cast hR
  simp only [intervalResidueSet, integerWindow, Finset.mem_filter, Finset.mem_Ico,
    intervalResiduePiece, Prod.mk.injEq, Int.ediv_eq_iff_of_pos hp]

theorem intervalResidueSet_pairwise_disjoint (R M : ℕ) (hR : 0 < R)
    (c d : ℤ × Fin M) (hne : c ≠ d) :
    Disjoint (intervalResidueSet (c.1 * R) R M c.2.val)
      (intervalResidueSet (d.1 * R) R M d.2.val) := by
  apply Finset.disjoint_left.mpr
  intro y hy hz
  have hc := (mem_intervalResidueSet_iff_piece R M hR c.1 c.2 y).mp hy
  have hd := (mem_intervalResidueSet_iff_piece R M hR d.1 d.2 y).mp hz
  have he := hc.symm.trans hd
  have he' := Prod.mk.inj he
  apply hne
  apply Prod.ext
  · exact he'.1
  · apply Fin.ext
    exact_mod_cast he'.2

theorem intervalResidueSet_union_sum (R M : ℕ) (hR : 0 < R)
    (C : Finset (ℤ × Fin M)) (F : ℤ → ℝ) :
    (∑ y ∈ C.biUnion (fun c => intervalResidueSet (c.1 * R) R M c.2.val), F y) =
      ∑ c ∈ C, ∑ y ∈ intervalResidueSet (c.1 * R) R M c.2.val, F y := by
  classical
  apply Finset.sum_biUnion
  intro c _ d _ hne
  exact intervalResidueSet_pairwise_disjoint R M hR c d hne

end Hindman168
