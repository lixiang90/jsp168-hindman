import Hindman168.CompleteResidueCell
import Hindman168.NilPieceLinearOrbits

namespace Hindman168

theorem completeResidueCellPoint_ediv (k : ℤ) (M q : ℕ) (hM : 0 < M)
    (r : Fin M) (t : Fin q) :
    completeResidueCellPoint k M q r t / (M : ℤ) = k * q + t.val := by
  have hm : (M : ℤ) ≠ 0 := by exact_mod_cast hM.ne'
  have hr : (r.val : ℤ) < M := by exact_mod_cast r.isLt
  have he : completeResidueCellPoint k M q r t =
      (r.val : ℤ) + (M : ℤ) * (k * q + t.val) := by
    unfold completeResidueCellPoint
    push_cast
    ring
  rw [he, Int.add_mul_ediv_left _ _ hm,
    Int.ediv_eq_zero_of_lt (Int.natCast_nonneg r.val) hr, zero_add]

/-- The original globally anchored exponent y/M realizes a locally
selected cyclic orbit after rebasing by the negative interval exponent. -/
theorem completeResidueCellPoint_orbit_rebase {G : Type*} [Group G] (Γ : Subgroup G)
    (k : ℤ) (M q : ℕ) (hM : 0 < M) (r : Fin M) (t : Fin q) (g x : G) :
    (g ^ (completeResidueCellPoint k M q r t / (M : ℤ)) * (g ^ (-(k * q)) * x) : G ⧸ Γ) =
      (g ^ (t.val : ℤ) * x : G ⧸ Γ) := by
  rw [completeResidueCellPoint_ediv k M q hM r t, add_comm (k * (q : ℤ)), zpow_add,
    mul_assoc, ← mul_assoc (g ^ (k * (q : ℤ))) (g ^ (-(k * (q : ℤ)))) x, ← zpow_add]
  simp only [add_neg_cancel, zpow_zero, one_mul]

theorem completeResidueCell_nil_correlation_rebase {G : Type*} [Group G]
    (Γ : Subgroup G) (k : ℤ) (M q : ℕ) (hM : 0 < M) (r : Fin M)
    (f : ℤ → ℝ) (obs : (G ⧸ Γ) → ℝ) (g x : G) :
    finiteHaarMean (fun t : Fin q => f (completeResidueCellPoint k M q r t) *
      obs (pieceLinearOrbit Γ M (fun _ : Unit => g) (fun _ => g ^ (-(k * q)) * x)
        () (completeResidueCellPoint k M q r t))) =
      finiteHaarMean (fun t : Fin q => f (completeResidueCellPoint k M q r t) *
        obs (g ^ (t.val : ℤ) * x)) := by
  congr 1
  funext t
  rw [pieceLinearOrbit, completeResidueCellPoint_orbit_rebase Γ k M q hM r t g x]

end Hindman168
