import Hindman168.AdditiveCopyExactCounts
import Hindman168.AdditiveRowTerminalProducts

/-! Exact regrouping of all old non-target copies into the complete
retained product. No non-target factor is divided out or discarded. -/

namespace Hindman168.AdditiveRowData

open scoped BigOperators Classical

variable {b c : ℕ}

theorem retained_product_flat (D : AdditiveRowData b c)
    (z : Fin c → ℤ) (v : Fin b → ℤ × ℤ) (Ω : ReplicaCubeRow b 1 → ℤ → ℝ) :
    (∏ i : {r : ReplicaCubeRow b 1 // r ≠ none},
      D.stageFactorProduct Finset.univ i.val z (predictionPairValues v) (Ω i.val)) =
        ∏ r : AdditiveNonRootCopy b,
          Ω r.val.val.1 (D.translatedForm r.val.val.1 r.val.val.2 z (predictionPairValues v)) := by
  have hr := D.eliminationIntegrand_terminal_retained z v (fun _ _ => 1) Ω
  rw [D.stageFactorProduct_full_root] at hr
  simp only [Finset.prod_const, one_pow, one_mul] at hr
  have hf := D.eliminationIntegrand_terminal_flat z v (fun _ _ => 1) Ω
  have hp : (fun r : AdditiveNonRootCopy b =>
      if r.val.val.1 = none then (1 : ℝ) else
        Ω r.val.val.1 (D.translatedForm r.val.val.1 r.val.val.2 z (predictionPairValues v))) =
      (fun r : AdditiveNonRootCopy b =>
        Ω r.val.val.1 (D.translatedForm r.val.val.1 r.val.val.2 z (predictionPairValues v))) :=
    funext (fun r => if_neg r.property)
  have hn : (fun r : {r : CopiedReplicaCubeRow (additiveRowAssigned b) // ¬ r.val.1 ≠ none} =>
      if r.val.val.1 = none then (1 : ℝ) else
        Ω r.val.val.1 (D.translatedForm r.val.val.1 r.val.val.2 z (predictionPairValues v))) =
      (fun _ => (1 : ℝ)) := funext (fun r => if_pos (not_ne_iff.mp r.property))
  rw [← Fintype.prod_subtype_mul_prod_subtype
    (fun r : CopiedReplicaCubeRow (additiveRowAssigned b) => r.val.1 ≠ none), hp, hn] at hf
  simp only [Finset.prod_const, one_pow, mul_one] at hf
  exact hr.symm.trans hf

end Hindman168.AdditiveRowData
