import Hindman168.MaskMasterGapIndependence

/-! A block is represented by a one-column chain before any later chain
selection. All permissible gaps at this block form a finite family in the
same original mask master catalogue. The family also retains the zero-prime
test used for nilsequence comparison. -/

namespace Hindman168
open Filter
open scoped Topology Classical

def maskBlockChain (T : Finset ℕ) (i : ℕ) (hT : T.Nonempty)
    (hTi : T ⊆ Finset.range i) : Chain 1 where
  tail := fun _ => T
  pivot := fun _ => i
  tail_nonempty := fun _ => hT
  tail_before := by intro a b hab; have := a.isLt; have := b.isLt; omega
  tails_before_pivots := fun _ _ _ hx => Finset.mem_range.mp (hTi hx)
  pivot_strictMono := by intro a b hab; have := a.isLt; have := b.isLt; omega

abbrev MaskValidBlockGap {N : ℕ} (T : Finset ℕ) (i : Fin N) :=
  {l : Fin N // T ⊆ Finset.range l.val ∧ l.val ≤ i.val}

theorem maskBlockChain_block_range {N : ℕ} (T : Finset ℕ) (i : Fin N)
    (hT : T.Nonempty) (hTi : T ⊆ Finset.range i.val) (col : Fin 1) :
    (maskBlockChain T i.val hT hTi).block col ⊆ Finset.range N := by
  intro x hx
  simp only [Chain.block, maskBlockChain, Finset.mem_insert] at hx
  rcases hx with rfl | hx
  · exact Finset.mem_range.mpr i.isLt
  · exact Finset.mem_range.mpr ((Finset.mem_range.mp (hTi hx)).trans i.isLt)

theorem masterPredictionBlockMask_eq_of_tail {b c : ℕ}
    (F : MasterParameterFamily) (C : ℕ → Chain b) (label : ℕ → Fin b)
    (E : ℕ → Chain c) (other : ℕ → Fin c) (w : ℕ)
    (ht : (C w).tail (label w) = (E w).tail (other w)) :
    masterPredictionBlockMask F C label w = masterPredictionBlockMask F E other w := by
  let H (S : Finset ℕ) : ℤ → ℝ := integerDivisorMask
    (tailMass (primorial w) (List.ofFn (fun j : Fin S.card => F.cutoff w (S.orderIsoOfFin rfl j))))
  change H ((C w).tail (label w)) = H ((E w).tail (other w))
  exact congrArg H ht

theorem maskBlockGap_templates_conditions (m d₀ : ℕ) (hd₀ : 0 < d₀)
    {N : ℕ} (hN : 0 < N) (T : Finset ℕ) (i : Fin N)
    (l : MaskValidBlockGap T i)
    (t : Fin (Fintype.card (LargeColumnSubset m) + 1)) :
    OriginalDualTemplateConditions
      (maskGeneratedDualTemplates m (fun _ => l.val) d₀ (fun _ => l.val) t)
      (originalRowMasterCatalog (maskGeneratedRowDataFamily m (fun _ => ⟨0, hN⟩)))
      (max d₀ (maskRowCountBound m)) (fun _ => T) (fun _ => i) := by
  have h := originalRowAndZeroTemplates_conditions
    (maskGeneratedRowDataFamily m (fun _ => l.val)) d₀ (max d₀ (maskRowCountBound m))
    hd₀ (le_max_left _ _)
    (fun z => (maskGeneratedRowDataFamily_dimension_le m (fun _ => l.val) z).trans
      (le_max_right _ _)) (fun _ => l.val) (fun _ => T) (fun _ => i)
    (Eventually.of_forall (fun _ => l.property.1))
    (Eventually.of_forall (fun _ => l.property.2))
    (fun _ => Eventually.of_forall (fun _ => l.property.1))
    (fun _ => Eventually.of_forall (fun _ => l.property.2)) t
  exact h

end Hindman168
