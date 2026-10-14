import Hindman168.AdditiveRowOrderedRecurrence

/-! Exact initial shifted correlation and terminal target cube times weights. -/

namespace Hindman168

open scoped BigOperators Classical

theorem additiveStageRowCopies_empty (b : ℕ) (i : ReplicaCubeRow b 1) :
    predictionStageRowCopies (additiveRowAssigned b) ∅ i =
      {canonicalReplicaCubeCopy (additiveRowAssigned b) i (fun _ => false)} := by
  ext r
  rw [mem_predictionStageRowCopies, Finset.mem_singleton]
  constructor
  · rintro ⟨hη, hb⟩
    apply Subtype.ext
    apply Prod.ext
    · exact hb
    · funext k
      have hk := hη k (Finset.notMem_empty k)
      simp only [canonicalReplicaCubeCopy, ite_self]
      exact hk
  · intro hr
    subst r
    refine ⟨?_, rfl⟩
    intro k _
    simp only [canonicalReplicaCubeCopy, ite_self]

namespace AdditiveRowData

variable {b c : ℕ}

theorem stageFactorProduct_empty (D : AdditiveRowData b c) (i : ReplicaCubeRow b 1)
    (z : Fin c → ℤ) (v : Fin b → Bool → ℤ) (F : ℤ → ℝ) :
    D.stageFactorProduct ∅ i z v F =
      F (D.form i (fun j => z j + ∑ k, v k false * D.direction k j)) := by
  rw [D.stageFactorProduct_eq_prod, additiveStageRowCopies_empty]
  simp only [Finset.prod_singleton, canonicalReplicaCubeCopy, ite_self]
  rw [D.translatedForm_eq_translate]

theorem eliminationIntegrand_empty (D : AdditiveRowData b c) (z : Fin c → ℤ)
    (v : Fin b → ℤ × ℤ) (F Ω : ReplicaCubeRow b 1 → ℤ → ℝ) :
    D.eliminationIntegrand ∅ z v F Ω =
      ∏ i : ReplicaCubeRow b 1, F i (D.form i (fun j => z j + ∑ k, (v k).1 * D.direction k j)) := by
  unfold eliminationIntegrand
  simp only [predictionEliminationTest, Finset.image_empty, Finset.notMem_empty, ite_false]
  simp only [D.stageFactorProduct_empty, predictionPairValues, Bool.false_eq_true, ite_false]

theorem stageFactorProduct_full_root (D : AdditiveRowData b c) (z : Fin c → ℤ)
    (v : Fin b → Bool → ℤ) (F : ℤ → ℝ) :
    D.stageFactorProduct Finset.univ none z v F =
      ∏ η : Fin b → Bool, F (D.translatedForm none η z v) := by
  rw [D.stageFactorProduct_eq_prod]
  apply Finset.prod_bij (fun r _ => r.val.2)
  · intro r _
    exact Finset.mem_univ _
  · intro r hr s hs he
    have hrb := ((mem_predictionStageRowCopies _ _ none r).mp hr).2
    have hsb := ((mem_predictionStageRowCopies _ _ none s).mp hs).2
    apply Subtype.ext
    exact Prod.ext (hrb.trans hsb.symm) he
  · intro η _
    refine ⟨replicaRootCopy (additiveRowAssigned b) η, ?_, rfl⟩
    apply (mem_predictionStageRowCopies _ _ _ _).mpr
    exact ⟨fun k hk => (hk (Finset.mem_univ k)).elim, rfl⟩
  · intro r hr
    have hb := ((mem_predictionStageRowCopies _ _ none r).mp hr).2
    rw [hb]

theorem stageFactorProduct_full_target_cube (D : AdditiveRowData b c) (M : ℤ)
    (hM : ∀ k, D.response none k = M) (z : Fin c → ℤ)
    (v : Fin b → ℤ × ℤ) (F : ℤ → ℝ) :
    D.stageFactorProduct Finset.univ none z (predictionPairValues v) F =
      ∏ η : Fin b → Bool, F (D.form none z + M * ∑ k, predictionPairValues v k (η k)) := by
  rw [D.stageFactorProduct_full_root]
  apply Fintype.prod_congr
  intro η
  simp only [translatedForm, hM, Finset.mul_sum]

theorem eliminationIntegrand_terminal_retained (D : AdditiveRowData b c)
    (z : Fin c → ℤ) (v : Fin b → ℤ × ℤ) (F Ω : ReplicaCubeRow b 1 → ℤ → ℝ) :
    D.eliminationIntegrand Finset.univ z v F Ω =
      D.stageFactorProduct Finset.univ none z (predictionPairValues v) (F none) *
      ∏ i : {r : ReplicaCubeRow b 1 // r ≠ none},
        D.stageFactorProduct Finset.univ i.val z (predictionPairValues v) (Ω i.val) := by
  unfold eliminationIntegrand
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ none, predictionEliminationTest_root]
  congr 1
  apply Fintype.prod_congr
  intro i
  cases hb : i.val with
  | none => exact (i.property hb).elim
  | some j => rw [predictionEliminationTest_full_nonroot _ (additiveRowAssigned_surjective b)]

theorem eliminationIntegrand_terminal_cube (D : AdditiveRowData b c) (M : ℤ)
    (hM : ∀ k, D.response none k = M) (z : Fin c → ℤ)
    (v : Fin b → ℤ × ℤ) (F Ω : ReplicaCubeRow b 1 → ℤ → ℝ) :
    D.eliminationIntegrand Finset.univ z v F Ω =
      (∏ η : Fin b → Bool, F none (D.form none z + M * ∑ k, predictionPairValues v k (η k))) *
      ∏ i : {r : ReplicaCubeRow b 1 // r ≠ none},
        D.stageFactorProduct Finset.univ i.val z (predictionPairValues v) (Ω i.val) := by
  rw [D.eliminationIntegrand_terminal_retained, D.stageFactorProduct_full_target_cube M hM]

end AdditiveRowData
end Hindman168
