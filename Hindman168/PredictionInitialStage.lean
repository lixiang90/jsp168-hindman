import Hindman168.MasterPredictionEliminationLimit

/-!
# The initial stage is the actual averaged translated row product

Before any duplication, each original base row has exactly one canonical
copy, with every direction bit false. Its evaluation is the original
integer row at the sum of the inserted directions. Unused true samples
therefore appear nowhere in the initial integrand.
-/

namespace Hindman168

open scoped BigOperators Classical

theorem predictionStageRowCopies_empty {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) (base : ReplicaCubeRow b d) :
    predictionStageRowCopies dir ∅ base =
      {canonicalReplicaCubeCopy dir base (fun _ => false)} := by
  ext r
  rw [mem_predictionStageRowCopies, Finset.mem_singleton]
  constructor
  · rintro ⟨hr, hb⟩
    apply Subtype.ext
    refine Prod.ext hb ?_
    funext i
    have hi := hr i (Finset.notMem_empty i)
    simpa only [canonicalReplicaCubeCopy, ite_self] using hi
  · rintro rfl
    refine ⟨?_, rfl⟩
    intro i _
    simp only [canonicalReplicaCubeCopy, ite_self]

theorem predictionEliminationTest_empty {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) (F Ω : ReplicaCubeRow b d → ℤ → ℝ)
    (base : ReplicaCubeRow b d) : predictionEliminationTest dir ∅ F Ω base = F base := by
  simp only [predictionEliminationTest, Finset.image_empty, Finset.notMem_empty, ite_false]

theorem predictionStageFactorProduct_empty {b d h : ℕ}
    (M : Fin b → ℤ) (dir : Fin h → Fin b × CubeVertex d) (base : ReplicaCubeRow b d)
    (z : ReplicaCubeColumn b d → ℤ) (v : Fin h → ℤ × ℤ) (F : ℤ → ℝ) :
    predictionStageFactorProduct M dir ∅ base z (predictionPairValues v) F =
      F (copiedReplicaCubeForm M dir base (fun _ => false) z (predictionPairValues v)) := by
  rw [predictionStageFactorProduct_eq_prod, predictionStageRowCopies_empty, Finset.prod_singleton,
    copiedReplicaCubeForm_canonical]

theorem predictionEliminationIntegrand_initial_translate {b d h : ℕ}
    (M : Fin b → ℤ) (dir : Fin h → Fin b × CubeVertex d)
    (z : ReplicaCubeColumn b d → ℤ) (v : Fin h → ℤ × ℤ)
    (F Ω : ReplicaCubeRow b d → ℤ → ℝ) :
    predictionEliminationIntegrand M dir ∅ z v F Ω =
      ∏ base : ReplicaCubeRow b d, F base (replicaCubeEval M base (fun col => z col +
        ∑ i, (v i).1 * replicaCubeDirection M (dir i).1 (dir i).2 col)) := by
  unfold predictionEliminationIntegrand
  simp only [predictionEliminationTest_empty, predictionStageFactorProduct_empty]
  apply Fintype.prod_congr
  intro base
  rw [← copiedReplicaCubeForm_translate]
  rfl

end Hindman168
