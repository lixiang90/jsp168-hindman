import Hindman168.IntegerProductLaw
import Hindman168.TensorProbability

/-!
# Quantitative joint product laws for independent harmonic blocks

Each block consists of an independent harmonic tail and pivot. The joint
PMF is explicitly the independent tensor of their actual product laws.
Comparison measures retain their original masses. Global raw-index
relabeling for disjoint Chain blocks is a separate bookkeeping step.
-/

namespace Hindman168

open scoped BigOperators

structure BlockCutoffs where
  tailCutoffs : List ℕ
  pivotCutoff : ℕ

def ValidBlockCutoffs (W : ℕ) (b : BlockCutoffs) : Prop :=
  ValidCutoffs b.tailCutoffs W ∧ 2 ≤ b.pivotCutoff ∧
    (W : ℝ) / b.pivotCutoff < Real.log b.pivotCutoff ∧ tailBound b.tailCutoffs ≤ b.pivotCutoff

noncomputable def blockOriginal (W : ℕ) (b : BlockCutoffs) : FiniteMass.Mass ℕ :=
  productMass (tailMass W b.tailCutoffs) b.pivotCutoff W

noncomputable def blockComparison (W : ℕ) (b : BlockCutoffs) : FiniteMass.Mass ℕ :=
  productComparisonMass (tailMass W b.tailCutoffs) b.pivotCutoff W

theorem blockOriginal_nonneg {W : ℕ} (b : BlockCutoffs) (hW : 0 < W)
    (hb : ValidBlockCutoffs W b) (n : ℕ) : 0 ≤ blockOriginal W b n :=
  productMass_nonneg (tailMass_nonneg hW b.tailCutoffs hb.1)
    (harmonicNormalizer_pos hb.2.1 hW hb.2.2.1) n

theorem blockOriginal_total {W : ℕ} (b : BlockCutoffs) (hW : 0 < W)
    (hb : ValidBlockCutoffs W b) : FiniteMass.total (blockOriginal W b) = 1 :=
  productMass_total (tailMass_total hW b.tailCutoffs hb.1)
    (harmonicNormalizer_pos hb.2.1 hW hb.2.2.1)

theorem blockComparison_nonneg {W : ℕ} (b : BlockCutoffs) (hW : 0 < W)
    (hb : ValidBlockCutoffs W b) (n : ℕ) : 0 ≤ blockComparison W b n :=
  productComparisonMass_nonneg (tailMass_nonneg hW b.tailCutoffs hb.1)
    (harmonicNormalizer_pos hb.2.1 hW hb.2.2.1) n

noncomputable def blockProductPMF (W : ℕ) (b : BlockCutoffs) (hW : 0 < W)
    (hb : ValidBlockCutoffs W b) : PMF ℕ :=
  productPMF (tailMass W b.tailCutoffs) (tailMass_nonneg hW b.tailCutoffs hb.1)
    (tailMass_total hW b.tailCutoffs hb.1) b.pivotCutoff W
    (harmonicNormalizer_pos hb.2.1 hW hb.2.2.1)

theorem blockProductPMF_eq_toPMF {W : ℕ} (b : BlockCutoffs) (hW : 0 < W)
    (hb : ValidBlockCutoffs W b) :
    blockProductPMF W b hW hb = FiniteMass.toPMF (blockOriginal W b)
      (blockOriginal_nonneg b hW hb) (blockOriginal_total b hW hb) := productPMF_eq_toPMF _ _ _

noncomputable def jointOriginal (W : ℕ) (bs : List BlockCutoffs) : FiniteMass.Mass (List ℕ) :=
  FiniteMass.tensorList (bs.map (blockOriginal W))

noncomputable def jointComparison (W : ℕ) (bs : List BlockCutoffs) : FiniteMass.Mass (List ℕ) :=
  FiniteMass.tensorList (bs.map (blockComparison W))

noncomputable def jointProductPMF (W : ℕ) (bs : List BlockCutoffs) (hW : 0 < W)
    (hv : ∀ b ∈ bs, ValidBlockCutoffs W b) : PMF (List ℕ) :=
  FiniteMass.tensorListPMF (bs.map (blockOriginal W))
    (by intro μ hμ; obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hμ; exact blockOriginal_nonneg b hW (hv b hb))
    (by intro μ hμ; obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hμ; exact blockOriginal_total b hW (hv b hb))

theorem jointProductPMF_apply {W : ℕ} (bs : List BlockCutoffs) (hW : 0 < W)
    (hv : ∀ b ∈ bs, ValidBlockCutoffs W b) (ys : List ℕ) :
    jointProductPMF W bs hW hv ys = ENNReal.ofReal (jointOriginal W bs ys) := rfl

/-- Recursive sampling uses the actual law of each block product. -/
theorem jointProductPMF_cons {W : ℕ} (b : BlockCutoffs) (bs : List BlockCutoffs) (hW : 0 < W)
    (hv : ∀ c ∈ b :: bs, ValidBlockCutoffs W c) :
    jointProductPMF W (b :: bs) hW hv =
      (FiniteMass.pairPMF (blockProductPMF W b hW (hv b List.mem_cons_self))
        (jointProductPMF W bs hW (fun c hc => hv c (List.mem_cons_of_mem b hc)))).map
          (fun x => x.1 :: x.2) := by
  unfold jointProductPMF
  simp only [List.map_cons]
  rw [FiniteMass.tensorListPMF_cons, blockProductPMF_eq_toPMF]

theorem jointComparison_apply_cons (W : ℕ) (b : BlockCutoffs) (bs : List BlockCutoffs)
    (y : ℕ) (ys : List ℕ) :
    jointComparison W (b :: bs) (y :: ys) =
      (harmonicWeight b.pivotCutoff W y * divisorMask (tailMass W b.tailCutoffs) y) *
        jointComparison W bs ys := by
  rw [jointComparison, List.map_cons, FiniteMass.tensorList_apply_cons,
    blockComparison, productComparisonMass_apply]
  rfl

/-- All component errors and masses are derived from harmonic sampling. -/
theorem joint_product_law_error {W : ℕ} (bs : List BlockCutoffs) (hW : 0 < W)
    (hv : ∀ b ∈ bs, ValidBlockCutoffs W b) {E M : ℝ} (hM : 0 ≤ M)
    (he : ∀ b ∈ bs, dilationError b.pivotCutoff W (tailBound b.tailCutoffs) ≤ E)
    (hm : ∀ b ∈ bs, residueError b.pivotCutoff W (tailBound b.tailCutoffs) ≤ M - 1) :
    FiniteMass.distance (jointOriginal W bs) (jointComparison W bs) ≤
      E * ∑ i ∈ Finset.range bs.length, M ^ i := by
  have h := FiniteMass.tensorList_distance_uniform
    (bs.map (fun b => (blockOriginal W b, blockComparison W b))) (E := E) hM
  have hc : ∀ p ∈ bs.map (fun b => (blockOriginal W b, blockComparison W b)),
      (∀ a, 0 ≤ p.1 a) ∧ FiniteMass.total p.1 = 1 ∧ (∀ a, 0 ≤ p.2 a) ∧
        FiniteMass.total p.2 ≤ M ∧ FiniteMass.distance p.1 p.2 ≤ E := by
    intro p hp
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hp
    have hvb := hv b hb
    refine ⟨blockOriginal_nonneg b hW hvb, blockOriginal_total b hW hvb,
      blockComparison_nonneg b hW hvb, ?_, ?_⟩
    · have hmass := (abs_le.mp (block_product_comparison_mass_error b.tailCutoffs hW
        hvb.1 hvb.2.1 hvb.2.2.1)).2
      have hbmass := hm b hb
      change FiniteMass.total (productComparisonMass (tailMass W b.tailCutoffs) b.pivotCutoff W) ≤ M
      linarith
    · exact (block_product_law_error b.tailCutoffs hW hvb.1 hvb.2.1
        hvb.2.2.1 hvb.2.2.2).trans (he b hb)
  simpa only [List.map_map, Function.comp_def, List.length_map, jointOriginal, jointComparison] using h hc

theorem list_natCast_injective : Function.Injective (fun xs : List ℕ => xs.map (fun n : ℕ => (n : ℤ))) := by
  intro xs ys h
  exact (List.map_inj_right (f := fun n : ℕ => (n : ℤ)) Int.ofNat_injective).mp h

noncomputable def jointIntegerOriginal (W : ℕ) (bs : List BlockCutoffs) : FiniteMass.Mass (List ℤ) :=
  (jointOriginal W bs).mapDomain (fun xs => xs.map (fun n : ℕ => (n : ℤ)))

noncomputable def jointIntegerComparison (W : ℕ) (bs : List BlockCutoffs) : FiniteMass.Mass (List ℤ) :=
  (jointComparison W bs).mapDomain (fun xs => xs.map (fun n : ℕ => (n : ℤ)))

theorem jointIntegerProductPMF_apply {W : ℕ} (bs : List BlockCutoffs) (hW : 0 < W)
    (hv : ∀ b ∈ bs, ValidBlockCutoffs W b) (zs : List ℤ) :
    ((jointProductPMF W bs hW hv).map (fun xs => xs.map (fun n : ℕ => (n : ℤ)))) zs =
      ENNReal.ofReal (jointIntegerOriginal W bs zs) := by
  rw [jointProductPMF, FiniteMass.tensorListPMF, FiniteMass.toPMF_map_apply]
  rfl

theorem integer_joint_product_law_error {W : ℕ} (bs : List BlockCutoffs) (hW : 0 < W)
    (hv : ∀ b ∈ bs, ValidBlockCutoffs W b) {E M : ℝ} (hM : 0 ≤ M)
    (he : ∀ b ∈ bs, dilationError b.pivotCutoff W (tailBound b.tailCutoffs) ≤ E)
    (hm : ∀ b ∈ bs, residueError b.pivotCutoff W (tailBound b.tailCutoffs) ≤ M - 1) :
    FiniteMass.distance (jointIntegerOriginal W bs) (jointIntegerComparison W bs) ≤
      E * ∑ i ∈ Finset.range bs.length, M ^ i := by
  rw [jointIntegerOriginal, jointIntegerComparison,
    FiniteMass.distance_push_injective
      (f := fun xs : List ℕ => xs.map (fun n : ℕ => (n : ℤ))) list_natCast_injective]
  exact joint_product_law_error bs hW hv hM he hm

end Hindman168
