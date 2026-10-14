import Hindman168.PredictionTranslationLaw
import Hindman168.QuotientIntervalGrowth

/-!
# Actual square-root pair sampling and the initial insertion bound

Auxiliary parameters are independently uniform on [0, floor(sqrt(T_q)))
for their assigned replica. Both independent samples use the same law.
The resulting initial-stage average differs from the original row product
by the explicit insertion cap. Modulus times original length bounds the
root displacement, even when replicas have different gap lengths.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

theorem uniformIntervalMass_support_bounds (A : ℤ) (T : ℕ) {z : ℤ}
    (hz : z ∈ (uniformIntervalMass A T).support) : A ≤ z ∧ z < A + T := by
  have hn := Finsupp.mem_support_iff.mp hz
  have hm : z ∈ integerWindow A T := by
    by_contra hc
    exact hn (by rw [uniformIntervalMass_apply, if_neg hc])
  exact Finset.mem_Ico.mp hm

noncomputable def predictionSquareRootPairMass {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) (T : Fin b → ℕ) : Mass (Fin h → ℤ × ℤ) :=
  piMass (fun i => tensor (uniformIntervalMass 0 (Nat.sqrt (T (dir i).1)))
    (uniformIntervalMass 0 (Nat.sqrt (T (dir i).1))))

theorem predictionSquareRootPairMass_nonneg {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) (T : Fin b → ℕ) :
    ∀ v, 0 ≤ predictionSquareRootPairMass dir T v :=
  piMass_nonneg _ (fun _ => tensor_nonneg _ _
    (uniformIntervalMass_nonneg _ _) (uniformIntervalMass_nonneg _ _))

theorem predictionSquareRootPairMass_total {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) (T : Fin b → ℕ) (hT : ∀ q, 0 < T q) :
    total (predictionSquareRootPairMass dir T) = 1 := by
  apply piMass_total_one
  intro i
  rw [tensor_total, uniformIntervalMass_total 0 (Nat.sqrt_pos.mpr (hT _)), one_mul]

theorem predictionSquareRootPairMass_first_bound {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) (T : Fin b → ℕ)
    {v : Fin h → ℤ × ℤ} (hv : v ∈ (predictionSquareRootPairMass dir T).support) (i : Fin h) :
    |((v i).1 : ℝ)| ≤ (Nat.sqrt (T (dir i).1) : ℝ) := by
  classical
  have hn := Finsupp.mem_support_iff.mp hv
  change (∏ k : Fin h, tensor (uniformIntervalMass 0 (Nat.sqrt (T (dir k).1)))
    (uniformIntervalMass 0 (Nat.sqrt (T (dir k).1))) (v k)) ≠ 0 at hn
  have hc := Finset.prod_ne_zero_iff.mp hn i (Finset.mem_univ i)
  have hf : (v i).1 ∈ (uniformIntervalMass 0 (Nat.sqrt (T (dir i).1))).support :=
    Finsupp.mem_support_iff.mpr (left_ne_zero_of_mul hc)
  have hb := uniformIntervalMass_support_bounds 0 _ hf
  have hnonneg : (0 : ℝ) ≤ (v i).1 := by exact_mod_cast hb.1
  rw [abs_of_nonneg hnonneg]
  exact_mod_cast (by omega : (v i).1 ≤ (Nat.sqrt (T (dir i).1) : ℤ))

theorem predictionSquareRootPairMass_root_bound {b d h : ℕ}
    (M : Fin b → ℤ) (dir : Fin h → Fin b × CubeVertex d)
    (T : Fin b → ℕ) (R : Fin b → ℝ)
    (hR : ∀ q, |(M q : ℝ)| * T q ≤ R q)
    {v : Fin h → ℤ × ℤ} (hv : v ∈ (predictionSquareRootPairMass dir T).support) (i : Fin h) :
    |((M (dir i).1 * (v i).1 : ℤ) : ℝ)| ≤ R (dir i).1 := by
  rw [Int.cast_mul, abs_mul]
  calc
    _ ≤ |(M (dir i).1 : ℝ)| * (Nat.sqrt (T (dir i).1) : ℝ) :=
      mul_le_mul_of_nonneg_left (predictionSquareRootPairMass_first_bound dir T hv i) (abs_nonneg _)
    _ ≤ |(M (dir i).1 : ℝ)| * (T (dir i).1 : ℝ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.sqrt_le_self (T (dir i).1)) (abs_nonneg _)
    _ ≤ _ := hR _

theorem prediction_square_root_initial_insertion_error {b d h : ℕ}
    (X W : ℕ) (A : Fin b × Fin d × Bool → ℤ) (T : Fin b → ℕ)
    (M : Fin b → ℤ) (dir : Fin h → Fin b × CubeVertex d) (R : Fin b → ℝ)
    (G Ω : ReplicaCubeRow b d → ℤ → ℝ) {B : ℝ}
    (hB : 0 ≤ B) (hG : ∀ base y, |G base y| ≤ B)
    (hX : 2 ≤ X) (hW : 0 < W) (hlog : (W : ℝ) / X < Real.log X)
    (hT : ∀ q, 0 < T q) (hM : ∀ q, (W : ℤ) ∣ M q)
    (hR : ∀ q, |(M q : ℝ)| * T q ≤ R q) :
    |expectation (piMass (predictionOriginalColumnMass X W A T))
        (fun z => expectation (predictionSquareRootPairMass dir T)
          (fun v => predictionEliminationIntegrand M dir ∅ z v G Ω)) -
      expectation (piMass (predictionOriginalColumnMass X W A T))
        (fun z => ∏ base, G base (replicaCubeEval M base z))| ≤
      B ^ Fintype.card (ReplicaCubeRow b d) *
        predictionInsertionErrorCap X W T dir R (fun q => (Nat.sqrt (T q) : ℝ)) := by
  have hZ := harmonicNormalizer_pos hX hW hlog
  have hcomm : expectation (piMass (predictionOriginalColumnMass X W A T))
      (fun z => expectation (predictionSquareRootPairMass dir T)
        (fun v => predictionEliminationIntegrand M dir ∅ z v G Ω)) =
      expectation (predictionSquareRootPairMass dir T)
        (fun v => expectation (piMass (predictionOriginalColumnMass X W A T))
          (fun z => predictionEliminationIntegrand M dir ∅ z v G Ω)) := by
    unfold expectation Finsupp.sum
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro z _
    ring
  rw [hcomm]
  simp_rw [predictionEliminationIntegrand_initial_translate]
  apply averaged_piMass_translation_expectation_bound
    (predictionOriginalColumnMass X W A T) (predictionSquareRootPairMass dir T)
    (fun v => predictionInsertedTranslation M dir (fun i => (v i).1))
    (fun z => ∏ base, G base (replicaCubeEval M base z))
    (predictionOriginalColumnMass_nonneg X W A T hZ)
    (predictionOriginalColumnMass_total X W A T hZ hT)
    (predictionSquareRootPairMass_nonneg dir T) (predictionSquareRootPairMass_total dir T hT)
    (pow_nonneg hB _)
  · intro z
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ _base : ReplicaCubeRow b d, B := Finset.prod_le_prod
        (fun _ _ => abs_nonneg _) (fun base _ => hG base _)
      _ = _ := by simp
  · intro v hv
    exact prediction_insertion_coordinate_errors X W A T M dir (fun i => (v i).1) R
      (fun q => (Nat.sqrt (T q) : ℝ)) hX hW hlog hT hM
      (fun _ => Nat.cast_nonneg _) (predictionSquareRootPairMass_first_bound dir T hv)
      (predictionSquareRootPairMass_root_bound M dir T R hR hv)

end Hindman168
