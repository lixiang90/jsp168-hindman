import Hindman168.MaskInputSubstitution
import Hindman168.MaskRemovalOffDiagonalAbsorption

/-! Absorb the actual normalized double test, including its single
outer density. All three factors have the same derived m-only exponent;
the old tuple stays shared and the absorbed diagonal is nonnegative. -/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass MaskOriginalSampling

variable {m N : ℕ} (S : Finset (Fin (m + 1))) (hS : 2 ≤ S.card)
  (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (C : ℕ → Chain (m + 1))

noncomputable def maskStageNormalizedDoubleTest {k w : ℕ}
    {T : Finset (Finset (Fin (m + 1)))}
    (D : MaskStageCorrelationInput S hS gap C k w T) (U : Finset (Fin (m + 1)))
    (r : MaskStagePoint S hS k) (pq : ℕ × ℕ) : ℝ :=
  maskStageDensity S hS gap a C k U w r *
    maskStageNormalizedInputTest S hS gap a C D U
      (r.1, (chosenMaskColumnPlan S U hS).coordinates pq.1 r.2) *
    maskStageNormalizedInputTest S hS gap a C D U
      (r.1, (chosenMaskColumnPlan S U hS).coordinates pq.2 r.2)

variable (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)
  (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)

include hC htail in
theorem maskStageNormalizedDoubleTest_eventually_bound :
    ∀ᶠ w in atTop, ∀ k T (D : MaskStageCorrelationInput S hS gap C k w T) U,
      ∀ x ∈ (monomialRowPrimeMass m gap (maskPrefixRowStage S hS k).primeArity w).support, ∀ z pq,
      |maskStageNormalizedDoubleTest S hS gap a C D U (x,z) pq| ≤
        ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ (6 * maskRowCountBound m) := by
  filter_upwards [maskStageDensity_eventually_nonneg S hS gap a C hC,
    maskStageDensity_eventually_polynomial_cap S hS gap a C hC htail,
    maskStageNormalizedInputTest_eventually_bound S hS gap a C hC htail] with w hn hd hH
  intro k T D U x hx z pq
  unfold maskStageNormalizedDoubleTest
  rw [abs_mul, abs_mul, abs_of_nonneg (hn k U (x,z))]
  calc
    _ ≤ (((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ (2 * maskRowCountBound m)) *
        (((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ (2 * maskRowCountBound m)) *
        (((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ (2 * maskRowCountBound m)) :=
      mul_le_mul (mul_le_mul (hd k U (x,z)) (hH k T D U x hx _) (abs_nonneg _) (by positivity))
        (hH k T D U x hx _) (abs_nonneg _) (by positivity)
    _ = _ := by rw [← pow_add, ← pow_add]; congr 1; omega

theorem maskStageNormalizedDoubleTest_outside {k w : ℕ} {T : Finset (Finset (Fin (m + 1)))}
    (D : MaskStageCorrelationInput S hS gap C k w T) (U : Finset (Fin (m + 1)))
    (u : Fin (m + 1)) (hu : u ∈ S) (hU : u ∉ U)
    (hP : chosenMaskColumnPlan S U hS = .outside u hu hU) (r : MaskStagePoint S hS k) (pq : ℕ × ℕ) :
    maskStageNormalizedDoubleTest S hS gap a C D U r pq =
      maskStageAbsorbedDoubleTest S hS gap a C k U w
        (maskStageNormalizedInputTest S hS gap a C D U) r pq := by
  unfold maskStageNormalizedDoubleTest maskStageAbsorbedDoubleTest
  rw [hP]
  rfl

theorem maskStageNormalizedDoubleTest_balancedAbsorption_identity (k : ℕ)
    (U : Finset (Fin (m + 1))) (u v : Fin (m + 1)) (hu : u ∈ S) (hv : v ∈ S)
    (huU : u ∈ U) (hvU : v ∈ U) (hne : u ≠ v)
    (hP : chosenMaskColumnPlan S U hS = .balanced u v hu hv huU hvU hne)
    (w : ℕ) (T : Finset (Finset (Fin (m + 1))))
    (D : MaskStageCorrelationInput S hS gap C k w T) :
    maskStageFreshOffDiagonalAverage S hS gap C k w (fun r pq =>
      maskStageNormalizedDoubleTest S hS gap a C D U
        (r.1, Function.update r.2 u (((pq.1*pq.2 : ℕ) : ℤ) * r.2 u)) pq) =
    maskStageFreshOffDiagonalAverage S hS gap C k w
      (maskStageAbsorbedDoubleTest S hS gap a C k U w
        (maskStageNormalizedInputTest S hS gap a C D U)) := by
  unfold maskStageFreshOffDiagonalAverage maskStageFreshPairAverage
  apply congrArg (expectation _)
  funext r
  apply expectation_congr_support
  intro pq hpq
  have hs := Finset.mem_product.mp (tensor_support _ _ hpq)
  have hp := (primePool_mem.mp (primePoolMass_support _ _ hs.1)).2.2.ne_zero
  have hq := (primePool_mem.mp (primePoolMass_support _ _ hs.2)).2.2.ne_zero
  by_cases he : pq.1 ≠ pq.2
  · simp only [if_pos he]
    unfold maskStageNormalizedDoubleTest maskStageAbsorbedDoubleTest
    rw [hP]
    dsimp only [MaskColumnPlan.coordinates, MaskColumnPlan.absorptionCoordinates,
      MaskColumnPlan.absorbedCoordinates]
    rw [maskBalancedCoordinates_pair_dilation u v hne hp,
      maskBalancedCoordinates_pair_dilation_swapped u v hne pq.1 hq]
  · simp only [if_neg he]

include hC hgap htail in
theorem maskStageNormalizedDoubleTest_eventually_absorption_bound (k : ℕ)
    (U : Finset (Fin (m + 1))) (u v : Fin (m + 1)) (hu : u ∈ S) (hv : v ∈ S)
    (huU : u ∈ U) (hvU : v ∈ U) (hne : u ≠ v)
    (hP : chosenMaskColumnPlan S U hS = .balanced u v hu hv huU hvU hne) :
    ∀ᶠ w in atTop, ∀ T (D : MaskStageCorrelationInput S hS gap C k w T),
      |maskStageFreshOffDiagonalAverage S hS gap C k w (fun r pq =>
          primeDivisorEta pq.1 (r.2 u) * primeDivisorEta pq.2 (r.2 u) *
            maskStageNormalizedDoubleTest S hS gap a C D U r pq) -
        maskStageFreshOffDiagonalAverage S hS gap C k w
          (maskStageAbsorbedDoubleTest S hS gap a C k U w
            (maskStageNormalizedInputTest S hS gap a C D U))| ≤
      |((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ (6 * maskRowCountBound m) *
        masterPrimePairDilationErrorCap (maskGeneratedMaster m gap) gap (maskOriginalPivotIndex C hC u) w| := by
  filter_upwards [maskStageNormalizedDoubleTest_eventually_bound S hS gap a C hC htail,
    maskStageOffDiagonalAbsorption_bound S hS gap C hC hgap k u (6 * maskRowCountBound m)] with w hH hb
  intro T D
  have he := hb (maskStageNormalizedDoubleTest S hS gap a C D U)
    (fun x hx pq _ z => hH k T D U x hx z pq)
  rw [maskStageNormalizedDoubleTest_balancedAbsorption_identity S hS gap a C k U u v hu hv huU hvU hne hP] at he
  exact he

include hC htail in
theorem maskStageNextInputCorrelation_eventually_absorbed :
    ∀ᶠ w in atTop, ∀ k T (D : MaskStageCorrelationInput S hS gap C k w T) U,
      maskStageNextInputCorrelation S hS gap a C D U =
      maskStageFreshPairAverage S hS gap C k w
        (maskStageAbsorbedDoubleTest S hS gap a C k U w
          (maskStageNormalizedInputTest S hS gap a C D U)) := by
  filter_upwards [maskRowMaskCorrelation_eventually_absorbedUpdate gap C S hS a hC htail] with w hw
  intro k T D U
  exact hw k U (T.erase U) D.masks D.rows

include hC htail in
theorem maskStageNextInputCorrelation_eventually_dominates_offDiagonal :
    ∀ᶠ w in atTop, ∀ k T (D : MaskStageCorrelationInput S hS gap C k w T) U,
      maskStageFreshOffDiagonalAverage S hS gap C k w
        (maskStageAbsorbedDoubleTest S hS gap a C k U w
          (maskStageNormalizedInputTest S hS gap a C D U)) ≤
      maskStageNextInputCorrelation S hS gap a C D U := by
  filter_upwards [maskStageNextInputCorrelation_eventually_absorbed S hS gap a C hC htail,
    maskStageAbsorbedOffDiagonal_eventually_le_full S hS gap a C hC] with w he hl
  intro k T D U
  rw [he k T D U]
  exact hl k U _

end Hindman168
