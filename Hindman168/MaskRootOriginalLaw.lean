import Hindman168.MaskRootOriginalMajorants
import Hindman168.RootSmoothedSamplingLaw

/-! Exact concrete enlarged sampling, using unchanged actual pivot laws,
original quotient direction pairs and two independent uniform root samples.
Every reindexed coefficient evaluates to the actual root-translated form. -/

set_option maxHeartbeats 2000000

namespace Hindman168.MaskRootOriginalSampling

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m))) (J : ℕ) (hJ : 0 < J)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)

local notation "S" => maskRootOriginalSampling m gap a ha C hC t J hJ hgap

noncomputable def directionPairMass (w : ℕ)
    (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) :
    Mass (MaskOriginalDirection m gap t → ℤ × ℤ) :=
  piMass (fun _ => tensor
    (uniformIntervalMass 0 (maskGeneratedShiftLength m gap t J w x))
    (uniformIntervalMass 0 (maskGeneratedShiftLength m gap t J w x)))

theorem component_mass_eq (w : ℕ)
    (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) :
    (S).baseMass w x = piMass (fun j => rootSmoothedComponentMass
      (fun col : Fin (m + 1) => integerMass ((maskGeneratedMaster m gap).cutoff w ((C w).pivot col)) (primorial w))
      (fun _k : MaskOriginalDirection m gap t => uniformIntervalMass 0 (maskGeneratedShiftLength m gap t J w x))
      (MaskOriginalSampling.rootMass (m := m) gap w) (maskRootColumnDecode m gap t j)) := by
  change piMass (fun j : MaskRootCopiedIndex m gap t =>
    if j ∈ maskRootHarmonic m gap t then
      integerMass ((maskGeneratedMaster m gap).cutoff w (maskRootIndex m gap C hC t w j).val) (primorial w)
    else uniformIntervalMass 0 (maskRootLength m gap t J w x j)) =
    piMass (fun j : MaskRootCopiedIndex m gap t => rootSmoothedComponentMass
      (fun col : Fin (m + 1) => integerMass ((maskGeneratedMaster m gap).cutoff w ((C w).pivot col)) (primorial w))
      (fun _k : MaskOriginalDirection m gap t => uniformIntervalMass 0 (maskGeneratedShiftLength m gap t J w x))
      (MaskOriginalSampling.rootMass (m := m) gap w) (maskRootColumnDecode m gap t j))
  apply congrArg piMass
  funext j
  cases hd : maskRootColumnDecode m gap t j with
  | inl col =>
    cases col with
    | inl col =>
      simp only [maskRootHarmonic, Finset.mem_filter, Finset.mem_univ, hd, true_and, if_true,
        maskRootIndex, rootSmoothedComponentMass, additiveComponentMass, Sum.elim_inl]
    | inr kb =>
      simp only [maskRootHarmonic, Finset.mem_filter, Finset.mem_univ, hd, true_and, if_false,
        maskRootLength, rootSmoothedComponentMass, additiveComponentMass, Sum.elim_inl, Sum.elim_inr]
  | inr bit =>
    simp only [maskRootHarmonic, Finset.mem_filter, Finset.mem_univ, hd, true_and, if_false,
      maskRootLength, rootSmoothedComponentMass, Sum.elim_inr, MaskOriginalSampling.rootMass]

theorem sampling_law (w : ℕ)
    (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ)
    (f : (MaskRootCopiedIndex m gap t → ℤ) → ℝ) :
    expectation ((S).baseMass w x) f =
      expectation (maskOriginalBaseMass m gap C w) (fun z =>
        expectation (directionPairMass gap t J w x) (fun v =>
          expectation (MaskOriginalSampling.rootMass (m := m) gap w) (fun u₀ =>
            expectation (MaskOriginalSampling.rootMass (m := m) gap w)
              (fun u₁ => f (rootSmoothedSampleCoordinates z v (u₀, u₁)))))) := by
  rw [component_mass_eq gap a ha C hC t J hJ hgap w x]
  exact rootSmoothedSampleCoordinates_law _ _ _ f

include ha hC in
theorem coefficient_eval_eventually :
    ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ z v u,
      ∀ r : MaskRootCopiedRow m gap t,
        (∑ j, maskRootCopiedCoefficient m gap a C t w x r j * rootSmoothedSampleCoordinates z v u j) =
          (MaskOriginalSampling.additiveData gap a C t w x).translatedForm r.val.1.val.1 r.val.1.val.2
            (fun col => z col + MaskOriginalSampling.rootShift gap a C t w x
              (rootPairValues u r.val.2) col) (predictionPairValues v) := by
  filter_upwards [MaskOriginalSampling.additiveData_eventually_certificate gap a ha C hC t] with w hw
  intro x hx z v u r
  obtain ⟨H, hD⟩ := hw x hx
  have he := rootSmoothedSampleCoordinates_eval H.data
    ((maskGeneratedRowDataFamily m gap t).rows.rootIntegerTranslation (maskGeneratedMaster m gap) w
      (masterColumnCoefficient N a (fun w => (C w).block) w) x
      (maskGeneratedRowDataFamily m gap t).target) r z v u
  rw [hD]
  refine Eq.trans ?_ he
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun q : ℤ => q * rootSmoothedSampleCoordinates z v u j)
    (H.rootSmoothedFinCoefficient_eq r j).symm

end Hindman168.MaskRootOriginalSampling
