import Hindman168.RenamedPrimeShortCubeLaw
import Hindman168.MaskEndpointShortCubeConditioning

/-! The mask-generated local prime slots have the full master arity.
Their concrete slot injection is a bijection, so the original weak
prime-good short-cube means are exactly the renamed master means. -/

namespace Hindman168
open FiniteMass MaskOriginalSampling
open scoped Classical

theorem maskGeneratedRowDataFamily_arity (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) :
    (maskGeneratedRowDataFamily m gap t).arity = maskMasterArity m := by
  unfold maskGeneratedRowDataFamily maskGeneratedRowData maskMasterArity
  exact fullMaskRowStage_primeArity _ _

theorem maskGeneratedSlot_eq_finCongr (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) :
    (maskGeneratedRowDataFamily m gap t).slot =
      (finCongr (maskGeneratedRowDataFamily_arity m gap t)) := by
  rfl

theorem maskRenamedLocalCatalog_nonzero (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) :
    ∀ pol ∈ ((maskGeneratedRowDataFamily m gap t).rows.catalog
      (maskGeneratedRowDataFamily m gap t).target).image
        (MvPolynomial.rename (maskGeneratedRowDataFamily m gap t).slot), pol ≠ 0 := by
  intro pol hpol
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hpol
  exact originalRowMasterCatalog_nonzero (maskGeneratedRowDataFamily m gap) _
    (originalRowMasterCatalog_inclusion (maskGeneratedRowDataFamily m gap) t p hp)

theorem maskLocal_primeGood_shortCube_eq_renamed (m : ℕ) {N : ℕ}
    (gap : ℕ → Fin N) (t : Fin (Fintype.card (LargeColumnSubset m)))
    (w X d J : ℕ) (g : ℤ → ℝ) :
    expectation (conditionMass
      (primeIndependentMass (maskGeneratedRowDataFamily m gap t).arity
        ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper)
      (primeSampleGood ((maskGeneratedRowDataFamily m gap t).rows.catalog
        (maskGeneratedRowDataFamily m gap t).target))) (fun x =>
      |integerPredictionShortCubeStatistic w ((maskGeneratedMaster m gap).modulus w : ℕ)
        ((maskGeneratedMaster m gap).gap w (gap w).val) X d J
        (targetPredictionPolynomial gap t) g x|) =
      expectation (conditionMass
        (primeIndependentMass (maskMasterArity m)
          ((maskGeneratedMaster m gap).pool w (gap w).val).lower
          ((maskGeneratedMaster m gap).pool w (gap w).val).upper)
        (primeSampleGood (((maskGeneratedRowDataFamily m gap t).rows.catalog
          (maskGeneratedRowDataFamily m gap t).target).image
            (MvPolynomial.rename (maskGeneratedRowDataFamily m gap t).slot)))) (fun x =>
        |integerPredictionShortCubeStatistic w ((maskGeneratedMaster m gap).modulus w : ℕ)
          ((maskGeneratedMaster m gap).gap w (gap w).val) X d J
          (MvPolynomial.rename (maskGeneratedRowDataFamily m gap t).slot
            (targetPredictionPolynomial gap t)) g x|) := by
  rw [maskGeneratedSlot_eq_finCongr]
  exact (renamed_primeGood_shortCube_expectation
    (finCongr (maskGeneratedRowDataFamily_arity m gap t)) _ _ _ _ _ _ _ _ _ _ _).symm

end Hindman168
