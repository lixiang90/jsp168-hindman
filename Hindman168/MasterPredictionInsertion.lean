import Hindman168.ConditionalPredictionInsertion

/-!
# Insertion under the actual master prime law

Both harmonic root growth and uniform quotient lower-length growth are
derived from master conditions. The prime law's positivity and mass one
are also proved properties, not input assumptions. The remaining explicit
application conditions concern actual replica moduli and original shift
support, not the desired insertion error.
-/

namespace Hindman168

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

theorem MasterParameterConditions.prediction_original_insertion_rapid
    {n N r b d h : ℕ} {A₀ : Finset ℚ}
    {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A₀ D F)
    (dir : Fin h → Fin b × CubeVertex d) (root : ℕ → Fin N)
    (gap : ℕ → Fin b → Fin N) (primeGap : ℕ → Fin r → ℕ) (k : Fin b → ℕ)
    (V : ℕ → ℕ) (hV : ∀ᶠ w in atTop, 1 ≤ V w)
    (hVroot : ∀ᶠ w in atTop, V w ≤ F.auxiliary w (root w).val)
    (hVgap : ∀ᶠ w in atTop, ∀ q, V w ≤ F.auxiliary w (gap w q).val)
    (hgap : ∀ᶠ w in atTop, ∀ q, (gap w q).val ≤ (root w).val)
    (E : ℕ → (Fin r → ℕ) → Prop)
    (A : ℕ → (Fin r → ℕ) → Fin b × Fin d × Bool → ℤ)
    (T : ℕ → (Fin r → ℕ) → Fin b → ℕ)
    (M : ℕ → (Fin r → ℕ) → Fin b → ℤ)
    (G Ω : ℕ → (Fin r → ℕ) → ReplicaCubeRow b d → ℤ → ℝ) (B : ℕ)
    (hT : ∀ᶠ w in atTop, ∀ x ∈ (masterPrimeSlotsMass F w (primeGap w)).support,
      E w x → ∀ q, masterShiftLengthLowerBound F w (gap w q).val (k q) ≤ T w x q)
    (hM : ∀ᶠ w in atTop, ∀ x ∈ (masterPrimeSlotsMass F w (primeGap w)).support,
      E w x → ∀ q, (primorial w : ℤ) ∣ M w x q)
    (hR : ∀ᶠ w in atTop, ∀ x ∈ (masterPrimeSlotsMass F w (primeGap w)).support,
      E w x → ∀ q, |(M w x q : ℝ)| * T w x q ≤ F.gap w (gap w q).val)
    (hG : ∀ᶠ w in atTop, ∀ x ∈ (masterPrimeSlotsMass F w (primeGap w)).support,
      E w x → ∀ base y, |G w x base y| ≤ (V w : ℝ) ^ B) :
    RapidlySmall atTop (fun w => (V w : ℝ)) (fun w =>
      expectation (masterPrimeSlotsMass F w (primeGap w)) (fun x => if E w x then
        expectation (piMass (predictionOriginalColumnMass (F.cutoff w (root w).val)
          (primorial w) (A w x) (T w x)))
          (fun z => expectation (predictionSquareRootPairMass dir (T w x))
            (fun v => predictionEliminationIntegrand (M w x) dir ∅ z v (G w x) (Ω w x))) else 0) -
      expectation (masterPrimeSlotsMass F w (primeGap w)) (fun x => if E w x then
        expectation (piMass (predictionOriginalColumnMass (F.cutoff w (root w).val)
          (primorial w) (A w x) (T w x)))
          (fun z => ∏ base, G w x base (replicaCubeEval (M w x) base z)) else 0)) := by
  have hroot := hF.root_gap_sampling_growth root
    (∑ i, (cubeRootDirection (dir i).2.val).natAbs) hVroot
    (H := fun w => predictionRootDisplacementCap dir (fun q => F.gap w (gap w q).val))
    (hgap.mono (fun w hw => predictionRootDisplacementCap_le_common_gap dir _ _
      (fun q => hF.gap_monotone w (hw q))))
  have hshift (q : Fin b) : PowerDominates atTop
      (fun w => (masterShiftLengthLowerBound F w (gap w q).val (k q) : ℝ))
      (fun w => (V w : ℝ)) := by
    apply (hF.quotient_shift_growth (fun w => gap w q) (k q)).mono_base 1
    filter_upwards [hVgap] with w hw
    simp only [pow_one]
    refine ⟨Nat.cast_nonneg _, by positivity, ?_⟩
    have hh : (V w : ℝ) ≤ F.auxiliary w (gap w q).val := by exact_mod_cast hw q
    linarith [(Nat.cast_nonneg (F.pool w (gap w q).val).upper :
      (0 : ℝ) ≤ (F.pool w (gap w q).val).upper)]
  exact conditional_square_root_insertion_rapid dir
    (fun w => masterPrimeSlotsMass F w (primeGap w)) E A T M G Ω B
    (fun w => hF.prime_slots_nonneg w (primeGap w))
    (fun w => hF.prime_slots_total w (primeGap w)) hV
    (Eventually.of_forall primorial_pos) hroot hshift hT hM hR hG

end Hindman168
