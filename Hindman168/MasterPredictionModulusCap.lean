import Hindman168.PredictionQuotientLengths
import Hindman168.MasterCyclicShortLengths

namespace Hindman168
open Filter
open scoped Topology Classical

theorem masterPredictionModulus_cap {N r b L : ℕ} (F : MasterParameterFamily)
    (gap : ℕ → Fin b → Fin N) (primeGap : ℕ → Fin r → Fin L)
    (J : ℕ) (s : ℕ → Fin b → ℕ) (f : Fin b → MvPolynomial (Fin r) ℤ)
    (hs : ∀ᶠ w in atTop, ∀ q, s w q ∣ (F.modulus w : ℕ))
    (hslots : ∀ᶠ w in atTop, ∀ q j, j ∈ (f q).vars →
      (primeGap w j).val = (gap w q).val) :
    ∀ᶠ w in atTop, ∀ x ∈ (masterPrimeSlotsMass F w (fun j => primeGap w j)).support,
      ∀ q, J * (predictionCubeModulus w (s w q) (f q) x).natAbs ≤
        ((F.pool w (gap w q).val).upper + F.auxiliary w (gap w q).val) ^
          (J + integerPolynomialCoeffSize (f q) + (f q).totalDegree + 1) := by
  filter_upwards [hs, hslots] with w hsw hslot
  intro x hx q
  apply predictionCubeModulus_polynomial_cap
  · have ha := F.auxiliary_ge_two w (gap w q).val
    omega
  · exact (Nat.le_of_dvd (F.modulus w).pos (hsw q)).trans
      ((F.modulus_le_auxiliary _ _).trans (Nat.le_add_left _ _))
  · intro j hj
    have hv := masterPrimeSlotsMass_support F w (fun j => primeGap w j) hx j
    rw [hslot q j hj] at hv
    omega

theorem MasterParameterConditions.prediction_short_lengths_uniform
    {n N r b L : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A D F)
    (gap : ℕ → Fin b → Fin N) (primeGap : ℕ → Fin r → Fin L)
    (J : ℕ) (hJ : 0 < J) (s : ℕ → Fin b → ℕ) (f : Fin b → MvPolynomial (Fin r) ℤ)
    (hs : ∀ᶠ w in atTop, ∀ q, s w q ∣ (F.modulus w : ℕ))
    (hslots : ∀ᶠ w in atTop, ∀ q j, j ∈ (f q).vars →
      (primeGap w j).val = (gap w q).val) (B : ℕ) :
    ∀ᶠ w in atTop, ∀ x ∈ (masterPrimeSlotsMass F w (fun j => primeGap w j)).support,
      ∀ q, MvPolynomial.eval (fun j => (x j : ℤ)) (f q) ≠ 0 →
        B ≤ predictionQuotientLength F gap J s f w x q := by
  have hlen : ∀ᶠ w in atTop, ∀ q : Fin b, ∀ P : ℕ, 0 < P →
      J * P ≤ ((F.pool w (gap w q).val).upper + F.auxiliary w (gap w q).val) ^
        (J + integerPolynomialCoeffSize (f q) + (f q).totalDegree + 1) →
      B ≤ F.gap w (gap w q).val / (J * P) := by
    apply eventually_all.mpr
    intro q
    exact hF.capped_short_lengths_eventually (fun w => gap w q) J
      (J + integerPolynomialCoeffSize (f q) + (f q).totalDegree + 1) B hJ
  filter_upwards [hlen, masterPredictionModulus_cap F gap primeGap J s f hs hslots, hs]
    with w hlenw hcap hsw
  intro x hx q hz
  exact hlenw q _ (Int.natAbs_pos.mpr (predictionCubeModulus_nonzero w (s w q) (f q) x
    (Nat.pos_of_dvd_of_pos (hsw q) (F.modulus w).pos) hz)) (hcap x hx q)

end Hindman168

