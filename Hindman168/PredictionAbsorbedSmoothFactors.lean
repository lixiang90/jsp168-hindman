import Hindman168.MasterPredictionQuotientCubeLimit

/-!
# Actual coefficient absorption supplies W-multiple replica smooth factors

For a master coefficient c, W^(e0+1)c divides M. Hence the actual natural
quotient s=M/c is positive, divides M, and is a multiple of W. Mere smoothness
s|W^e would not justify the root harmonic translations.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical

theorem absorbed_modulus_quotient_conditions (W M c e : ℕ)
    (hM : 0 < M) (hc : 0 < c) (habs : W ^ (e + 1) * c ∣ M) :
    0 < M / c ∧ M / c ∣ M ∧ W ∣ M / c := by
  have hcdiv : c ∣ M := (dvd_mul_left c (W ^ (e + 1))).trans habs
  have hcm := Nat.mul_div_cancel' hcdiv
  have hp : 0 < M / c := Nat.div_pos (Nat.le_of_dvd hM hcdiv) hc
  have hqdiv : M / c ∣ M := ⟨c, by simpa only [mul_comm] using hcm.symm⟩
  obtain ⟨d, hd⟩ := habs
  have heq : M = c * (W ^ (e + 1) * d) := by rw [hd]; ring
  have hquot : M / c = W ^ (e + 1) * d := by rw [heq, Nat.mul_div_cancel_left _ hc]
  have hW : W ∣ W ^ (e + 1) := ⟨W ^ e, by rw [pow_succ]; ring⟩
  exact ⟨hp, hqdiv, hquot ▸ (hW.trans (dvd_mul_right _ _))⟩

noncomputable def predictionCoefficientSmoothFactor {b : ℕ}
    (F : MasterParameterFamily) (c : ℕ → Fin b → ℕ) (w : ℕ) (q : Fin b) : ℕ :=
  (F.modulus w : ℕ) / c w q

theorem MasterParameterConditions.prediction_coefficient_smooth_factors
    {n N b : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A D F)
    (a : Fin b → ℚ) (ha : ∀ q, a q ∈ A)
    (block : ℕ → Fin b → Finset ℕ)
    (hblock : ∀ w q, block w q ⊆ Finset.range N)
    (hnonempty : ∀ w q, (block w q).Nonempty)
    (c : ℕ → Fin b → ℕ)
    (hc : ∀ᶠ w in atTop, ∀ q,
      (masterScale (primorial w) w N (block w q) : ℚ) * a q = (c w q : ℚ)) :
    ∀ᶠ w in atTop, ∀ q,
      0 < predictionCoefficientSmoothFactor F c w q ∧
      predictionCoefficientSmoothFactor F c w q ∣ (F.modulus w : ℕ) ∧
      primorial w ∣ predictionCoefficientSmoothFactor F c w q := by
  filter_upwards [hF.coefficients, hc] with w hw hcw
  intro q
  obtain ⟨c', hc', heq, habs⟩ := hw (a q) (ha q) (block w q) (hblock w q) (hnonempty w q)
  have he : c' = c w q := by exact_mod_cast heq.symm.trans (hcw q)
  subst c'
  exact absorbed_modulus_quotient_conditions (primorial w) (F.modulus w) (c w q)
    (F.exponent w) (F.modulus w).property hc' habs

end Hindman168
