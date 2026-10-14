import Hindman168.PolynomialRowIntegerTranslations

/-!
# Actual mask rows and master coefficients yield integer W-translations

The master column coefficients are defined from the original rational
subset scales. Their positivity and absorption are derived. Thus every
actual generated row type has the paper's translations and exact response
identities on its original good-tuple event, with no direction or
integrality hypothesis in the application.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical

structure PolynomialRowFamily.IntegerTranslationConditions {n r m : ℕ}
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (master : MasterParameterFamily) (w : ℕ) (c : Fin (m + 1) → ℕ)
    (x : Fin n → ℕ) (target : Fin r) : Prop where
  modulus_pos : 0 < F.translationModulus master w x target
  translation_W : ∀ i k, (primorial w : ℤ) ∣ F.integerTranslation master w c x target i k
  root_W : ∀ k, (primorial w : ℤ) ∣ F.rootIntegerTranslation master w c x target k
  target_response : ∀ i, i ≠ target →
    F.normalizedLinearForm x c target (F.integerTranslation master w c x target i) =
      (F.translationModulus master w x target : ℚ)
  fixed_response : ∀ i, i ≠ target →
    F.normalizedLinearForm x c i (F.integerTranslation master w c x target i) = 0
  other_response : ∀ i, i ≠ target → ∀ l, l ≠ i →
    F.normalizedLinearForm x c l (F.integerTranslation master w c x target i) ≠ 0
  root_target_response : F.normalizedLinearForm x c target
    (F.rootIntegerTranslation master w c x target) = 0
  root_other_response : ∀ l, l ≠ target → F.normalizedLinearForm x c l
    (F.rootIntegerTranslation master w c x target) ≠ 0

theorem PolynomialRowFamily.integer_translation_conditions {n r m : ℕ}
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (master : MasterParameterFamily) (w : ℕ) (c : Fin (m + 1) → ℕ)
    (x : Fin n → ℕ) (target : Fin r) (hc : ∀ k, 0 < c k)
    (habs : ∀ k, (primorial w) ^ (master.exponent w + 1) * c k ∣ (master.modulus w : ℕ))
    (hg : predictionLocalPrimeGoodEvent master (F.catalog target) (F.denominator target) w x) :
    F.IntegerTranslationConditions master w c x target where
  modulus_pos := F.translationModulus_pos master w x target hg
  translation_W := fun i k => F.integerTranslation_W_divisible master w c x target i habs hg k
  root_W := fun k => F.rootIntegerTranslation_W_divisible master w c x target hc habs k
  target_response := fun i hi => (F.integerTranslation_responses master w c x target i hi hc habs hg).1
  fixed_response := fun i hi => (F.integerTranslation_responses master w c x target i hi hc habs hg).2.1
  other_response := fun i hi => (F.integerTranslation_responses master w c x target i hi hc habs hg).2.2
  root_target_response := (F.rootIntegerTranslation_responses master w c x target hc habs hg).1
  root_other_response := (F.rootIntegerTranslation_responses master w c x target hc habs hg).2

theorem maskGenerated_integer_translation_conditions (m : ℕ) {N : ℕ}
    (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ k, 0 < a k)
    (block : ℕ → Fin (m + 1) → Finset ℕ)
    (hblock : ∀ w k, block w k ⊆ Finset.range N)
    (hnonempty : ∀ w k, (block w k).Nonempty) :
    ∀ᶠ w in atTop, ∀ t : Fin (Fintype.card (LargeColumnSubset m)), ∀ x,
      predictionLocalPrimeGoodEvent (maskGeneratedMaster m gap)
        ((maskGeneratedRowDataFamily m gap t).rows.catalog (maskGeneratedRowDataFamily m gap t).target)
        ((maskGeneratedRowDataFamily m gap t).rows.denominator (maskGeneratedRowDataFamily m gap t).target) w x →
      (maskGeneratedRowDataFamily m gap t).rows.IntegerTranslationConditions
        (maskGeneratedMaster m gap) w (masterColumnCoefficient N a block w) x
        (maskGeneratedRowDataFamily m gap t).target := by
  have hA : ∀ q ∈ Finset.univ.image a, 0 < q := by
    intro q hq
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hq
    exact ha k
  have hF := maskGeneratedMaster_conditions m gap (Finset.univ.image a) hA
  have hcoeff := hF.column_coefficients a (fun k => Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
    block hblock hnonempty
  filter_upwards [hcoeff] with w hw
  intro t x hg
  exact (maskGeneratedRowDataFamily m gap t).rows.integer_translation_conditions
    (maskGeneratedMaster m gap) w (masterColumnCoefficient N a block w) x _
    (fun k => (hw k).1) (fun k => (hw k).2.2) hg

end Hindman168
