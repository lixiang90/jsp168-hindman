import Hindman168.MaskGeneratedNormalizedIntegerRows
import Hindman168.MaskGeneratedIntegerResponseUnits
import Hindman168.MaskGeneratedUniformDirectionBounds

/-!
The paper's row-direction lemma on the actual mask family and master chain.
Coordinates, integer row responses, the exception catalogue and one size
exponent are derived; the analytic removal/correlation estimate is separate.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical

structure PolynomialRowFamily.IntegerRowDirectionConditions {n r m : ℕ}
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (master : MasterParameterFamily) (w : ℕ) (c : Fin (m + 1) → ℕ)
    (x : Fin n → ℕ) (target : Fin r) (V B K : ℕ) : Prop where
  rows : F.NormalizedIntegerRowConditions x c (primorial w)
  modulus_pos : 0 < F.translationModulus master w x target
  translation_W : ∀ i k, (primorial w : ℤ) ∣ F.integerTranslation master w c x target i k
  root_W : ∀ k, (primorial w : ℤ) ∣ F.rootIntegerTranslation master w c x target k
  target_response : ∀ i, i ≠ target →
    F.normalizedIntegerLinearForm x c target (F.integerTranslation master w c x target i) =
      (F.translationModulus master w x target : ℤ)
  fixed_response : ∀ i, i ≠ target →
    F.normalizedIntegerLinearForm x c i (F.integerTranslation master w c x target i) = 0
  other_response : ∀ i, i ≠ target → ∀ l, l ≠ i →
    F.normalizedIntegerLinearForm x c l (F.integerTranslation master w c x target i) ≠ 0
  root_target_response : F.normalizedIntegerLinearForm x c target
    (F.rootIntegerTranslation master w c x target) = 0
  root_other_response : ∀ l, l ≠ target → F.normalizedIntegerLinearForm x c l
    (F.rootIntegerTranslation master w c x target) ≠ 0
  rough_units : ∀ p : ℕ, p.Prime → w < p →
    (∀ f ∈ F.catalog target,
      MvPolynomial.eval₂ (Int.castRingHom (ZMod p)) (fun j => (x j : ZMod p)) f ≠ 0) →
    (∀ i, i ≠ target → ∀ l, l ≠ i →
      IsUnit (F.normalizedIntegerLinearForm x c l (F.integerTranslation master w c x target i) : ZMod p)) ∧
    (∀ l, l ≠ target →
      IsUnit (F.normalizedIntegerLinearForm x c l (F.rootIntegerTranslation master w c x target) : ZMod p))
  anchor_units : ∀ l q, 0 < q → q ≤ V →
    IsUnit (F.normalizedIntegerRow x c l (F.normalizationAnchor l) : ZMod q)
  size_bounds : ∀ i k, (F.integerTranslation master w c x target i k).natAbs ≤ B ^ K ∧
    (F.rootIntegerTranslation master w c x target k).natAbs ≤ B ^ K

theorem PolynomialRowFamily.NormalizedIntegerRowConditions.translation_response_eq {n r m : ℕ}
    {F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m}
    {x : Fin n → ℕ} {c : Fin (m + 1) → ℕ} {W : ℕ}
    (hrows : F.NormalizedIntegerRowConditions x c W)
    (master : MasterParameterFamily) (w : ℕ) (target i l : Fin r) (hi : i ≠ target)
    (hc : ∀ k, 0 < c k)
    (habs : ∀ k, (primorial w) ^ (master.exponent w + 1) * c k ∣ (master.modulus w : ℕ))
    (hg : predictionLocalPrimeGoodEvent master (F.catalog target) (F.denominator target) w x) :
    F.normalizedIntegerLinearForm x c l (F.integerTranslation master w c x target i) =
      F.integerTranslationResponse master w c x target i l := by
  have he := (hrows.form_cast l _).trans
    (F.integerTranslationResponse_cast master w c x target i l hi hc habs hg).symm
  exact_mod_cast he

theorem PolynomialRowFamily.NormalizedIntegerRowConditions.root_response_eq {n r m : ℕ}
    {F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m}
    {x : Fin n → ℕ} {c : Fin (m + 1) → ℕ} {W : ℕ}
    (hrows : F.NormalizedIntegerRowConditions x c W)
    (master : MasterParameterFamily) (w : ℕ) (target l : Fin r)
    (hc : ∀ k, 0 < c k)
    (habs : ∀ k, (primorial w) ^ (master.exponent w + 1) * c k ∣ (master.modulus w : ℕ)) :
    F.normalizedIntegerLinearForm x c l (F.rootIntegerTranslation master w c x target) =
      F.rootIntegerTranslationResponse master w c x target l := by
  have he := (hrows.form_cast l _).trans
    (F.rootIntegerTranslationResponse_cast master w c x target l hc habs).symm
  exact_mod_cast he

theorem maskGenerated_chain_integer_row_directions (m : ℕ) {N : ℕ}
    (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ k, 0 < a k)
    (C : ℕ → Chain (m + 1)) (hC : ∀ w k, (C w).block k ⊆ Finset.range N) :
    ∀ᶠ w in atTop, ∀ t : Fin (Fintype.card (LargeColumnSubset m)),
      ∀ x ∈ (primeIndependentMass (maskGeneratedRowDataFamily m gap t).arity
        ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper).support,
      predictionLocalPrimeGoodEvent (maskGeneratedMaster m gap)
        ((maskGeneratedRowDataFamily m gap t).rows.catalog (maskGeneratedRowDataFamily m gap t).target)
        ((maskGeneratedRowDataFamily m gap t).rows.denominator (maskGeneratedRowDataFamily m gap t).target) w x →
      (maskGeneratedRowDataFamily m gap t).rows.IntegerRowDirectionConditions
        (maskGeneratedMaster m gap) w (masterColumnCoefficient N a (fun w => (C w).block) w) x
        (maskGeneratedRowDataFamily m gap t).target
        ((maskGeneratedMaster m gap).auxiliary w (gap w).val)
        (((maskGeneratedMaster m gap).pool w (gap w).val).upper +
          (maskGeneratedMaster m gap).auxiliary w (gap w).val) (maskRowDirectionSizeExponent m) := by
  have hA : ∀ q ∈ Finset.univ.image a, 0 < q := by
    intro q hq
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hq
    exact ha k
  have hF := maskGeneratedMaster_conditions m gap (Finset.univ.image a) hA
  have hcoeff := hF.column_coefficients a
    (fun k => Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
    (fun w => (C w).block) hC (fun w k => (C w).block_nonempty k)
  filter_upwards [hcoeff, maskGenerated_chain_integer_row_conditions m gap a ha C hC,
    maskGenerated_integer_translation_conditions m gap a ha (fun w => (C w).block) hC
      (fun w k => (C w).block_nonempty k),
    maskGenerated_integer_response_unit_conditions m gap a ha (fun w => (C w).block) hC
      (fun w k => (C w).block_nonempty k),
    maskGenerated_chain_integer_anchor_units m gap a ha C hC,
    maskGenerated_uniform_integer_translation_size_bounds m gap a ha (fun w => (C w).block) hC
      (fun w k => (C w).block_nonempty k)] with w hc hr ht hu haunit hs
  intro t x hx hg
  let F := (maskGeneratedRowDataFamily m gap t).rows
  let target := (maskGeneratedRowDataFamily m gap t).target
  let c := masterColumnCoefficient N a (fun w => (C w).block) w
  have hrows := hr t x
  have htrans := ht t x hg
  have hunits := hu t x hg
  have hpos : ∀ k, 0 < c k := fun k => (hc k).1
  have habs : ∀ k, (primorial w) ^ ((maskGeneratedMaster m gap).exponent w + 1) * c k ∣
      ((maskGeneratedMaster m gap).modulus w : ℕ) := fun k => (hc k).2.2
  have heq := fun i hi l => hrows.translation_response_eq (maskGeneratedMaster m gap) w
    target i l hi hpos habs hg
  have hroot := fun l => hrows.root_response_eq (maskGeneratedMaster m gap) w target l hpos habs
  refine {
    rows := hrows
    modulus_pos := htrans.modulus_pos
    translation_W := htrans.translation_W
    root_W := htrans.root_W
    target_response := ?_
    fixed_response := ?_
    other_response := ?_
    root_target_response := ?_
    root_other_response := ?_
    rough_units := ?_
    anchor_units := ?_
    size_bounds := hs t x hx }
  · intro i hi
    have h := (F.integerTranslationResponse_responses (maskGeneratedMaster m gap) w c x
      target i hi hpos habs hg).1
    exact (heq i hi target).trans h
  · intro i hi
    exact (heq i hi i).trans (F.integerTranslationResponse_responses
      (maskGeneratedMaster m gap) w c x target i hi hpos habs hg).2.1
  · intro i hi l hl
    rw [heq i hi l]
    exact (F.integerTranslationResponse_responses
      (maskGeneratedMaster m gap) w c x target i hi hpos habs hg).2.2 l hl
  · exact (hroot target).trans (F.rootIntegerTranslationResponse_responses
      (maskGeneratedMaster m gap) w c x target hpos habs hg).1
  · intro l hl
    rw [hroot l]
    exact (F.rootIntegerTranslationResponse_responses
      (maskGeneratedMaster m gap) w c x target hpos habs hg).2 l hl
  · intro p hp hwp havoid
    have hu := hunits.rough_units p hp hwp havoid
    refine ⟨?_, ?_⟩
    · intro i hi l hl
      rw [heq i hi l]
      exact hu.1 i hi l hl
    · intro l hl
      rw [hroot l]
      exact hu.2 l hl
  · intro l q hq hcap
    exact haunit t x hx l q hq hcap

end Hindman168
