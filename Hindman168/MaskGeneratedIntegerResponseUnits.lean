import Hindman168.PolynomialIntegerTranslationResponses

/-!
The fixed, nonzero polynomial catalogue is the exact exception list.
All actual integer responses are units at every rough prime outside it.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical

structure PolynomialRowFamily.IntegerResponseUnitConditions {n r m : ℕ}
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (master : MasterParameterFamily) (w : ℕ) (c : Fin (m + 1) → ℕ)
    (x : Fin n → ℕ) (target : Fin r) : Prop where
  rough_units : ∀ p : ℕ, p.Prime → w < p →
    (∀ f ∈ F.catalog target,
      MvPolynomial.eval₂ (Int.castRingHom (ZMod p)) (fun j => (x j : ZMod p)) f ≠ 0) →
    (∀ i, i ≠ target → ∀ l, l ≠ i →
      IsUnit (F.integerTranslationResponse master w c x target i l : ZMod p)) ∧
    (∀ l, l ≠ target → IsUnit (F.rootIntegerTranslationResponse master w c x target l : ZMod p))

theorem PolynomialRowFamily.integer_response_rough_units {n n' r m N : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n') ℤ)}
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (master : MasterParameterFamily) (hF : MasterParameterConditions N A D master)
    (w : ℕ) (c : Fin (m + 1) → ℕ) (x : Fin n → ℕ) (target : Fin r)
    (habs : ∀ k, (primorial w) ^ (master.exponent w + 1) * c k ∣ (master.modulus w : ℕ))
    (hg : predictionLocalPrimeGoodEvent master (F.catalog target) (F.denominator target) w x) :
    F.IntegerResponseUnitConditions master w c x target := by
  constructor
  intro p hp hwp havoid
  letI : Fact p.Prime := ⟨hp⟩
  have hM := hF.modulus_residue_isUnit w p (prime_coprime_primorial_of_gt hp hwp).symm
  have hcat : ∀ f ∈ F.catalog target,
      IsUnit ((MvPolynomial.eval (fun j => (x j : ℤ)) f : ℤ) : ZMod p) := by
    intro f hf
    rw [integerPolynomialEval_residue]
    exact isUnit_iff_ne_zero.mpr (havoid f hf)
  exact ⟨fun i hi l hl => F.integerTranslationResponse_residue_isUnit master w c x
    target i l hi hl p habs hg hM hcat,
    fun l hl => F.rootIntegerTranslationResponse_residue_isUnit master w c x target l hl p habs hM hcat⟩

theorem maskGenerated_integer_response_unit_conditions (m : ℕ) {N : ℕ}
    (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ k, 0 < a k)
    (block : ℕ → Fin (m + 1) → Finset ℕ)
    (hblock : ∀ w k, block w k ⊆ Finset.range N)
    (hnonempty : ∀ w k, (block w k).Nonempty) :
    ∀ᶠ w in atTop, ∀ t : Fin (Fintype.card (LargeColumnSubset m)), ∀ x,
      predictionLocalPrimeGoodEvent (maskGeneratedMaster m gap)
        ((maskGeneratedRowDataFamily m gap t).rows.catalog (maskGeneratedRowDataFamily m gap t).target)
        ((maskGeneratedRowDataFamily m gap t).rows.denominator (maskGeneratedRowDataFamily m gap t).target) w x →
      (maskGeneratedRowDataFamily m gap t).rows.IntegerResponseUnitConditions
        (maskGeneratedMaster m gap) w (masterColumnCoefficient N a block w) x
        (maskGeneratedRowDataFamily m gap t).target := by
  have hA : ∀ q ∈ Finset.univ.image a, 0 < q := by
    intro q hq
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hq
    exact ha k
  have hF := maskGeneratedMaster_conditions m gap (Finset.univ.image a) hA
  filter_upwards [hF.column_coefficients a
    (fun k => Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩) block hblock hnonempty] with w hw
  intro t x hg
  exact (maskGeneratedRowDataFamily m gap t).rows.integer_response_rough_units
    (maskGeneratedMaster m gap) hF w _ x _ (fun k => (hw k).2.2) hg

theorem PolynomialRowFamily.integer_response_nonunit_exception {n r m : ℕ}
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (master : MasterParameterFamily) (w : ℕ) (c : Fin (m + 1) → ℕ)
    (x : Fin n → ℕ) (target : Fin r)
    (hu : F.IntegerResponseUnitConditions master w c x target)
    (p : ℕ) (hp : p.Prime) (hwp : w < p) (i l : Fin r) (hi : i ≠ target) (hl : l ≠ i)
    (hbad : ¬ IsUnit (F.integerTranslationResponse master w c x target i l : ZMod p)) :
    ∃ f ∈ F.catalog target,
      MvPolynomial.eval₂ (Int.castRingHom (ZMod p)) (fun j => (x j : ZMod p)) f = 0 := by
  by_contra h
  have havoid : ∀ f ∈ F.catalog target,
      MvPolynomial.eval₂ (Int.castRingHom (ZMod p)) (fun j => (x j : ZMod p)) f ≠ 0 := by
    intro f hf hz
    exact h ⟨f, hf, hz⟩
  exact hbad ((hu.rough_units p hp hwp havoid).1 i hi l hl)

theorem PolynomialRowFamily.root_response_nonunit_exception {n r m : ℕ}
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (master : MasterParameterFamily) (w : ℕ) (c : Fin (m + 1) → ℕ)
    (x : Fin n → ℕ) (target : Fin r)
    (hu : F.IntegerResponseUnitConditions master w c x target)
    (p : ℕ) (hp : p.Prime) (hwp : w < p) (l : Fin r) (hl : l ≠ target)
    (hbad : ¬ IsUnit (F.rootIntegerTranslationResponse master w c x target l : ZMod p)) :
    ∃ f ∈ F.catalog target,
      MvPolynomial.eval₂ (Int.castRingHom (ZMod p)) (fun j => (x j : ZMod p)) f = 0 := by
  by_contra h
  have havoid : ∀ f ∈ F.catalog target,
      MvPolynomial.eval₂ (Int.castRingHom (ZMod p)) (fun j => (x j : ZMod p)) f ≠ 0 := by
    intro f hf hz
    exact h ⟨f, hf, hz⟩
  exact hbad ((hu.rough_units p hp hwp havoid).2 l hl)

end Hindman168
