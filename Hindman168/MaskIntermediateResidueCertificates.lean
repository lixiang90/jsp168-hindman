import Hindman168.MaskBaseResidueCertificates
import Hindman168.MonomialPrimeResidueUnits

/-! Certificates for every fixed monomial row family, including actual
intermediate multiplicative-mask stages, under the unchanged generated
master. No inclusion in the final row catalogue or good event is needed. -/

set_option maxHeartbeats 2000000

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

noncomputable def monomialRowPrimeMass (m : ℕ) {N : ℕ} (gap : ℕ → Fin N) (n w : ℕ) :
    Mass (Fin n → ℕ) :=
  masterPrimeSlotsMass (maskGeneratedMaster m gap) w (fun _ => (gap w).val)

variable {m N n r : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)

include gap ha hC in
theorem monomialRows_integer_conditions_eventually :
    ∀ᶠ w in atTop, ∀ x, F.NormalizedIntegerRowConditions x
      (masterColumnCoefficient N a (fun w => (C w).block) w) (primorial w) := by
  have hA : ∀ q ∈ Finset.univ.image a, 0 < q := by
    intro q hq
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hq
    exact ha k
  have hF := maskGeneratedMaster_conditions m gap (Finset.univ.image a) hA
  have hmem : ∀ k, a k ∈ Finset.univ.image a := fun k =>
    Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
  filter_upwards [hF.column_coefficients a hmem (fun w => (C w).block) hC
    (fun w k => (C w).block_nonempty k), hF.chain_column_ratios a hmem C hC] with w hw hr
  intro x
  exact F.ordered_integer_row_conditions x _ _ (fun k => (hw k).1) hr

include gap ha hC in
theorem monomialRows_primitive_eventually (hmono : F.MonomialStructure) :
    ∀ᶠ w in atTop, ∀ x ∈ (monomialRowPrimeMass m gap n w).support,
      ∀ p : boundedRoughPrimeSet w ((maskGeneratedMaster m gap).auxiliary w (gap w).val),
      ∀ i, ∃ j, (F.normalizedIntegerRow x
        (masterColumnCoefficient N a (fun w => (C w).block) w) i j : ZMod (p : ℕ)) ≠ 0 := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  have hp := hF.prime_slots_eventually_gt_budget (fun w (_ : Fin n) => gap w)
    (fun w => (maskGeneratedMaster m gap).auxiliary w (gap w).val)
    (Eventually.of_forall (fun _ _ => le_rfl))
  filter_upwards [monomialRows_integer_conditions_eventually gap a ha C hC F, hp] with w hr hb
  intro x hx p i
  have hpr := (mem_boundedRoughPrimeSet w ((maskGeneratedMaster m gap).auxiliary w (gap w).val) (p : ℕ)).mp p.property
  letI : Fact (p : ℕ).Prime := ⟨hpr.1⟩
  refine ⟨F.normalizationAnchor i, ?_⟩
  rw [(hr x).anchor i]
  exact ((hmono i).monomial_of_ne_zero _ (F.normalizationAnchor_ne_zero i)).residue_isUnit_bounded
    x (hb x hx) hpr.1.pos hpr.2.2 |>.ne_zero

include gap ha hC in
theorem monomialRows_independent_eventually (target : Fin r) :
    ∀ᶠ w in atTop, ∀ x ∈ (monomialRowPrimeMass m gap n w).support,
      ∀ p : boundedRoughPrimeSet w ((maskGeneratedMaster m gap).auxiliary w (gap w).val),
      ¬ squarefreeCRTBadEvent
        (boundedRoughPrimeSet w ((maskGeneratedMaster m gap).auxiliary w (gap w).val))
        (fun p hp => ((mem_boundedRoughPrimeSet w ((maskGeneratedMaster m gap).auxiliary w (gap w).val) p).mp hp).1)
        (F.catalog target) (fun j => (x j : ZMod (squarefreeCRTModulus
          (boundedRoughPrimeSet w ((maskGeneratedMaster m gap).auxiliary w (gap w).val))))) p →
      ∀ i l, i ≠ l → LinearIndependent (ZMod (p : ℕ))
        ![(fun j => (F.normalizedIntegerRow x (masterColumnCoefficient N a (fun w => (C w).block) w) i j : ZMod (p : ℕ))),
          (fun j => (F.normalizedIntegerRow x (masterColumnCoefficient N a (fun w => (C w).block) w) l j : ZMod (p : ℕ)))] := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  filter_upwards [monomialRows_integer_conditions_eventually gap a ha C hC F,
    MaskOriginalSampling.actualColumnBounds_eventually (m := m) gap a ha C hC] with w hr hc
  intro x _ p hbad i l hil
  have hp := (mem_boundedRoughPrimeSet w ((maskGeneratedMaster m gap).auxiliary w (gap w).val) (p : ℕ)).mp p.property
  apply (hr x).residue_pair_independent (fun col => (hc col).1) target i l hil (p : ℕ) hp.1
  · intro col
    exact natDivisor_residue_isUnit (hc col).2.1
      (hF.modulus_residue_isUnit w (p : ℕ) (prime_coprime_primorial_of_gt hp.1 hp.2.1).symm)
  · exact F.catalog_nonzero_of_not_squarefree_bad _ _ _ x p hbad

end Hindman168
