import Hindman168.AlignmentRetainedCRTClasses
import Hindman168.AlignmentMasterResidueData
import Hindman168.RoughDenominatorUnits
import Hindman168.AlignmentExposureArrayGoodEvent

namespace Hindman168
open scoped BigOperators

theorem alignmentMaster_retained_coprime
    {n k : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions n A D F)
    (w d : ℕ) (hd : 0 < d) (hw : d ≤ w) (x : Fin n → ℕ) (U : Finset (Fin n))
    (hunit : ∀ j ∈ U, Nat.Coprime (x j) (primorial w)) :
    Nat.Coprime (F.modulus w : ℕ) (alignmentNaturalBlockProduct x U) ∧
      Nat.Coprime d (alignmentNaturalBlockProduct x U) := by
  have h := alignmentMaster_tail_coprime hF w x U hunit
  have hW := (alignmentNaturalBlockProduct_coprime x U (primorial w) hunit).symm
  exact ⟨Nat.Coprime.of_dvd_left (dvd_mul_right (F.modulus w : ℕ) _) h.symm,
    fixed_denominator_coprime_rough hd.ne' hw hW⟩

theorem alignmentMaster_retained_cube_class
    {n k : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions n A D F)
    (w d : ℕ) (hd : 0 < d) (hw : d ≤ w) (x : Fin n → ℕ) (T U : Finset (Fin n))
    (hU : U ⊆ T) (hpos : ∀ j ∈ U, 0 < x j)
    (hunit : ∀ j ∈ U, Nat.Coprime (x j) (primorial w))
    (p Y r c ell : ℤ)
    (hr : ((alignmentNaturalBlockProduct x T : ℤ) * p) % (F.modulus w : ℤ) = r)
    (hc : Int.ModEq d (alignmentCubeBase (F.modulus w) (alignmentNaturalBlockProduct x T) p Y ell) c) :
    let a := alignmentRetainedRepresentative (F.modulus w) d (alignmentNaturalBlockProduct x U) Y r c
    0 ≤ a ∧ a < (d : ℤ) * alignmentNaturalBlockProduct x U ∧
      Int.ModEq ((d : ℤ) * alignmentNaturalBlockProduct x U) a
        (alignmentCubeBase (F.modulus w) (alignmentNaturalBlockProduct x T) p Y ell) := by
  have hq : 0 < alignmentNaturalBlockProduct x U := Finset.prod_pos hpos
  have hco := alignmentMaster_retained_coprime hF w d hd hw x U hunit
  have hdiv : (alignmentNaturalBlockProduct x U : ℤ) ∣ (alignmentNaturalBlockProduct x T : ℤ) := by
    exact_mod_cast Finset.prod_dvd_prod_of_subset U T x hU
  have hb := alignmentRetainedRepresentative_bounds (F.modulus w) d
    (alignmentNaturalBlockProduct x U) hd hq Y r c
  exact ⟨hb.1, hb.2, alignment_retained_cube_class (F.modulus w) d
    (alignmentNaturalBlockProduct x U) hq hco.1 hco.2
    (alignmentNaturalBlockProduct x T) p Y r c ell hdiv hr hc⟩

theorem alignment_raw_retained_cube_class
    {n k : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions n A D F)
    (w d : ℕ) (hd : 0 < d) (hw : d ≤ w) (x : Fin n → ℕ)
    (hx : x ∈ (globalRawMass (F.cutoff w) (primorial w) n).support)
    (T U : Finset (Fin n)) (hU : U ⊆ T) (p Y r c ell : ℤ)
    (hr : ((alignmentNaturalBlockProduct x T : ℤ) * p) % (F.modulus w : ℤ) = r)
    (hc : Int.ModEq d (alignmentCubeBase (F.modulus w) (alignmentNaturalBlockProduct x T) p Y ell) c) :
    let a := alignmentRetainedRepresentative (F.modulus w) d (alignmentNaturalBlockProduct x U) Y r c
    0 ≤ a ∧ a < (d : ℤ) * alignmentNaturalBlockProduct x U ∧
      Int.ModEq ((d : ℤ) * alignmentNaturalBlockProduct x U) a
        (alignmentCubeBase (F.modulus w) (alignmentNaturalBlockProduct x T) p Y ell) := by
  apply alignmentMaster_retained_cube_class hF w d hd hw x T U hU
    (fun j _ => alignmentGlobalRawMass_support_positive hF w x hx j) _ p Y r c ell hr hc
  intro j _
  have hn := Finsupp.mem_support_iff.mp hx
  rw [globalRawMass, FiniteMass.piMass_apply] at hn
  have hs := Finsupp.mem_support_iff.mpr (Finset.prod_ne_zero_iff.mp hn j (Finset.mem_univ j))
  exact (Finset.mem_filter.mp (rawMass_support_window _ _ hs)).2

theorem alignment_retained_product_update {n : ℕ} (x : Fin n → ℕ)
    (U : Finset (Fin n)) (j : Fin n) (hj : j ∉ U) (s : ℕ) :
    alignmentNaturalBlockProduct (Function.update x j s) U = alignmentNaturalBlockProduct x U := by
  apply Finset.prod_congr rfl
  intro l hl
  exact Function.update_of_ne (by intro he; subst l; exact hj hl) _ _

theorem alignmentRetainedRepresentative_update {n : ℕ} (M d : ℕ)
    (x : Fin n → ℕ) (U : Finset (Fin n)) (j : Fin n) (hj : j ∉ U)
    (s : ℕ) (Y r c : ℤ) :
    alignmentRetainedRepresentative M d (alignmentNaturalBlockProduct (Function.update x j s) U) Y r c =
      alignmentRetainedRepresentative M d (alignmentNaturalBlockProduct x U) Y r c := by
  rw [alignment_retained_product_update x U j hj s]

end Hindman168
