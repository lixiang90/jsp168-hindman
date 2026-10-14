import Hindman168.MaskDescendantIntegerForms

/-! Every descendant row keeps its original tail majorant. Invariant
rows receive the bounded merged function; both noninvariant copies keep
the original row function with its original bound. -/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass MaskOriginalSampling

variable {m N n r : ℕ} (gap : ℕ → Fin N) (C : ℕ → Chain (m + 1))

noncomputable def maskFamilyRowDivisorMass
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m) (w : ℕ) (i : Fin r) : Mass ℕ :=
  tailMass (primorial w) ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w)
    (F.normalizationAnchor i))

noncomputable def maskFamilyRowMajorant
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m) (w : ℕ) (i : Fin r) (t : ℤ) : ℝ :=
  1 + integerDivisorMask (maskFamilyRowDivisorMass gap C F w i) t

theorem maskFamilyRowMajorant_flattened
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (tag : Fin (m + 1) → Fin 3) (w : ℕ) (d : MaskDescendant F tag) (t : ℤ) :
    maskFamilyRowMajorant gap C (F.flattenedMaskStep tag) w (Fintype.equivFin _ d) t =
      maskFamilyRowMajorant gap C F w d.val.1 t := by
  unfold maskFamilyRowMajorant maskFamilyRowDivisorMass
  rw [F.flattenedMaskStep_normalizationAnchor tag d]

noncomputable def maskDescendantFunction {S U : Finset (Fin (m + 1))}
    (P : MaskColumnPlan S U) (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (w p q : ℕ) (f : Fin r → ℤ → ℝ) (d : MaskDescendant F P.tag) (t : ℤ) : ℝ :=
  match d.val.2 with
  | none => divisorWeightedMerge (maskFamilyRowDivisorMass gap C F w d.val.1)
      (P.absorbedScalar p q (P.tag (F.normalizationAnchor d.val.1)))
      (P.absorbedScalar q p (P.tag (F.normalizationAnchor d.val.1)))
      (f d.val.1) (f d.val.1) t
  | some _ => f d.val.1 t

theorem maskDescendantFunction_none {S U : Finset (Fin (m + 1))}
    (P : MaskColumnPlan S U) (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (w p q : ℕ) (f : Fin r → ℤ → ℝ) (d : MaskDescendant F P.tag) (hd : d.val.2 = none) (t : ℤ) :
    maskDescendantFunction gap C P F w p q f d t =
      divisorWeightedMerge (maskFamilyRowDivisorMass gap C F w d.val.1)
        (P.absorbedScalar p q (P.tag (F.normalizationAnchor d.val.1)))
        (P.absorbedScalar q p (P.tag (F.normalizationAnchor d.val.1))) (f d.val.1) (f d.val.1) t := by
  simp only [maskDescendantFunction, hd]

theorem maskDescendantFunction_some {S U : Finset (Fin (m + 1))}
    (P : MaskColumnPlan S U) (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (w p q : ℕ) (f : Fin r → ℤ → ℝ) (d : MaskDescendant F P.tag) (b : Bool)
    (hd : d.val.2 = some b) (t : ℤ) :
    maskDescendantFunction gap C P F w p q f d t = f d.val.1 t := by
  simp only [maskDescendantFunction, hd]

theorem maskDescendantFunction_bound {S U : Finset (Fin (m + 1))}
    (P : MaskColumnPlan S U) (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (w p q : ℕ) (f : Fin r → ℤ → ℝ)
    (hρ : ∀ i d, 0 ≤ maskFamilyRowDivisorMass gap C F w i d)
    (hp : ∀ i, ∀ d ∈ (maskFamilyRowDivisorMass gap C F w i).support, p.Coprime d)
    (hq : ∀ i, ∀ d ∈ (maskFamilyRowDivisorMass gap C F w i).support, q.Coprime d)
    (hf : ∀ i t, |f i t| ≤ maskFamilyRowMajorant gap C F w i t)
    (d : MaskDescendant F P.tag) (t : ℤ) :
    |maskDescendantFunction gap C P F w p q f d t| ≤
      maskFamilyRowMajorant gap C (F.flattenedMaskStep P.tag) w (Fintype.equivFin _ d) t := by
  rw [maskFamilyRowMajorant_flattened]
  cases hd : d.val.2 with
  | none =>
    rw [maskDescendantFunction_none gap C P F w p q f d hd]
    apply divisorWeightedMerge_bound _ (hρ d.val.1) _ _ _ _ (f d.val.1) (f d.val.1)
      (hf d.val.1) (hf d.val.1) t
    · intro k hk
      exact P.absorbedScalar_coprime p q k (hp d.val.1 k hk) (hq d.val.1 k hk) _
    · intro k hk
      exact P.absorbedScalar_coprime q p k (hq d.val.1 k hk) (hp d.val.1 k hk) _
  | some b =>
    rw [maskDescendantFunction_some gap C P F w p q f d b hd]
    exact hf d.val.1 t

variable (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)

include hC htail in
theorem maskDescendantFunction_eventually_bound :
    ∀ᶠ w in atTop, ∀ (n r : ℕ)
      (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
      (S U : Finset (Fin (m + 1))) (P : MaskColumnPlan S U),
      ∀ p ∈ primePool ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper,
      ∀ q ∈ primePool ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper,
      ∀ f : Fin r → ℤ → ℝ,
      (∀ i t, |f i t| ≤ maskFamilyRowMajorant gap C F w i t) →
      ∀ d : MaskDescendant F P.tag, ∀ t,
      |maskDescendantFunction gap C P F w p q f d t| ≤
        maskFamilyRowMajorant gap C (F.flattenedMaskStep P.tag) w (Fintype.equivFin _ d) t := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  filter_upwards [hF.raw_cutoffs_valid, maskTail_fresh_prime_units gap C hC htail] with w hv hu
  intro n r F S U P p hp q hq f hf d t
  apply maskDescendantFunction_bound gap C P F w p q f _ _ _ hf d t
  · intro i k
    exact tailMass_nonneg (primorial_pos w) _ (chain_tailCutoffs_valid (C w)
      ((maskGeneratedMaster m gap).cutoff w) (primorial w) (hC w)
      (fun j hj => ⟨(hv j hj).1, (hv j hj).2.1⟩) _) k
  · intro i k hk
    exact hu _ p hp k hk
  · intro i k hk
    exact hu _ q hq k hk

end Hindman168
