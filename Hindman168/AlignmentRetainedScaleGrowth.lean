import Hindman168.AlignmentRetainedScaleBound

namespace Hindman168
open Filter
open scoped Topology BigOperators

theorem alignment_retained_scale_eventually
    {n k : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions n A D F)
    (i : Fin n) (T : Finset (Fin n)) (d : ℕ) (hd : 0 < d)
    (p : ℕ) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ w in atTop, ∀ (x : Fin n → ℕ) (q S : ℕ), 0 < q →
      q ≤ F.auxiliary w i.val → S ≤ F.auxiliary w i.val →
      (S : ℝ) ^ p ≤ eps * (alignmentCubeScale F w i T x / ((d : ℝ) * q)) := by
  have hg := master_microcell_eventually_polynomial_small hF (fun _ => i) (p + 2) d heps
  filter_upwards [hg] with w hw x q S hq hqV hSV
  have ha : 1 ≤ (∏ j ∈ T, 2 ^ Nat.log2 (x j) : ℕ) := by
    have h : 0 < (∏ j ∈ T, 2 ^ Nat.log2 (x j) : ℕ) := by positivity
    omega
  have h := alignment_retained_scale_power_bound (F.modulus w) q d
    (∏ j ∈ T, 2 ^ Nat.log2 (x j) : ℕ)
    (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)) (F.auxiliary w i.val) S eps p
    (by exact_mod_cast (F.modulus w).pos) (by exact_mod_cast hq) (by exact_mod_cast hd)
    (by exact_mod_cast ha) (by positivity) (by positivity) (by positivity) heps.le
    (by exact_mod_cast F.modulus_le_auxiliary w i.val) (by exact_mod_cast hqV)
    (by exact_mod_cast hSV) hw
  simpa only [alignmentCubeScale, alignmentShortBinVolume, Nat.cast_mul] using h

theorem alignment_tail_factor_scale_eventually
    {n k : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions n A D F)
    (i : Fin n) (T : Finset (Fin n)) (hT : ∀ j ∈ T, j < i)
    (d : ℕ) (hd : 0 < d) (p : ℕ) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ w in atTop, ∀ (x : Fin n → ℕ), (∀ j ∈ T, 0 < x j) →
      (∀ j, j < i → x j ≤ F.cutoff w j.val ^ 2) →
      ∀ U : Finset (Fin n), U ⊆ T → ∀ j ∈ T,
      ((2 ^ Nat.log2 (x j) : ℕ) : ℝ) ^ p ≤
        eps * (alignmentCubeScale F w i T x / ((d : ℝ) * alignmentNaturalBlockProduct x U)) := by
  filter_upwards [alignment_retained_scale_eventually hF i T d hd p heps] with
    w hw x hx hcut U hU j hj
  have hq : 0 < alignmentNaturalBlockProduct x U := by
    unfold alignmentNaturalBlockProduct
    exact Finset.prod_pos (fun l hl => hx l (hU hl))
  have hqV := alignment_earlier_block_product_bound hF w i x hcut U
    (fun l hl => hT l (hU hl))
  have hjV : x j ≤ F.auxiliary w i.val := by
    have h := alignment_earlier_block_product_bound hF w i x hcut {j}
      (by intro l hl; have he := Finset.mem_singleton.mp hl; subst l; exact hT j hj)
    simpa only [alignmentNaturalBlockProduct, Finset.prod_singleton] using h
  have hSV := (Nat.log2_self_le (hx j hj).ne').trans hjV
  exact hw x (alignmentNaturalBlockProduct x U) (2 ^ Nat.log2 (x j)) hq hqV hSV

theorem alignment_tail_factor_scale_powerDominates
    {n k : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions n A D F)
    (i : Fin n) (T : Finset (Fin n)) (hT : ∀ j ∈ T, j < i)
    (d : ℕ) (hd : 0 < d) (x : ℕ → Fin n → ℕ)
    (U : ℕ → Finset (Fin n)) (j : ℕ → Fin n)
    (hvalid : ∀ᶠ w in atTop, (∀ l ∈ T, 0 < x w l) ∧
      (∀ l, l < i → x w l ≤ F.cutoff w l.val ^ 2) ∧ U w ⊆ T ∧ j w ∈ T) :
    PowerDominates atTop
      (fun w => alignmentCubeScale F w i T (x w) / ((d : ℝ) * alignmentNaturalBlockProduct (x w) (U w)))
      (fun w => ((2 ^ Nat.log2 (x w (j w)) : ℕ) : ℝ)) := by
  intro p
  apply Asymptotics.isLittleO_iff.mpr
  intro eps heps
  filter_upwards [alignment_tail_factor_scale_eventually hF i T hT d hd p heps, hvalid]
    with w hw hv
  have hb := hw (x w) hv.1 hv.2.1 (U w) hv.2.2.1 (j w) hv.2.2.2
  have hz : 0 ≤ alignmentCubeScale F w i T (x w) /
      ((d : ℝ) * alignmentNaturalBlockProduct (x w) (U w)) := by
    unfold alignmentCubeScale
    positivity
  have hs : 0 ≤ (((2 ^ Nat.log2 (x w (j w)) : ℕ) : ℝ) ^ p) := by positivity
  simpa only [Real.norm_eq_abs, abs_of_nonneg hs,
    abs_of_nonneg hz] using hb

end Hindman168
