import Hindman168.PrincipalPositiveCountExtraction
import Hindman168.MasterDivisorSampling
import Hindman168.AlignedInteriorMassSplit

/-!
# Positive principal counts yield distinct finite FS/FP witnesses

Original harmonic support bounds and the original cutoff growth imply
strict increase of every supported scaled tuple. This finishes the finite
witness extraction in Section 2.5, conditional only on count positivity.
-/

namespace Hindman168
open Filter FiniteMass
open scoped BigOperators Topology Classical

/-- Every supported pivot coordinate lies in its original harmonic window. -/
theorem principalPivotProductMass_support_bounds {n m : ℕ}
    (e : Fin (2*n) ↪o ℕ) (F : MasterParameterFamily)
    (C : PrincipalCoordinateChain n m) (w : ℕ) (z : Fin m → ℤ)
    (hz : z ∈ (principalPivotProductMass e F C w).support) (i : Fin m) :
    F.cutoff w (energyPrincipal e (C.pivot i)) ≤ (z i).toNat ∧
      (z i).toNat < F.cutoff w (energyPrincipal e (C.pivot i)) ^ 2 := by
  have hn := Finsupp.mem_support_iff.mp hz
  rw [principalPivotProductMass, piMass_apply] at hn
  have hcoord := Finsupp.mem_support_iff.mpr
    (Finset.prod_ne_zero_iff.mp hn i (Finset.mem_univ i))
  have hwin := Finset.mem_Ico.mp (integerMass_support_in_window _ _ hcoord)
  have hz0 : 0 ≤ z i := (Int.natCast_nonneg _).trans hwin.1
  have hc : ((z i).toNat : ℤ) = z i := Int.toNat_of_nonneg hz0
  constructor
  · exact_mod_cast (show (F.cutoff w (energyPrincipal e (C.pivot i)) : ℤ) ≤
      ((z i).toNat : ℤ) by simpa only [hc] using hwin.1)
  · exact_mod_cast (show ((z i).toNat : ℤ) <
      (F.cutoff w (energyPrincipal e (C.pivot i)) ^ 2 : ℕ) by
        simpa only [hc] using hwin.2)

/-- Original admissibility makes every supported scaled tuple strictly
increasing. No extra separation or injectivity premise is assumed. -/
theorem MasterParameterConditions.principal_support_strictMono_eventually
    {d n m M : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin d) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions M A P F)
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M)
    (C : PrincipalCoordinateChain n m) (a : Fin m → ℚ) (ha : ∀ i, a i ∈ A) :
    ∀ᶠ w in atTop, ∀ z ∈ (principalPivotProductMass e F C w).support,
      StrictMono (fun i => C.coefficient M e a w i * (z i).toNat) := by
  have hcoeff := hF.column_coefficients_bounds a ha (fun _ => (C.lift e).block)
    (fun _ => C.lift_range e heM) (fun _ i => (C.lift e).block_nonempty i)
  have hg : ∀ᶠ w in atTop, ∀ i : Fin m,
      2 * F.auxiliary w (energyPrincipal e (C.pivot i)) ^ 2 ≤
        F.cutoff w (energyPrincipal e (C.pivot i)) := by
    apply (eventually_all).mpr
    intro i
    have hb := (powerDominates_log_to_cutoff
      (hF.cutoff_auxiliary_growth (energyPrincipal e (C.pivot i)))).eventually_bound
      (Eventually.of_forall (fun _ => Nat.cast_nonneg _))
      (Eventually.of_forall (fun _ => Nat.cast_nonneg _)) 2 (by norm_num : (0 : ℝ) < 2)
    filter_upwards [hb] with w hw
    exact_mod_cast hw
  filter_upwards [hcoeff, hg] with w hcw hgw
  intro z hz i j hij
  have hci : C.coefficient M e a w i ≤ (F.modulus w : ℕ) := by
    simpa only [C.coefficient_lift e heM] using (hcw i).2.2
  have hcj : 0 < C.coefficient M e a w j := by
    simpa only [C.coefficient_lift e heM] using (hcw j).1
  have hp : energyPrincipal e (C.pivot i) < energyPrincipal e (C.pivot j) :=
    (energyPrincipal_strictMono e) (C.pivot_strictMono hij)
  have hprior : F.cutoff w (energyPrincipal e (C.pivot i)) ^ 2 ≤
      F.auxiliary w (energyPrincipal e (C.pivot j)) := by
    simpa using hF.earlier_tail_product_bound w (energyPrincipal e (C.pivot j))
      {energyPrincipal e (C.pivot i)} (by simpa using hp)
  have hzi := (principalPivotProductMass_support_bounds e F C w z hz i).2.le
  have hzj := (principalPivotProductMass_support_bounds e F C w z hz j).1
  have hm := F.modulus_le_auxiliary w (energyPrincipal e (C.pivot j))
  have hv := F.auxiliary_ge_two w (energyPrincipal e (C.pivot j))
  have hai : C.coefficient M e a w i * (z i).toNat ≤
      F.auxiliary w (energyPrincipal e (C.pivot j)) ^ 2 := by
    calc
      _ ≤ F.auxiliary w (energyPrincipal e (C.pivot j)) *
          F.auxiliary w (energyPrincipal e (C.pivot j)) :=
        Nat.mul_le_mul (hci.trans hm) (hzi.trans hprior)
      _ = _ := by ring
  have haj : F.cutoff w (energyPrincipal e (C.pivot j)) ≤
      C.coefficient M e a w j * (z j).toNat := by nlinarith
  have hgg := hgw j
  nlinarith

/-- The actual positive weighted count produces the repository's exact
indexed witness, with injectivity derived from the original support. -/
theorem MasterParameterConditions.principal_positive_count_indexed_eventually
    {d n m M r : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin d) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions M A P F)
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M)
    (C : PrincipalCoordinateChain n (m+1)) (a : Fin (m+1) → ℚ)
    (ha : ∀ i, a i ∈ A) (χ : ℕ → Fin r) :
    ∀ᶠ w in atTop, ∀ κ : Fin r,
      0 < principalWeightedColorCount C M e F a χ (fun _ => κ) κ w →
      IndexedWitness (m := m+1) χ := by
  filter_upwards [hF.principal_positive_count_extract_eventually e heM C a ha χ,
    hF.principal_support_strictMono_eventually e heM C a ha] with w hex hstrict
  intro κ hcount
  obtain ⟨z, hz, hpos, hmono⟩ := hex κ hcount
  exact ⟨fun i => C.coefficient M e a w i * (z i).toNat,
    (hstrict z hz).injective, fun i => (hpos i).2, κ, hmono⟩

/-- Positivity at arbitrarily late stages suffices for a genuine finite
FS/FP set of exactly the requested size. This is the end of the paper's
counting argument; obtaining positive counts is still the analytic task. -/
theorem MasterParameterConditions.principal_positive_counts_yield_finite_witness
    {d n m M r : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin d) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions M A P F)
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M)
    (C : PrincipalCoordinateChain n (m+1)) (a : Fin (m+1) → ℚ)
    (ha : ∀ i, a i ∈ A) (χ : ℕ → Fin r)
    (hpositive : ∃ᶠ w in atTop, ∃ κ : Fin r,
      0 < principalWeightedColorCount C M e F a χ (fun _ => κ) κ w) :
    ∃ B : Finset ℕ, B.card = m+1 ∧ (∀ x ∈ B, 0 < x) ∧ MonoFSFP χ B := by
  have he := hF.principal_positive_count_indexed_eventually e heM C a ha χ
  obtain ⟨w, ⟨κ, hκ⟩, hw⟩ := (hpositive.and_eventually he).exists
  exact indexed_to_finset χ (hw κ hκ)

/-- A finite family of chains and scales may supply different positive
counts at different stages. No fixed witnessing chain is required. -/
theorem MasterParameterConditions.principal_finite_family_yields_finite_witness
    {d n m M r : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin d) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions M A P F)
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M)
    {ι : Type*} [Fintype ι] (C : ι → PrincipalCoordinateChain n (m+1))
    (a : ι → Fin (m+1) → ℚ) (ha : ∀ q i, a q i ∈ A)
    (χ : ℕ → Fin r)
    (hpositive : ∃ᶠ w in atTop, ∃ q : ι, ∃ κ : Fin r,
      0 < principalWeightedColorCount (C q) M e F (a q) χ (fun _ => κ) κ w) :
    ∃ B : Finset ℕ, B.card = m+1 ∧ (∀ x ∈ B, 0 < x) ∧ MonoFSFP χ B := by
  have he : ∀ᶠ w in atTop, ∀ q : ι, ∀ κ : Fin r,
      0 < principalWeightedColorCount (C q) M e F (a q) χ (fun _ => κ) κ w →
        IndexedWitness (m := m+1) χ := by
    apply (eventually_all).mpr
    intro q
    exact hF.principal_positive_count_indexed_eventually e heM (C q) (a q) (ha q) χ
  obtain ⟨w, ⟨q, κ, hκ⟩, hw⟩ := (hpositive.and_eventually he).exists
  exact indexed_to_finset χ (hw q κ hκ)

/-- The positive finite sum of actual counts in equation (2.16) gives
an actual finite witness. Chains, scales and colors may vary in the sum. -/
theorem MasterParameterConditions.principal_positive_sum_yields_finite_witness
    {d n m M r : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin d) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions M A P F)
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M)
    {ι : Type*} [Fintype ι] (C : ι → PrincipalCoordinateChain n (m+1))
    (a : ι → Fin (m+1) → ℚ) (ha : ∀ q i, a q i ∈ A)
    (χ : ℕ → Fin r) (κ : ι → Fin r)
    (hpositive : ∃ᶠ w in atTop, 0 < ∑ q,
      principalWeightedColorCount (C q) M e F (a q) χ (fun _ => κ q) (κ q) w) :
    ∃ B : Finset ℕ, B.card = m+1 ∧ (∀ x ∈ B, 0 < x) ∧ MonoFSFP χ B := by
  apply hF.principal_finite_family_yields_finite_witness e heM C a ha χ
  apply hpositive.mono
  intro w hw
  by_contra hn
  push Not at hn
  have hs : (∑ q,
      principalWeightedColorCount (C q) M e F (a q) χ (fun _ => κ q) (κ q) w) ≤ 0 := by
    apply Finset.sum_nonpos
    intro q _
    exact hn q (κ q)
  linarith

end Hindman168
