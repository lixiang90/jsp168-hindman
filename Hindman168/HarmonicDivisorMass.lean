import Hindman168.HarmonicComparisonExcess
import Hindman168.FiniteCountableExpectations
import Hindman168.IntegerProductLaw

/-!
# Original finite harmonic row-divisor masses

These are the actual independent raw masses mapped to products, with
their exact PMFs and their positive, rough, cutoff-bounded supports.
No new independence hypothesis is introduced by the row product map.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

noncomputable def harmonicDivisorMass {κ : Type*} [Fintype κ] (X : κ → ℕ) (W : ℕ) : Mass ℕ :=
  (piMass (fun j => rawMass (X j) W)).mapDomain (fun x => ∏ j, x j)

noncomputable def harmonicRowDivisorMass {q : ℕ} {κ : Type*} [Fintype κ]
    (X : Fin q → κ → ℕ) (W : ℕ) : Mass (Fin q → ℕ) :=
  piMass (fun i => harmonicDivisorMass (X i) W)

theorem harmonicDivisorMass_nonneg {κ : Type*} [Fintype κ] (X : κ → ℕ) (W : ℕ)
    (hH : ∀ j, 0 < harmonicNormalizer (X j) W) (d : ℕ) :
    0 ≤ harmonicDivisorMass X W d :=
  push_nonneg _ _ (piMass_nonneg _ (fun j n => by
    rw [rawMass_apply]; exact harmonicWeight_nonneg (hH j) n)) d

theorem harmonicDivisorMass_total {κ : Type*} [Fintype κ] (X : κ → ℕ) (W : ℕ)
    (hH : ∀ j, 0 < harmonicNormalizer (X j) W) : total (harmonicDivisorMass X W) = 1 := by
  rw [harmonicDivisorMass, total_push, piMass_total_one _ (fun j => rawMass_total (hH j))]

theorem harmonicDivisorPMF_eq_toPMF {κ : Type*} [Fintype κ] (X : κ → ℕ) (W : ℕ)
    (hH : ∀ j, 0 < harmonicNormalizer (X j) W) :
    harmonicDivisorPMF X W hH = toPMF (harmonicDivisorMass X W)
      (harmonicDivisorMass_nonneg X W hH) (harmonicDivisorMass_total X W hH) := by
  unfold harmonicDivisorPMF
  simp only [harmonicPMF_eq_toPMF]
  rw [← toPMF_piMass, toPMF_map]
  rfl

theorem harmonicRowDivisorMass_nonneg {q : ℕ} {κ : Type*} [Fintype κ]
    (X : Fin q → κ → ℕ) (W : ℕ) (hH : ∀ i j, 0 < harmonicNormalizer (X i j) W)
    (d : Fin q → ℕ) : 0 ≤ harmonicRowDivisorMass X W d :=
  piMass_nonneg _ (fun i => harmonicDivisorMass_nonneg (X i) W (hH i)) d

theorem harmonicRowDivisorMass_total {q : ℕ} {κ : Type*} [Fintype κ]
    (X : Fin q → κ → ℕ) (W : ℕ) (hH : ∀ i j, 0 < harmonicNormalizer (X i j) W) :
    total (harmonicRowDivisorMass X W) = 1 :=
  piMass_total_one _ (fun i => harmonicDivisorMass_total (X i) W (hH i))

theorem harmonicRowDivisorPMF_eq_toPMF {q : ℕ} {κ : Type*} [Fintype κ]
    (X : Fin q → κ → ℕ) (W : ℕ) (hH : ∀ i j, 0 < harmonicNormalizer (X i j) W) :
    harmonicRowDivisorPMF X W hH = toPMF (harmonicRowDivisorMass X W)
      (harmonicRowDivisorMass_nonneg X W hH) (harmonicRowDivisorMass_total X W hH) := by
  unfold harmonicRowDivisorPMF harmonicRowDivisorMass
  simp only [harmonicDivisorPMF_eq_toPMF]
  rw [← toPMF_piMass]

theorem harmonicDivisorMass_support {κ : Type*} [Fintype κ] (X : κ → ℕ) (W : ℕ)
    (hX : ∀ j, 2 ≤ X j) {d : ℕ} (hd : d ∈ (harmonicDivisorMass X W).support) :
    0 < d ∧ d ≤ ∏ j, (X j) ^ 2 ∧ d.Coprime W := by
  classical
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hd)
  have hs (j : κ) : x j ∈ harmonicWindow (X j) W := by
    have hj := Fintype.mem_piFinset.mp (piMass_support _ hx) j
    exact (unitInterval_raw (X j) W) ▸ (intervalMass_support _ _ _ _ hj)
  have hpos (j : κ) : 0 < x j := by
    have hj := (Finset.mem_Ico.mp (Finset.mem_filter.mp (hs j)).1).1
    have hXj := hX j
    omega
  have hle (j : κ) : x j ≤ (X j) ^ 2 :=
    (Finset.mem_Ico.mp (Finset.mem_filter.mp (hs j)).1).2.le
  have hc (j : κ) : (x j).Coprime W := (Finset.mem_filter.mp (hs j)).2
  exact ⟨Finset.prod_pos (fun j _ => hpos j),
    Finset.prod_le_prod' (fun j _ => hle j), Nat.coprime_prod_left_iff.mpr (fun j _ => hc j)⟩

theorem harmonicRowDivisorMass_support {q : ℕ} {κ : Type*} [Fintype κ]
    (X : Fin q → κ → ℕ) (W : ℕ) (hX : ∀ i j, 2 ≤ X i j)
    {d : Fin q → ℕ} (hd : d ∈ (harmonicRowDivisorMass X W).support) (i : Fin q) :
    0 < d i ∧ d i ≤ ∏ j, (X i j) ^ 2 ∧ (d i).Coprime W := by
  classical
  have hne := Finsupp.mem_support_iff.mp hd
  change piMass (fun i => harmonicDivisorMass (X i) W) d ≠ 0 at hne
  rw [piMass_apply] at hne
  exact harmonicDivisorMass_support (X i) W (hX i)
    (Finsupp.mem_support_iff.mpr (Finset.prod_ne_zero_iff.mp hne i (Finset.mem_univ i)))

theorem harmonicRowDivisorMass_expectation {q : ℕ} {κ : Type*} [Fintype κ]
    (X : Fin q → κ → ℕ) (W : ℕ) (hH : ∀ i j, 0 < harmonicNormalizer (X i j) W)
    (f : (Fin q → ℕ) → ℝ) :
    expectation (harmonicRowDivisorMass X W) f =
      DiscreteProduct.expectation (harmonicRowDivisorPMF X W hH) f := by
  rw [harmonicRowDivisorPMF_eq_toPMF, toPMF_expectation]

end Hindman168
