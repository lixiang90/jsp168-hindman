import Hindman168.PositivePrincipalSumBounds
import Hindman168.PrincipalPredictionLimitData

/-!
# From prediction limits and alignment mass to positive actual counts

This uses the exact `PrincipalPredictionLimitData` already produced by the
prediction construction. Calibration and weighted/model comparison
hypotheses are read from that structure, not assumed again. Alignment
enters through its raw event mass and the pointwise chain selection; no
positive actual or model count is assumed.
-/

namespace Hindman168
open Filter FiniteMass
open scoped BigOperators Topology Classical

/-- The union-bound and finite-count step (2.14)--(2.16), using the original
prediction limit interface and the actual principal weighted counts. -/
theorem principal_prediction_positive_sum_of_alignment_selection
    {n m r : ℕ} {ι α β : Type*} [Fintype α] [Fintype β]
    (M : ℕ) (e : Fin (2*n) ↪o ℕ) (F : MasterParameterFamily)
    (U : Ultrafilter ℕ) (cap η : ℝ) (a : ι → ℚ)
    (χ : ℕ → Fin r) (color : ι → Fin r)
    (S : Finset (Fin n) → Fin n → ι → ℕ → ℤ → ℝ)
    (hdata : PrincipalPredictionLimitData (m := m) M e F U cap η a χ color S)
    (hS : ∀ T b γ w y, S T b γ w y ∈ Set.Icc (0 : ℝ) 1)
    (hμ : ∀ᶠ w in (U : Filter ℕ), ∀ x, 0 ≤ selectedPrincipalRawMass e F w x)
    (T : α → Finset (Fin n)) (pivot : α → Fin n) (index : α → ι)
    (hT : ∀ j, (T j).Nonempty) (hbefore : ∀ j k, k ∈ T j → k < pivot j)
    (C : β → PrincipalCoordinateChain n (m+1)) (γ : β → Fin (m+1) → ι)
    (κ : β → Fin r) (E : ℕ → (Fin n → ℕ) → Prop)
    (θ δ t : ℝ) (hθ : 0 < θ) (ht : 0 ≤ t)
    (halignmass : ∀ᶠ w in (U : Filter ℕ), δ ≤ event (selectedPrincipalRawMass e F w) (E w))
    (hselect : ∀ᶠ w in (U : Filter ℕ), ∀ x ∈ (selectedPrincipalRawMass e F w).support,
      E w x →
      (∀ j : α, ¬ (let z : ℤ := (principalSubsetProduct (insert (pivot j) (T j)) x : ℤ)
        0 < z ∧ χ (principalBlockCoefficient M e (T j) (pivot j) (a (index j)) w * z.toNat) =
          color (index j) ∧ S (T j) (pivot j) (index j) w z ≤ 2*θ)) →
      ∃ q : β, t ≤ principalBoundedCountIntegrand (C q) M e (fun i => a (γ q i)) w
        (fun i => S ((C q).tail i) ((C q).pivot i) (γ q i) w)
        (principalColorProductMask (C q) M e (fun i => a (γ q i)) χ (κ q) w)
        (fun i => ((C q).sampleProducts x i : ℤ)))
    (hbudget : 0 < t * (δ - (Fintype.card α : ℝ) * (3*θ + cap)) -
      (Fintype.card β : ℝ) * η) :
    ∀ᶠ w in (U : Filter ℕ), 0 < ∑ q : β,
      principalWeightedColorCount (C q) M e F (fun i => a (γ q i)) χ
        (fun i => color (γ q i)) (κ q) w := by
  let cal (j : α) := principalCalibrationProbability M e F (T j) (pivot j)
    (a (index j)) χ (color (index j)) (S (T j) (pivot j) (index j)) θ
  let B (q : β) := principalModelColorCount (C q) M e F (fun i => a (γ q i)) χ
    (κ q) (fun i => S ((C q).tail i) ((C q).pivot i) (γ q i))
  let I (q : β) := principalWeightedColorCount (C q) M e F (fun i => a (γ q i)) χ
    (fun i => color (γ q i)) (κ q)
  let clim (j : α) := limUnder (U : Filter ℕ) (cal j)
  let Blim (q : β) := limUnder (U : Filter ℕ) (B q)
  let Ilim (q : β) := limUnder (U : Filter ℕ) (I q)
  have hcal (j : α) : Tendsto (cal j) (U : Filter ℕ) (𝓝 (clim j)) ∧
      clim j ≤ 3*θ + cap := by
    have h := hdata.calibration (T j) (pivot j) (index j) (hT j) (hbefore j) θ hθ
    exact ⟨h.1, h.2.2⟩
  have hBT (q : β) : Tendsto (B q) (U : Filter ℕ) (𝓝 (Blim q)) :=
    (hdata.model_counts (C q) (γ q) (κ q)).1
  have hIT (q : β) : Tendsto (I q) (U : Filter ℕ) (𝓝 (Ilim q)) :=
    (hdata.weighted_counts (C q) (γ q) (κ q)).2.1
  have herror (q : β) : |Ilim q - Blim q| ≤ η :=
    (hdata.weighted_counts (C q) (γ q) (κ q)).2.2.2.2
  have hcalT := tendsto_finsetSum Finset.univ (fun j _ => (hcal j).1)
  have hmodelT := tendsto_finsetSum Finset.univ (fun q _ => hBT q)
  have hactualT := tendsto_finsetSum Finset.univ (fun q _ => hIT q)
  have hlow : ∀ᶠ w in (U : Filter ℕ), t * (δ - ∑ j, cal j w) ≤ ∑ q, B q w := by
    filter_upwards [hμ, halignmass, hselect] with w hmw hemw hselw
    let bad (j : α) (x : Fin n → ℕ) : Prop :=
      let z : ℤ := (principalSubsetProduct (insert (pivot j) (T j)) x : ℤ)
      0 < z ∧ χ (principalBlockCoefficient M e (T j) (pivot j) (a (index j)) w * z.toNat) =
        color (index j) ∧ S (T j) (pivot j) (index j) w z ≤ 2*θ
    let f (q : β) (x : Fin n → ℕ) : ℝ :=
      principalBoundedCountIntegrand (C q) M e (fun i => a (γ q i)) w
        (fun i => S ((C q).tail i) ((C q).pivot i) (γ q i) w)
        (principalColorProductMask (C q) M e (fun i => a (γ q i)) χ (κ q) w)
        (fun i => ((C q).sampleProducts x i : ℤ))
    have hf (q : β) (x : Fin n → ℕ) : 0 ≤ f q x :=
      (principalBoundedColorIntegrand_Icc (C q) e _ χ (κ q) w _
        (fun i y => hS _ _ _ w y) _).1
    have hh := positivePrincipalSum_model_lower_bound (selectedPrincipalRawMass e F w)
      hmw (E w) bad f hf t ht hselw
    exact (mul_le_mul_of_nonneg_left (sub_le_sub_right hemw _) ht).trans hh
  have hl := le_of_tendsto_of_tendsto ((tendsto_const_nhds.sub hcalT).const_mul t) hmodelT hlow
  have hc : (∑ j, clim j) ≤ (Fintype.card α : ℝ) * (3*θ + cap) := by
    calc
      _ ≤ ∑ _j : α, (3*θ + cap) := Finset.sum_le_sum (fun j _ => (hcal j).2)
      _ = _ := by simp; ring
  have hb : t * (δ - (Fintype.card α : ℝ) * (3*θ + cap)) ≤ ∑ q, Blim q :=
    (mul_le_mul_of_nonneg_left (sub_le_sub_left hc δ) ht).trans hl
  have hi := positivePrincipalSum_error_transfer Ilim Blim η _ herror hb
  have hpositive : 0 < ∑ q, Ilim q := hbudget.trans_le hi
  exact hactualT.eventually (Ioi_mem_nhds hpositive)

end Hindman168
