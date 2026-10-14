import Hindman168.SelectedAlignmentRouteExtension
import Hindman168.SelectedAlignmentRouteRawKernel

namespace Hindman168
open Filter FiniteMass
open scoped Classical Topology ENNReal NNReal BigOperators
attribute [local instance] alignmentAddingPairFintype

theorem selected_alignment_route_full_raw_extension
    {d n M : ℕ} {κ : Type*} {A : Finset ℚ} {Poly : Finset (MvPolynomial (Fin d) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions M A Poly F)
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (i : Fin n) (q₀ : ℕ) (hq : 0 < q₀)
    (S : Finset (Fin n) → ℚ → κ → ℕ → ℤ → ℝ) (θ : ℝ)
    (plan : List (AlignmentPivotStage n i)) (incoming : Finset (Fin n → ℚ))
    (b : Fin n → ℚ) (hb : b ∈ incoming)
    (requests : List (AlignmentPivotRequest n i)) (hQ : 0 < (principalPivotRoutes plan).card)
    (hfailure : Tendsto (fun w => event (globalRawMass (F.cutoff w) (primorial w) M)
      (fun x => selectedAlignmentRawRouteCellMass F e heM i q₀ w x S θ plan b requests <
        ((3 / (4 * ((principalPivotRoutes plan).card : ℝ≥0)) : ℝ≥0) : ℝ≥0∞))) atTop (𝓝 0)) :
    ∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧ ∀ᶠ w in atTop,
      ∀ E : (Fin M → ℕ) → Prop,
      (∀ x y, (∀ j < principalAlignmentEmbedding e heM i, x j = y j) → (E x ↔ E y)) →
      (1 / (3 * ((principalPivotRoutes plan).card : ℝ)^2)) *
        event (globalRawMass (F.cutoff w) (primorial w) M) E - err w ≤
      event (globalRawMass (F.cutoff w) (primorial w) M)
        (fun x => E x ∧ selectedAlignmentSignedRouteSecured (principalAlignmentEmbedding e heM) i F q₀ w
          x S θ plan b requests (x (principalAlignmentEmbedding e heM i))) := by
  obtain ⟨err,he,hh⟩ := selected_alignment_route_pivot_extension hF e heM i q₀ hq S θ
    plan incoming b hb requests hQ hfailure
  refine ⟨err,he,?_⟩
  filter_upwards [hh,hF.raw_cutoffs_valid] with w hw hv E hE
  have h := hw (fun outside => E (insertPivotCoordinate (principalAlignmentEmbedding e heM i) outside 0))
  rw [selected_alignment_earlier_event_outside F w (principalAlignmentEmbedding e heM i)
    (hv (energyPrincipal e i) (Finset.mem_range.mpr (heM _))).2.2 E hE] at h
  have hpivot : (principalAlignmentEmbedding e heM i).val = energyPrincipal e i := rfl
  have hsec := selected_alignment_secured_event_original (principalAlignmentEmbedding e heM) i F q₀ w S θ plan b requests E hE
  simp only [hpivot] at hsec
  rw [hsec] at h
  exact h

end Hindman168
