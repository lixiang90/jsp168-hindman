import Hindman168.PositivePrincipalSumNativePalette
import Hindman168.AlignmentRawCanonicalPieces
import Hindman168.FiniteSupportedEventComparison

/-! Simultaneous original finite-word requests imply the selected event.
The coefficient identities are discharged by admissibility at late stages. -/
namespace Hindman168
open Filter
open scoped BigOperators Classical

noncomputable def PrincipalNativeRequestEvent {n M r : ℕ}
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (F : MasterParameterFamily)
    (B : Finset (Fin n → ℚ)) (A : Finset ℚ) (_hclosed : FiniteScaleClosure B A)
    (S : Finset (Fin n) → Fin n → ScaleColorIndex A r → ℕ → ℤ → ℝ)
    (q₀ : ℕ) (θ : ℝ) (w : ℕ) (x : Fin M → ℕ) : Prop :=
  ∃ b : B, ∀ i : Fin n, ∀ request ∈ alignmentCanonicalRequests n i,
    alignmentPivotRequestHolds q₀ b.val
      (principalNativeLetter (principalAlignmentEmbedding e heM))
      (principalNativeScalePalette e heM F A S q₀ w x θ i) 1 request

theorem principal_native_requests_imply_alignment_event_eventually
    {d n M r : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin d) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions M A P F)
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M)
    (B : Finset (Fin n → ℚ)) (hclosed : FiniteScaleClosure B A)
    (hB : ∀ b ∈ B, ∀ k, 0 < b k) (q₀ : ℕ) (hq : 0 < q₀)
    (hclear : ∀ b ∈ B, ∀ i, ∀ p : AlignmentAddingPair n i,
      (q₀ : ℚ) * (finiteScaleBlockProduct b (alignmentPairSourceBlock p) /
        finiteScaleBlockProduct b (alignmentPairTargetBlock p)) ∈ (Int.castRingHom ℚ).range)
    (S : Finset (Fin n) → Fin n → ScaleColorIndex A r → ℕ → ℤ → ℝ)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    ∀ᶠ w in atTop, ∀ x : Fin M → ℕ, (∀ j, Nat.Coprime (x j) (primorial w)) →
      PrincipalNativeRequestEvent e heM F B A hclosed S q₀ θ w x →
      PrincipalSumAlignmentEvent M e B A hclosed S θ w
        (fun k => x (selectedPrincipalIndex e heM k)) := by
  filter_upwards [hF.principal_adding_ratios_exact_eventually e heM B hclosed,
    eventually_ge_atTop (q₀+1)] with w hr hw
  intro x hx hrequests
  obtain ⟨b, hb⟩ := hrequests
  refine ⟨b, ?_⟩
  intro κ
  exact principal_adding_alignment_of_native_requests hF e heM hq hw x hx b.val
    (hB b.val b.property) _ θ hθ (hclear b.val b.property)
    (fun i p => (hr b.val b.property i p).2.2.2)
    (fun i => principal_native_scale_requests_specialize e heM F B A hclosed S q₀ w x θ b i (hb i) κ)

/-- No mass is lost on discarding unused coordinates: the global native
request mass is bounded by the original selected alignment-event mass. -/
theorem principal_native_request_mass_le_alignment_eventually
    {d n M r : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin d) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions M A P F)
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M)
    (B : Finset (Fin n → ℚ)) (hclosed : FiniteScaleClosure B A)
    (hB : ∀ b ∈ B, ∀ k, 0 < b k) (q₀ : ℕ) (hq : 0 < q₀)
    (hclear : ∀ b ∈ B, ∀ i, ∀ p : AlignmentAddingPair n i,
      (q₀ : ℚ) * (finiteScaleBlockProduct b (alignmentPairSourceBlock p) /
        finiteScaleBlockProduct b (alignmentPairTargetBlock p)) ∈ (Int.castRingHom ℚ).range)
    (S : Finset (Fin n) → Fin n → ScaleColorIndex A r → ℕ → ℤ → ℝ)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    ∀ᶠ w in atTop,
      FiniteMass.event (globalRawMass (F.cutoff w) (primorial w) M)
        (PrincipalNativeRequestEvent e heM F B A hclosed S q₀ θ w) ≤
      FiniteMass.event (selectedPrincipalRawMass e F w)
        (PrincipalSumAlignmentEvent M e B A hclosed S θ w) := by
  filter_upwards [principal_native_requests_imply_alignment_event_eventually hF e heM B hclosed
    hB q₀ hq hclear S θ hθ, hF.selected_principal_raw_law e heM,
    hF.raw_cutoffs_valid] with w himp hlaw hcut
  rw [← hlaw, FiniteMass.event_map]
  apply FiniteMass.event_mono_on_support
  · apply FiniteMass.piMass_nonneg
    intro j y
    rw [rawMass_apply]
    exact harmonicWeight_nonneg (hcut j (Finset.mem_range.mpr j.isLt)).2.2 y
  · intro x hx hreq
    exact himp x (alignmentGlobalRawMass_support_coprime F w x hx) hreq

/-- The exact native request liminf transfers to the concrete event used
by the already proved final deduction. -/
theorem principal_native_request_liminf_le_alignment
    {d n M r : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin d) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions M A P F)
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M)
    (B : Finset (Fin n → ℚ)) (hclosed : FiniteScaleClosure B A)
    (hB : ∀ b ∈ B, ∀ k, 0 < b k) (q₀ : ℕ) (hq : 0 < q₀)
    (hclear : ∀ b ∈ B, ∀ i, ∀ p : AlignmentAddingPair n i,
      (q₀ : ℚ) * (finiteScaleBlockProduct b (alignmentPairSourceBlock p) /
        finiteScaleBlockProduct b (alignmentPairTargetBlock p)) ∈ (Int.castRingHom ℚ).range)
    (S : Finset (Fin n) → Fin n → ScaleColorIndex A r → ℕ → ℤ → ℝ)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    Filter.liminf (fun w => FiniteMass.event (globalRawMass (F.cutoff w) (primorial w) M)
      (PrincipalNativeRequestEvent e heM F B A hclosed S q₀ θ w)) atTop ≤
    Filter.liminf (fun w => FiniteMass.event (selectedPrincipalRawMass e F w)
      (PrincipalSumAlignmentEvent M e B A hclosed S θ w)) atTop := by
  refine Filter.liminf_le_liminf
    (principal_native_request_mass_le_alignment_eventually hF e heM B hclosed hB q₀ hq hclear S θ hθ) ?_ ?_
  · apply isBoundedUnder_of_eventually_ge (a := (0 : ℝ))
    apply hF.raw_cutoffs_valid.mono
    intro w hcut
    apply FiniteMass.event_nonneg
    apply FiniteMass.piMass_nonneg
    intro j y
    rw [rawMass_apply]
    exact harmonicWeight_nonneg (hcut j (Finset.mem_range.mpr j.isLt)).2.2 y
  · apply isCoboundedUnder_ge_of_eventually_le atTop (x := (1 : ℝ))
    apply (hF.selected_principal_raw_probability e heM).mono
    intro w hw
    exact (FiniteMass.event_le_total _ _ hw.1).trans_eq hw.2

end Hindman168
