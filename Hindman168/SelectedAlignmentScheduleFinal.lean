import Hindman168.SelectedAlignmentScheduleNativeMass
import Hindman168.PositivePrincipalSumFutureFinal

/-! The actual first-success path mass reaches the final selected alignment
predicate. Finite scales, final tuples, denominator, and positive mass budget
are fixed from n, r, s alone, before models and thresholds. -/
namespace Hindman168
open Filter FiniteMass
open scoped Classical Topology BigOperators
universe u

theorem selected_alignment_schedule_prefix_at {n : ℕ} {α : Type*}
    (q₀ : ℕ) (Good : SelectedAlignmentScheduleSuccess n α)
    (schedule : List (AlignmentPlannedPivot n)) (b : Fin n → ℚ) (x : α) (k : ℕ) :
    selectedAlignmentSchedulePrefixState q₀ Good schedule b x k =
      selectedAlignmentSchedulePrefixState q₀ (fun p later c route (_ : Unit) => Good p later c route x)
        schedule b () k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [selectedAlignmentSchedulePrefixState, ih]
    congr 1

/-- A complete successful deterministic prefix gives final native requests
on the same raw sample, with the final scale membership deduced. -/
theorem selected_alignment_schedule_path_native_event {n M r s : ℕ}
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (F : MasterParameterFamily)
    (S : Finset (Fin n) → Fin n → ScaleColorIndex (selectedAlignmentScheduleScales n r s) r → ℕ → ℤ → ℝ)
    (θ : ℝ) (w : ℕ) (x : Fin M → ℕ)
    (h : ∃ b, selectedAlignmentSchedulePathEvent n r s (selectedAlignmentScheduleClearing n r s)
      (selectedAlignmentScheduleNativeSuccess e heM F (selectedAlignmentScheduleScales n r s) S
        (selectedAlignmentScheduleClearing n r s) θ) n b w x) :
    PrincipalNativeThresholdEvent e heM F (selectedAlignmentScheduleFinal n r s)
      (selectedAlignmentScheduleScales n r s) (selected_alignment_schedule_scales_closed n r s) S
      (selectedAlignmentScheduleClearing n r s) θ w x := by
  obtain ⟨b, hb⟩ := h
  unfold selectedAlignmentSchedulePathEvent at hb
  rw [selected_alignment_schedule_prefix_at] at hb
  have hlen := selected_alignment_schedule_length n r s
  exact principal_native_threshold_path_event e heM F (selectedAlignmentSchedule n r s)
    (selected_alignment_schedule_cover n r s) (fun _ => 1) _
    (selected_alignment_schedule_scales_closed n r s) S _ w x θ b.val
    (selected_alignment_schedule_prefix_threshold_path _ _ _ _ _ _ θ _ _ _ _ (by simpa only [hlen, selectedAlignmentScheduleNativeSuccess] using hb))

/-- The actual original-raw native threshold mass has the preselected
positive lower bound, with no compactness, local-mass, or path premise. -/
theorem selected_alignment_schedule_native_liminf
    {d n M r s : ℕ} {Poly : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M (selectedAlignmentScheduleScales n r s) Poly F)
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M)
    (S : Finset (Fin n) → Fin n → ScaleColorIndex (selectedAlignmentScheduleScales n r s) r → ℕ → ℤ → ℝ)
    (hS : ∀ T i γ, NativePieceRepresented.{u} s F
      (fun _ => (⟨energyPadding e i,heM _⟩ : Fin M)) (S T i γ))
    (θ : ℝ) (hθ : 0 < θ) :
    selectedAlignmentScheduleDelta n r s ≤
      atTop.liminf (fun w => event (globalRawMass (F.cutoff w) (primorial w) M)
        (PrincipalNativeThresholdEvent e heM F (selectedAlignmentScheduleFinal n r s)
          (selectedAlignmentScheduleScales n r s) (selected_alignment_schedule_scales_closed n r s) S
          (selectedAlignmentScheduleClearing n r s) θ w)) := by
  apply (selected_alignment_schedule_native_path_liminf hF e heM S hS θ hθ).trans
  apply Filter.liminf_le_liminf
  · filter_upwards [alignmentGlobalRawMass_geometry hF] with w hw
    apply event_mono _ hw.1
    intro x hx
    exact selected_alignment_schedule_path_native_event e heM F S θ w x hx
  · apply isBoundedUnder_of_eventually_ge (a := (0 : ℝ))
    exact (alignmentGlobalRawMass_geometry hF).mono (fun _ hw => event_nonneg _ _ hw.1)
  · apply isCoboundedUnder_ge_of_eventually_le atTop (x := (1 : ℝ))
    exact (alignmentGlobalRawMass_geometry hF).mono (fun _ hw =>
      (event_le_total _ _ hw.1).trans_eq hw.2.1)

/-- The final §8.5 positive-mass alignment theorem for the actual represented
finite prediction family. All finite choices precede F, e, S and theta. -/
theorem selected_alignment_schedule_alignment_liminf
    {d n M r s : ℕ} {Poly : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M (selectedAlignmentScheduleScales n r s) Poly F)
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M)
    (S : Finset (Fin n) → Fin n → ScaleColorIndex (selectedAlignmentScheduleScales n r s) r → ℕ → ℤ → ℝ)
    (hS : ∀ T i γ, NativePieceRepresented.{u} s F
      (fun _ => (⟨energyPadding e i,heM _⟩ : Fin M)) (S T i γ))
    (θ : ℝ) (hθ : 0 < θ) :
    selectedAlignmentScheduleDelta n r s ≤
      atTop.liminf (fun w => event (selectedPrincipalRawMass e F w)
        (PrincipalSumAlignmentEvent M e (selectedAlignmentScheduleFinal n r s)
          (selectedAlignmentScheduleScales n r s) (selected_alignment_schedule_scales_closed n r s) S θ w)) := by
  exact (selected_alignment_schedule_native_liminf hF e heM S hS θ hθ).trans
    (principal_native_threshold_liminf_le_alignment hF e heM (selectedAlignmentScheduleFinal n r s)
      (selected_alignment_schedule_scales_closed n r s) (selected_alignment_schedule_final_positive n r s)
      (selectedAlignmentScheduleClearing n r s) (selected_alignment_schedule_clearing_pos n r s)
      (selected_alignment_schedule_final_denominators n r s) S θ hθ.le)

/-- A self-contained pre-model finite-data package for the final deduction. -/
theorem selected_alignment_finite_data_mass (n r s : ℕ) :
    ∃ (B : Finset (Fin n → ℚ)) (A : Finset ℚ),
      B.Nonempty ∧ (∀ b ∈ B, ∀ j, 0 < b j) ∧ (∀ a ∈ A, 0 < a) ∧
      ∃ hclosed : FiniteScaleClosure B A, ∃ δ : ℝ, 0 < δ ∧
      ∀ (d M : ℕ) (Poly : Finset (MvPolynomial (Fin d) ℤ)) (F : MasterParameterFamily),
      MasterParameterConditions M A Poly F →
      ∀ (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M)
        (S : Finset (Fin n) → Fin n → ScaleColorIndex A r → ℕ → ℤ → ℝ),
      (∀ T i γ, NativePieceRepresented.{u} s F
        (fun _ => (⟨energyPadding e i,heM _⟩ : Fin M)) (S T i γ)) →
      ∀ θ : ℝ, 0 < θ → δ ≤
        atTop.liminf (fun w => event (selectedPrincipalRawMass e F w)
          (PrincipalSumAlignmentEvent M e B A hclosed S θ w)) := by
  refine ⟨selectedAlignmentScheduleFinal n r s, selectedAlignmentScheduleScales n r s,
    selected_alignment_schedule_final_nonempty (selected_alignment_schedule_exact n r s),
    selected_alignment_schedule_final_positive n r s, selected_alignment_schedule_scales_positive n r s,
    selected_alignment_schedule_scales_closed n r s, selectedAlignmentScheduleDelta n r s,
    selected_alignment_schedule_delta_pos n r s, ?_⟩
  intro d M Poly F hF e heM S hS θ hθ
  exact selected_alignment_schedule_alignment_liminf hF e heM S hS θ hθ

end Hindman168
