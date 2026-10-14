import Hindman168.SelectedAlignmentScheduleMass
import Hindman168.SelectedAlignmentScheduleDependence
import Hindman168.SelectedAlignmentFiniteScalePivotExtension

/-! The actual local native theorem supplies every finite-state error.
Thus no local mass, independence, or extension oracle remains in the global
first-success path lower bound. -/
namespace Hindman168
open Filter FiniteMass
open scoped Classical Topology BigOperators
universe u

/-- The selected schedule satisfies every input of the actual local theorem. -/
theorem selected_alignment_schedule_local_extension
    {d n M r s : ℕ} {Poly : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M (selectedAlignmentScheduleScales n r s) Poly F)
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (i : Fin n)
    (b : Fin n → ℚ) (hb : b ∈ selectedAlignmentScheduleInput n r s i)
    (S : Finset (Fin n) → Fin n → ScaleColorIndex (selectedAlignmentScheduleScales n r s) r → ℕ → ℤ → ℝ)
    (hS : ∀ T i γ, NativePieceRepresented.{u} s F
      (fun _ => (⟨energyPadding e i,heM _⟩ : Fin M)) (S T i γ))
    (θ : ℝ) (hθ : 0 < θ) :
    ∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧ ∀ᶠ w in atTop,
      ∀ E : (Fin M → ℕ) → Prop,
      (∀ x y, (∀ j < principalAlignmentEmbedding e heM i, x j = y j) → (E x ↔ E y)) →
      (1 / (3 * (selectedAlignmentScheduleRouteCount n r s i : ℝ) *
        (selectedAlignmentScheduleRouteCount n r s i : ℝ))) *
        event (globalRawMass (F.cutoff w) (primorial w) M) E - err w ≤
      event (globalRawMass (F.cutoff w) (primorial w) M)
        (fun x => E x ∧ ∃ route ∈ principalPivotRoutes (selectedAlignmentScheduleEntry n r s i).plan,
          selectedAlignmentScheduleNativeSuccess e heM F (selectedAlignmentScheduleScales n r s) S
            (selectedAlignmentScheduleClearing n r s) θ w (selectedAlignmentScheduleEntry n r s i)
              (selectedAlignmentScheduleAfter n r s i) b route x) := by
  let p := selectedAlignmentScheduleEntry n r s i
  let later := selectedAlignmentScheduleAfter n r s i
  let requests := selectedAlignmentScheduleRequests later p.pivot
  have hplan : p.plan = selectedAlignmentCosetPlan (κ := Fin r) s requests :=
    selected_alignment_schedule_entry_plan n r s i
  have hint := selected_alignment_schedule_denominators
    (selectedAlignmentScheduleBefore n r s i) p later (selected_alignment_schedule_decompose n r s i)
  have hscale : ∀ ν ∈ alignmentJointRouteFactorCatalogue (Fin r)
      (selectedAlignmentScheduleClearing n r s) (selectedAlignmentCosetPlan (κ := Fin r) s requests)
      (selectedAlignmentScheduleInput n r s i) requests, ν.2.1 ∈ selectedAlignmentScheduleScales n r s := by
    rw [← hplan]
    exact selected_alignment_schedule_catalogue_scale_mem _ p later
      (selected_alignment_schedule_decompose n r s i) _
  rw [hplan] at hint
  obtain ⟨err, he, hh⟩ := selected_alignment_finite_scale_pivot_extension hF e heM p.pivot requests
    (selected_alignment_schedule_requests_own later p.pivot) (selectedAlignmentScheduleInput n r s i)
    (selectedAlignmentScheduleClearing n r s) (selected_alignment_schedule_clearing_pos n r s)
    hint b hb (selected_alignment_schedule_input_positive n r s i b hb) S
    (fun T γ => hS T p.pivot γ) hscale θ hθ
  refine ⟨err, he, ?_⟩
  rw [← hplan] at hh
  simpa only [selectedAlignmentScheduleNativeSuccess, selectedAlignmentScheduleRouteCount,
    p, later, requests, selected_alignment_schedule_entry_pivot, pow_two, mul_assoc] using hh

/-- Every actual first-success state has its own vanishing error. Unreachable
states have the empty event and exactly zero error. -/
theorem selected_alignment_schedule_state_extension
    {d n M r s : ℕ} {Poly : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M (selectedAlignmentScheduleScales n r s) Poly F)
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (i : Fin n)
    (b : selectedAlignmentScheduleStates n r s)
    (S : Finset (Fin n) → Fin n → ScaleColorIndex (selectedAlignmentScheduleScales n r s) r → ℕ → ℤ → ℝ)
    (hS : ∀ T i γ, NativePieceRepresented.{u} s F
      (fun _ => (⟨energyPadding e i,heM _⟩ : Fin M)) (S T i γ))
    (θ : ℝ) (hθ : 0 < θ) :
    let Good := selectedAlignmentScheduleNativeSuccess e heM F (selectedAlignmentScheduleScales n r s) S
      (selectedAlignmentScheduleClearing n r s) θ
    let E := selectedAlignmentSchedulePathEvent n r s (selectedAlignmentScheduleClearing n r s) Good i.val b
    ∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧ ∀ᶠ w in atTop,
      (1 / (3 * (selectedAlignmentScheduleRouteCount n r s i : ℝ) *
        (selectedAlignmentScheduleRouteCount n r s i : ℝ))) *
        event (globalRawMass (F.cutoff w) (primorial w) M) (E w) - err w ≤
      event (globalRawMass (F.cutoff w) (primorial w) M)
        (fun x => E w x ∧ ∃ route ∈ principalPivotRoutes (selectedAlignmentScheduleEntry n r s i).plan,
          Good w (selectedAlignmentScheduleEntry n r s i) (selectedAlignmentScheduleAfter n r s i)
            b.val route x) := by
  dsimp only
  by_cases hb : b.val ∈ selectedAlignmentScheduleInput n r s i
  · obtain ⟨err, he, hh⟩ := selected_alignment_schedule_local_extension hF e heM i b.val hb S hS θ hθ
    refine ⟨err, he, ?_⟩
    filter_upwards [hh] with w hw
    apply hw
    intro x y hxy
    unfold selectedAlignmentSchedulePathEvent
    rw [selected_alignment_schedule_native_prefix_congr e heM F _ S _ θ w i x y hxy]
  · refine ⟨fun _ => 0, tendsto_const_nhds, Filter.Eventually.of_forall ?_⟩
    intro w
    have hfalse : ∀ x, ¬ selectedAlignmentSchedulePathEvent n r s (selectedAlignmentScheduleClearing n r s)
        (selectedAlignmentScheduleNativeSuccess e heM F (selectedAlignmentScheduleScales n r s) S
          (selectedAlignmentScheduleClearing n r s) θ) i.val b w x := by
      intro x hx
      apply hb
      exact selected_alignment_schedule_prefix_mem _ _ (selectedAlignmentSchedule n r s)
        {fun _ => 1} (fun _ => 1) (Finset.mem_singleton_self _) x i.val
        (by rw [selected_alignment_schedule_length]; exact i.isLt.le) b.val hx
    have he : selectedAlignmentSchedulePathEvent n r s (selectedAlignmentScheduleClearing n r s)
        (selectedAlignmentScheduleNativeSuccess e heM F (selectedAlignmentScheduleScales n r s) S
          (selectedAlignmentScheduleClearing n r s) θ) i.val b w = (fun _ => False) :=
      funext (fun x => propext ⟨fun h => hfalse x h, False.elim⟩)
    simp only [he, false_and, event_false, mul_zero, sub_zero, le_refl]

/-- Positive full-original-raw mass of successful complete paths, with
all local mass and path extension premises discharged. -/
theorem selected_alignment_schedule_native_path_liminf
    {d n M r s : ℕ} {Poly : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M (selectedAlignmentScheduleScales n r s) Poly F)
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M)
    (S : Finset (Fin n) → Fin n → ScaleColorIndex (selectedAlignmentScheduleScales n r s) r → ℕ → ℤ → ℝ)
    (hS : ∀ T i γ, NativePieceRepresented.{u} s F
      (fun _ => (⟨energyPadding e i,heM _⟩ : Fin M)) (S T i γ))
    (θ : ℝ) (hθ : 0 < θ) :
    selectedAlignmentScheduleDelta n r s ≤
      atTop.liminf (fun w => event (globalRawMass (F.cutoff w) (primorial w) M)
        (fun x => ∃ b, selectedAlignmentSchedulePathEvent n r s (selectedAlignmentScheduleClearing n r s)
          (selectedAlignmentScheduleNativeSuccess e heM F (selectedAlignmentScheduleScales n r s) S
            (selectedAlignmentScheduleClearing n r s) θ) n b w x)) := by
  have hlocal := fun i b => selected_alignment_schedule_state_extension hF e heM i b S hS θ hθ
  choose err herr hstep using hlocal
  apply selected_alignment_schedule_path_mass_liminf n r s _ _ _
    ((alignmentGlobalRawMass_geometry hF).mono (fun _ h => ⟨h.1,h.2.1⟩)) err herr
  intro i
  exact Filter.eventually_all.mpr (hstep i)

end Hindman168
