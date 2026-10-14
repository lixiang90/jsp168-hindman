import Hindman168.SelectedAlignmentSchedulePaths

namespace Hindman168
open Filter FiniteMass
open scoped Classical Topology BigOperators

theorem selected_alignment_schedule_drop (n r s : ℕ) (i : Fin n) :
    (selectedAlignmentSchedule n r s).drop i.val =
      selectedAlignmentScheduleEntry n r s i :: selectedAlignmentScheduleAfter n r s i :=
  List.drop_eq_getElem_cons _

theorem selected_alignment_schedule_prefix_global_mem {n r s : ℕ} {α : Type*}
    (q₀ : ℕ) (Good : SelectedAlignmentScheduleSuccess n α) (x : α)
    (k : ℕ) (hk : k ≤ n) (b : Fin n → ℚ)
    (h : selectedAlignmentSchedulePrefixState q₀ Good (selectedAlignmentSchedule n r s)
      (fun _ => 1) x k = some b) : b ∈ selectedAlignmentScheduleStates n r s := by
  have hb := selected_alignment_schedule_prefix_mem q₀ Good (selectedAlignmentSchedule n r s)
    {fun _ => 1} (fun _ => 1) (Finset.mem_singleton_self _) x k
    (by rw [selected_alignment_schedule_length]; exact hk) b h
  apply Finset.mem_union_left
  have hh := selected_alignment_schedule_prefix_incoming
    ((selectedAlignmentSchedule n r s).take k) ((selectedAlignmentSchedule n r s).drop k) _ hb
  simpa only [List.take_append_drop] using hh

noncomputable def selectedAlignmentSchedulePathEvent {α : Type*}
    (n r s q₀ : ℕ) (Good : ℕ → SelectedAlignmentScheduleSuccess n α)
    (k : ℕ) (b : selectedAlignmentScheduleStates n r s) (w : ℕ) (x : α) : Prop :=
  selectedAlignmentSchedulePrefixState q₀ (Good w) (selectedAlignmentSchedule n r s)
    (fun _ => 1) x k = some b.val

noncomputable def selectedAlignmentScheduleExtensionEvent {α : Type*}
    (n r s q₀ : ℕ) (Good : ℕ → SelectedAlignmentScheduleSuccess n α)
    (k : ℕ) (b : selectedAlignmentScheduleStates n r s) (w : ℕ) (x : α) : Prop :=
  selectedAlignmentSchedulePathEvent n r s q₀ Good k b w x ∧
    ∃ c, selectedAlignmentScheduleAdvance q₀ (Good w)
      ((selectedAlignmentSchedule n r s).drop k) b.val x = some c

theorem selected_alignment_schedule_path_disjoint {α : Type*}
    (n r s q₀ : ℕ) (Good : ℕ → SelectedAlignmentScheduleSuccess n α)
    (k w : ℕ) (x : α) (b c : selectedAlignmentScheduleStates n r s)
    (hb : selectedAlignmentSchedulePathEvent n r s q₀ Good k b w x)
    (hc : selectedAlignmentSchedulePathEvent n r s q₀ Good k c w x) : b = c := by
  apply Subtype.ext
  exact Option.some.inj (hb.symm.trans hc)

theorem selected_alignment_schedule_path_next {α : Type*}
    (n r s q₀ : ℕ) (Good : ℕ → SelectedAlignmentScheduleSuccess n α)
    (k : ℕ) (hk : k < n) (w : ℕ) (x : α) :
    (∃ b, selectedAlignmentScheduleExtensionEvent n r s q₀ Good k b w x) ↔
      ∃ c, selectedAlignmentSchedulePathEvent n r s q₀ Good (k+1) c w x := by
  constructor
  · rintro ⟨b, hb, c, hc⟩
    have hnext : selectedAlignmentSchedulePrefixState q₀ (Good w) (selectedAlignmentSchedule n r s)
        (fun _ => 1) x (k+1) = some c := by
      rw [selectedAlignmentSchedulePrefixState, hb, Option.bind_some]
      exact hc
    exact ⟨⟨c,selected_alignment_schedule_prefix_global_mem q₀ (Good w) x (k+1)
      (by omega) c hnext⟩,hnext⟩
  · rintro ⟨c, hc⟩
    obtain ⟨b, hb, hc⟩ := Option.bind_eq_some_iff.mp hc
    exact ⟨⟨b,selected_alignment_schedule_prefix_global_mem q₀ (Good w) x k hk.le b hb⟩,
      hb, c.val, hc⟩

theorem selected_alignment_schedule_extension_iff {α : Type*}
    (n r s q₀ : ℕ) (Good : ℕ → SelectedAlignmentScheduleSuccess n α)
    (i : Fin n) (b : selectedAlignmentScheduleStates n r s) (w : ℕ) (x : α) :
    selectedAlignmentScheduleExtensionEvent n r s q₀ Good i.val b w x ↔
      selectedAlignmentSchedulePathEvent n r s q₀ Good i.val b w x ∧
      ∃ route ∈ principalPivotRoutes (selectedAlignmentScheduleEntry n r s i).plan,
        Good w (selectedAlignmentScheduleEntry n r s i) (selectedAlignmentScheduleAfter n r s i)
          b.val route x := by
  unfold selectedAlignmentScheduleExtensionEvent
  rw [selected_alignment_schedule_drop, selected_alignment_schedule_advance_exists]

/-- The exact deterministic first-success partition converts the actual
per-state extension inequalities into the preselected product lower bound.
All finite state errors are retained and only then sent to zero. -/
theorem selected_alignment_schedule_path_mass_liminf {α : Type*}
    (n r s q₀ : ℕ) (Good : ℕ → SelectedAlignmentScheduleSuccess n α)
    (μ : ℕ → Mass α)
    (hμ : ∀ᶠ w in atTop, (∀ x, 0 ≤ μ w x) ∧ total (μ w) = 1)
    (err : Fin n → selectedAlignmentScheduleStates n r s → ℕ → ℝ)
    (herr : ∀ i b, Tendsto (err i b) atTop (𝓝 0))
    (hstep : ∀ i : Fin n, ∀ᶠ w in atTop, ∀ b,
      (1 / (3 * (selectedAlignmentScheduleRouteCount n r s i : ℝ) *
        (selectedAlignmentScheduleRouteCount n r s i : ℝ))) *
          event (μ w) (selectedAlignmentSchedulePathEvent n r s q₀ Good i.val b w) - err i b w ≤
      event (μ w) (fun x => selectedAlignmentSchedulePathEvent n r s q₀ Good i.val b w x ∧
        ∃ route ∈ principalPivotRoutes (selectedAlignmentScheduleEntry n r s i).plan,
          Good w (selectedAlignmentScheduleEntry n r s i) (selectedAlignmentScheduleAfter n r s i)
            b.val route x)) :
    selectedAlignmentScheduleDelta n r s ≤
      atTop.liminf (fun w => event (μ w)
        (fun x => ∃ b, selectedAlignmentSchedulePathEvent n r s q₀ Good n b w x)) := by
  let c : ℕ → ℝ := fun k => 1 / (3 * (selectedAlignmentScheduleRouteCountNat n r s k : ℝ) *
    (selectedAlignmentScheduleRouteCountNat n r s k : ℝ))
  let errors : ℕ → selectedAlignmentScheduleStates n r s → ℕ → ℝ :=
    fun k b w => if hk : k < n then err ⟨k,hk⟩ b w else 0
  apply principal_finite_path_mass_liminf atTop μ
    (selectedAlignmentSchedulePathEvent n r s q₀ Good)
    (selectedAlignmentScheduleExtensionEvent n r s q₀ Good) c errors n hμ
  · intro k hk
    exact div_nonneg zero_le_one (by positivity)
  · apply Filter.Eventually.of_forall
    intro w x
    have hb : (fun _ : Fin n => (1 : ℚ)) ∈ selectedAlignmentScheduleStates n r s := by
      apply Finset.mem_union_left
      exact alignmentScheduleStates_contains_incoming _ _ (Finset.mem_singleton_self _)
    exact ⟨⟨_,hb⟩,rfl⟩
  · intro k hk
    exact Filter.Eventually.of_forall (fun w x b c => selected_alignment_schedule_path_disjoint
      n r s q₀ Good k w x b c)
  · intro k hk
    exact Filter.Eventually.of_forall (fun _ _ _ h => h.1)
  · intro k hk
    exact Filter.Eventually.of_forall (fun w x => selected_alignment_schedule_path_next
      n r s q₀ Good k hk w x)
  · intro k hk
    filter_upwards [hstep ⟨k,hk⟩] with w hw
    intro b
    have he : (selectedAlignmentScheduleExtensionEvent n r s q₀ Good k b w) =
        (fun x => selectedAlignmentSchedulePathEvent n r s q₀ Good k b w x ∧
          ∃ route ∈ principalPivotRoutes (selectedAlignmentScheduleEntry n r s ⟨k,hk⟩).plan,
            Good w (selectedAlignmentScheduleEntry n r s ⟨k,hk⟩)
              (selectedAlignmentScheduleAfter n r s ⟨k,hk⟩) b.val route x) :=
      funext (fun x => propext (selected_alignment_schedule_extension_iff n r s q₀ Good ⟨k,hk⟩ b w x))
    simpa only [c, errors, selectedAlignmentScheduleRouteCountNat, dif_pos hk, he] using hw b
  · intro k hk b
    simpa only [errors, dif_pos hk] using herr ⟨k,hk⟩ b

end Hindman168
