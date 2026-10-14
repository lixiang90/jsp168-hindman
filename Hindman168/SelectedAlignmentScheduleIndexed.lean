import Hindman168.SelectedAlignmentScheduleBudgets
import Hindman168.PositivePrincipalSumPivotIteration
import Mathlib.Data.List.TakeDrop

namespace Hindman168
open scoped Classical BigOperators

noncomputable def selectedAlignmentScheduleEntry (n r s : ℕ) (i : Fin n) : AlignmentPlannedPivot n :=
  (selectedAlignmentSchedule n r s)[i.val]'(by rw [selected_alignment_schedule_length]; exact i.isLt)

noncomputable def selectedAlignmentScheduleBefore (n r s : ℕ) (i : Fin n) :
    List (AlignmentPlannedPivot n) := (selectedAlignmentSchedule n r s).take i.val

noncomputable def selectedAlignmentScheduleAfter (n r s : ℕ) (i : Fin n) :
    List (AlignmentPlannedPivot n) := (selectedAlignmentSchedule n r s).drop (i.val+1)

theorem selected_alignment_schedule_entry_pivot (n r s : ℕ) (i : Fin n) :
    (selectedAlignmentScheduleEntry n r s i).pivot = i := by
  have h := selected_alignment_schedule_cover n r s
  have hi : i.val < (selectedAlignmentSchedule n r s).length := by
    rw [selected_alignment_schedule_length]; exact i.isLt
  have he := List.getElem_map AlignmentPlannedPivot.pivot (l := selectedAlignmentSchedule n r s)
    (i := i.val) (h := by simpa using hi)
  simpa [h, selectedAlignmentScheduleEntry, List.getElem_finRange] using he.symm

theorem selected_alignment_schedule_entry_mem (n r s : ℕ) (i : Fin n) :
    selectedAlignmentScheduleEntry n r s i ∈ selectedAlignmentSchedule n r s :=
  List.getElem_mem _

theorem selected_alignment_schedule_decompose (n r s : ℕ) (i : Fin n) :
    selectedAlignmentSchedule n r s = selectedAlignmentScheduleBefore n r s i ++
      selectedAlignmentScheduleEntry n r s i :: selectedAlignmentScheduleAfter n r s i := by
  unfold selectedAlignmentScheduleBefore selectedAlignmentScheduleEntry selectedAlignmentScheduleAfter
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

theorem selected_alignment_schedule_entry_plan (n r s : ℕ) (i : Fin n) :
    (selectedAlignmentScheduleEntry n r s i).plan =
      selectedAlignmentCosetPlan (κ := Fin r) s
        (selectedAlignmentScheduleRequests (selectedAlignmentScheduleAfter n r s i)
          (selectedAlignmentScheduleEntry n r s i).pivot) := by
  apply SelectedAlignmentScheduleExact.plan (selectedAlignmentScheduleBefore n r s i)
  rw [← selected_alignment_schedule_decompose]
  exact selected_alignment_schedule_exact n r s

noncomputable def selectedAlignmentScheduleInput (n r s : ℕ) (i : Fin n) : Finset (Fin n → ℚ) :=
  selectedAlignmentScheduleIncoming (selectedAlignmentScheduleBefore n r s i) {fun _ => 1}

theorem selected_alignment_schedule_input_nonempty (n r s : ℕ) (i : Fin n) :
    (selectedAlignmentScheduleInput n r s i).Nonempty :=
  selected_alignment_schedule_incoming_nonempty _ _ (Finset.singleton_nonempty _)
    (fun p hp => (selected_alignment_schedule_exact n r s).routes_nonempty p (List.mem_of_mem_take hp))

theorem selected_alignment_schedule_input_positive (n r s : ℕ) (i : Fin n) :
    ∀ b ∈ selectedAlignmentScheduleInput n r s i, ∀ j, 0 < b j :=
  selected_alignment_schedule_incoming_positive _ _
    (by intro b hb; obtain rfl := Finset.mem_singleton.mp hb; exact fun _ => zero_lt_one)
    (fun p hp => (selected_alignment_schedule_exact n r s).positive p (List.mem_of_mem_take hp))

theorem selected_alignment_schedule_input_subset (n r s : ℕ) (i : Fin n) :
    selectedAlignmentScheduleInput n r s i ⊆ selectedAlignmentScheduleStates n r s := by
  intro b hb
  apply Finset.mem_union_left
  rw [selected_alignment_schedule_decompose n r s i]
  exact selected_alignment_schedule_prefix_incoming _ _ _ hb

noncomputable def selectedAlignmentScheduleRouteCount (n r s : ℕ) (i : Fin n) : ℕ :=
  (principalPivotRoutes (selectedAlignmentScheduleEntry n r s i).plan).card

theorem selected_alignment_schedule_route_count_pos (n r s : ℕ) (i : Fin n) :
    0 < selectedAlignmentScheduleRouteCount n r s i :=
  Finset.card_pos.mpr ((selected_alignment_schedule_exact n r s).routes_nonempty _
    (selected_alignment_schedule_entry_mem n r s i))

noncomputable def selectedAlignmentScheduleRouteCountNat (n r s k : ℕ) : ℕ :=
  if hk : k < n then selectedAlignmentScheduleRouteCount n r s ⟨k,hk⟩ else 1

noncomputable def selectedAlignmentScheduleDelta (n r s : ℕ) : ℝ :=
  principalPivotDelta (selectedAlignmentScheduleRouteCountNat n r s)
    (selectedAlignmentScheduleRouteCountNat n r s) n

theorem selected_alignment_schedule_delta_pos (n r s : ℕ) :
    0 < selectedAlignmentScheduleDelta n r s := by
  have hQ : ∀ k < n, 0 < selectedAlignmentScheduleRouteCountNat n r s k := by
    intro k hk
    simp only [selectedAlignmentScheduleRouteCountNat, dif_pos hk]
    exact selected_alignment_schedule_route_count_pos n r s ⟨k,hk⟩
  exact principal_pivot_delta_pos _ _ n hQ hQ

theorem selected_alignment_schedule_delta_formula (n r s : ℕ) :
    selectedAlignmentScheduleDelta n r s =
      ∏ i ∈ Finset.range n, 1 / (3 * (selectedAlignmentScheduleRouteCountNat n r s i : ℝ) *
        (selectedAlignmentScheduleRouteCountNat n r s i : ℝ)) := rfl

end Hindman168
