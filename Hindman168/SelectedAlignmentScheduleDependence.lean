import Hindman168.SelectedAlignmentSchedulePaths
import Hindman168.SelectedAlignmentRouteNumericalPivot

namespace Hindman168
open scoped Classical

/-- Every first-success decision in a prefix only uses the predicates
queried by that prefix. The future budget is kept exactly as in the full schedule. -/
theorem selected_alignment_schedule_prefix_congr {n : ℕ} {α : Type*}
    (q₀ : ℕ) (Good : SelectedAlignmentScheduleSuccess n α)
    (schedule : List (AlignmentPlannedPivot n)) (b : Fin n → ℚ)
    (x y : α) (k : ℕ) (hk : k ≤ schedule.length)
    (h : ∀ earlier p later, schedule = earlier ++ p :: later → earlier.length < k →
      ∀ c route, route ∈ principalPivotRoutes p.plan →
        (Good p later c route x ↔ Good p later c route y)) :
    selectedAlignmentSchedulePrefixState q₀ Good schedule b x k =
      selectedAlignmentSchedulePrefixState q₀ Good schedule b y k := by
  induction schedule generalizing b k with
  | nil =>
    have hk0 : k = 0 := by simpa using hk
    subst k
    rfl
  | cons p later ih =>
    cases k with
    | zero => rfl
    | succ k =>
      rw [selected_alignment_schedule_prefix_cons, selected_alignment_schedule_prefix_cons]
      rw [selected_alignment_schedule_advance_congr q₀ Good p later b x y
        (h [] p later rfl (by simp) b)]
      congr 1
      funext c
      apply ih c k (by simpa using hk)
      intro earlier p' later' hs hlen d route hr
      exact h (p :: earlier) p' later' (by simpa using congrArg (List.cons p) hs)
        (by simpa using hlen) d route hr

/-- A native request at pivot i depends only on raw coordinates through i. -/
theorem selected_alignment_native_request_congr {n M r : ℕ}
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (F : MasterParameterFamily)
    (A : Finset ℚ)
    (S : Finset (Fin n) → Fin n → ScaleColorIndex A r → ℕ → ℤ → ℝ)
    (q₀ w : ℕ) (i : Fin n) (x y : Fin M → ℕ)
    (hxy : ∀ j ≤ principalAlignmentEmbedding e heM i, x j = y j)
    (b : Fin n → ℚ) (θ : ℝ) (request : AlignmentPivotRequest n i) :
    principalThresholdRequestHolds q₀ b (principalNativeLetter (principalAlignmentEmbedding e heM))
      (principalNativeScaleObservation e heM F A S q₀ w x i) θ 1 request ↔
    principalThresholdRequestHolds q₀ b (principalNativeLetter (principalAlignmentEmbedding e heM))
      (principalNativeScaleObservation e heM F A S q₀ w y i) θ 1 request := by
  have hi : i ∉ request.tail := fun hi => (lt_irrefl i) (request.before i hi)
  have hB : ∀ j ∈ (insert i request.tail).erase i, j < i := by
    simpa only [Finset.erase_insert hi] using request.before
  have hearlier : ∀ j < principalAlignmentEmbedding e heM i, x j = y j :=
    fun j hj => hxy j hj.le
  have heq : ∀ a u c,
      principalNativeScaleObservation e heM F A S q₀ w x i (insert i request.tail) a u c =
      principalNativeScaleObservation e heM F A S q₀ w y i (insert i request.tail) a u c := by
    intro a u c
    rw [← selected_alignment_signed_observation_eq_native_scale,
      ← selected_alignment_signed_observation_eq_native_scale]
    have hcurrent : x (selectedPrincipalIndex e heM i) = y (selectedPrincipalIndex e heM i) :=
      hxy _ le_rfl
    rw [hcurrent]
    exact selected_alignment_signed_observation_earlier_eq _ i F q₀ w x y hearlier
      _ _ _ hB a u c
  unfold principalThresholdRequestHolds
  simp only [heq]

noncomputable def selectedAlignmentScheduleNativeSuccess {n M r : ℕ}
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (F : MasterParameterFamily)
    (A : Finset ℚ)
    (S : Finset (Fin n) → Fin n → ScaleColorIndex A r → ℕ → ℤ → ℝ)
    (q₀ : ℕ) (θ : ℝ) (w : ℕ) : SelectedAlignmentScheduleSuccess n (Fin M → ℕ) :=
  fun p later b route x => ∀ request ∈ selectedAlignmentScheduleRequests later p.pivot,
    principalThresholdRequestHolds q₀ (alignmentJointRouteArithmetic q₀ p.plan b route).1
      (principalNativeLetter (principalAlignmentEmbedding e heM))
      (principalNativeScaleObservation e heM F A S q₀ w x p.pivot) θ 1 request

theorem selected_alignment_schedule_native_success_congr {n M r : ℕ}
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (F : MasterParameterFamily)
    (A : Finset ℚ)
    (S : Finset (Fin n) → Fin n → ScaleColorIndex A r → ℕ → ℤ → ℝ)
    (q₀ : ℕ) (θ : ℝ) (w : ℕ) (p : AlignmentPlannedPivot n)
    (later : List (AlignmentPlannedPivot n)) (b : Fin n → ℚ)
    (route : List (ℕ × List (AlignmentAddingPair n p.pivot × ℚ)))
    (x y : Fin M → ℕ)
    (hxy : ∀ j ≤ principalAlignmentEmbedding e heM p.pivot, x j = y j) :
    selectedAlignmentScheduleNativeSuccess e heM F A S q₀ θ w p later b route x ↔
      selectedAlignmentScheduleNativeSuccess e heM F A S q₀ θ w p later b route y := by
  unfold selectedAlignmentScheduleNativeSuccess
  exact forall_congr' (fun request => forall_congr' (fun _ =>
    selected_alignment_native_request_congr e heM F A S q₀ w p.pivot x y hxy _ θ request))

/-- The numerical pivot at an arbitrary schedule position is exactly that
position in the fixed increasing pivot order. -/
theorem selected_alignment_schedule_position {n r s : ℕ}
    (earlier : List (AlignmentPlannedPivot n)) (p : AlignmentPlannedPivot n)
    (later : List (AlignmentPlannedPivot n))
    (hs : selectedAlignmentSchedule n r s = earlier ++ p :: later) :
    p.pivot.val = earlier.length := by
  have h := selected_alignment_schedule_cover n r s
  rw [hs, List.map_append, List.map_cons] at h
  have hlen : earlier.length < n := by
    have hh := congrArg List.length h
    simp only [List.length_append, List.length_map, List.length_cons, List.length_finRange] at hh
    omega
  have hh := congrArg (fun l : List (Fin n) => l[earlier.length]?) h
  simpa [List.getElem?_append, hlen, List.getElem?_eq_getElem] using congrArg (Option.map Fin.val) hh

/-- The actual first-success prefix event is unaffected by changing the
current or any later coordinate, exactly as required by pivot conditioning. -/
theorem selected_alignment_schedule_native_prefix_congr {n M r s : ℕ}
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (F : MasterParameterFamily)
    (A : Finset ℚ)
    (S : Finset (Fin n) → Fin n → ScaleColorIndex A r → ℕ → ℤ → ℝ)
    (q₀ : ℕ) (θ : ℝ) (w : ℕ) (i : Fin n) (x y : Fin M → ℕ)
    (hxy : ∀ j < principalAlignmentEmbedding e heM i, x j = y j) :
    selectedAlignmentSchedulePrefixState q₀ (selectedAlignmentScheduleNativeSuccess e heM F A S q₀ θ w)
      (selectedAlignmentSchedule n r s) (fun _ => 1) x i.val =
    selectedAlignmentSchedulePrefixState q₀ (selectedAlignmentScheduleNativeSuccess e heM F A S q₀ θ w)
      (selectedAlignmentSchedule n r s) (fun _ => 1) y i.val := by
  apply selected_alignment_schedule_prefix_congr
  · rw [selected_alignment_schedule_length]
    exact i.isLt.le
  · intro earlier p later hs hlen b route _
    apply selected_alignment_schedule_native_success_congr
    intro j hj
    apply hxy j
    apply lt_of_le_of_lt hj
    apply (principalAlignmentEmbedding e heM).strictMono
    show p.pivot.val < i.val
    rw [selected_alignment_schedule_position earlier p later hs]
    exact hlen

end Hindman168
