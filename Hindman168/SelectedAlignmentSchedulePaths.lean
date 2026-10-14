import Hindman168.SelectedAlignmentScheduleIndexed
import Hindman168.PositivePrincipalSumFutureThresholdPaths

/-! Deterministic first-success refinement of the actual finite routes.
The partition state is the chosen scale tuple; paths reaching the same tuple
are grouped without losing disjointness or any earlier secured request. -/
namespace Hindman168
open scoped Classical

noncomputable def selectedAlignmentFirstRoute {n : ℕ} {i : Fin n}
    (plan : List (AlignmentPivotStage n i))
    (P : (principalPivotRoutes plan) → Prop) : Option (principalPivotRoutes plan) :=
  (principalFirstSuccess (Fintype.card (principalPivotRoutes plan))
    (fun j (_ : Unit) => P ((Fintype.equivFin (principalPivotRoutes plan)).symm j)) ()).map
      (Fintype.equivFin (principalPivotRoutes plan)).symm

theorem selected_alignment_first_route_spec {n : ℕ} {i : Fin n}
    (plan : List (AlignmentPivotStage n i)) (P : (principalPivotRoutes plan) → Prop)
    (route : principalPivotRoutes plan) (h : selectedAlignmentFirstRoute plan P = some route) :
    P route := by
  obtain ⟨j, hj, he⟩ := Option.map_eq_some_iff.mp h
  subst route
  exact (principal_first_success_spec _ _ () j hj).1

theorem selected_alignment_first_route_exists {n : ℕ} {i : Fin n}
    (plan : List (AlignmentPivotStage n i)) (P : (principalPivotRoutes plan) → Prop) :
    (∃ route, selectedAlignmentFirstRoute plan P = some route) ↔ ∃ route, P route := by
  constructor
  · rintro ⟨route, hr⟩
    exact ⟨route, selected_alignment_first_route_spec plan P route hr⟩
  · rintro ⟨route, hr⟩
    have he : ∃ j : Fin (Fintype.card (principalPivotRoutes plan)),
        P ((Fintype.equivFin (principalPivotRoutes plan)).symm j) :=
      ⟨(Fintype.equivFin (principalPivotRoutes plan)) route, by simpa using hr⟩
    obtain ⟨j, hj⟩ := (principal_first_success_exists (Fintype.card (principalPivotRoutes plan))
      (fun j (_ : Unit) => P ((Fintype.equivFin (principalPivotRoutes plan)).symm j)) ()).mpr he
    exact ⟨_, Option.map_eq_some_iff.mpr ⟨j, hj, rfl⟩⟩

abbrev SelectedAlignmentScheduleSuccess (n : ℕ) (α : Type*) :=
  (p : AlignmentPlannedPivot n) → List (AlignmentPlannedPivot n) →
    (Fin n → ℚ) → List (ℕ × List (AlignmentAddingPair n p.pivot × ℚ)) → α → Prop

noncomputable def selectedAlignmentScheduleAdvance {n : ℕ} {α : Type*}
    (q₀ : ℕ) (Good : SelectedAlignmentScheduleSuccess n α)
    (schedule : List (AlignmentPlannedPivot n)) (b : Fin n → ℚ) (x : α) : Option (Fin n → ℚ) :=
  match schedule with
  | [] => none
  | p :: later =>
    (selectedAlignmentFirstRoute p.plan (fun route => Good p later b route.val x)).map
      (fun route => (alignmentJointRouteArithmetic q₀ p.plan b route.val).1)

noncomputable def selectedAlignmentSchedulePrefixState {n : ℕ} {α : Type*}
    (q₀ : ℕ) (Good : SelectedAlignmentScheduleSuccess n α)
    (schedule : List (AlignmentPlannedPivot n)) (b : Fin n → ℚ) (x : α) : ℕ → Option (Fin n → ℚ)
  | 0 => some b
  | k+1 => (selectedAlignmentSchedulePrefixState q₀ Good schedule b x k).bind
      (fun c => selectedAlignmentScheduleAdvance q₀ Good (schedule.drop k) c x)

theorem selected_alignment_schedule_advance_spec {n : ℕ} {α : Type*}
    (q₀ : ℕ) (Good : SelectedAlignmentScheduleSuccess n α)
    (p : AlignmentPlannedPivot n) (later : List (AlignmentPlannedPivot n))
    (b c : Fin n → ℚ) (x : α)
    (h : selectedAlignmentScheduleAdvance q₀ Good (p :: later) b x = some c) :
    ∃ route ∈ principalPivotRoutes p.plan,
      c = (alignmentJointRouteArithmetic q₀ p.plan b route).1 ∧ Good p later b route x := by
  obtain ⟨route, hr, he⟩ := Option.map_eq_some_iff.mp h
  exact ⟨route.val, route.property, he.symm,
    selected_alignment_first_route_spec p.plan _ route hr⟩

theorem selected_alignment_schedule_advance_exists {n : ℕ} {α : Type*}
    (q₀ : ℕ) (Good : SelectedAlignmentScheduleSuccess n α)
    (p : AlignmentPlannedPivot n) (later : List (AlignmentPlannedPivot n))
    (b : Fin n → ℚ) (x : α) :
    (∃ c, selectedAlignmentScheduleAdvance q₀ Good (p :: later) b x = some c) ↔
      ∃ route ∈ principalPivotRoutes p.plan, Good p later b route x := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨route, hr, _, hg⟩ := selected_alignment_schedule_advance_spec q₀ Good p later b c x hc
    exact ⟨route, hr, hg⟩
  · rintro ⟨route, hr, hg⟩
    obtain ⟨chosen, hc⟩ := (selected_alignment_first_route_exists p.plan
      (fun route => Good p later b route.val x)).mpr ⟨⟨route,hr⟩,hg⟩
    exact ⟨_, Option.map_eq_some_iff.mpr ⟨chosen, hc, rfl⟩⟩

theorem selected_alignment_schedule_advance_scale_mem {n : ℕ} {α : Type*}
    (q₀ : ℕ) (Good : SelectedAlignmentScheduleSuccess n α)
    (p : AlignmentPlannedPivot n) (later : List (AlignmentPlannedPivot n))
    (b c : Fin n → ℚ) (x : α)
    (h : selectedAlignmentScheduleAdvance q₀ Good (p :: later) b x = some c) :
    c ∈ alignmentScaleFrontier p.pivot (alignmentForwardOptions p.plan) {b} := by
  obtain ⟨route, hr, rfl, _⟩ := selected_alignment_schedule_advance_spec q₀ Good p later b c x h
  exact selected_alignment_route_scale_mem q₀ _ p.plan b route hr

/-- Iterating the finite-state selector has the literal head-first recursion. -/
theorem selected_alignment_schedule_prefix_cons {n : ℕ} {α : Type*}
    (q₀ : ℕ) (Good : SelectedAlignmentScheduleSuccess n α)
    (p : AlignmentPlannedPivot n) (later : List (AlignmentPlannedPivot n))
    (b : Fin n → ℚ) (x : α) (k : ℕ) :
    selectedAlignmentSchedulePrefixState q₀ Good (p :: later) b x (k+1) =
      (selectedAlignmentScheduleAdvance q₀ Good (p :: later) b x).bind
        (fun c => selectedAlignmentSchedulePrefixState q₀ Good later c x k) := by
  induction k with
  | zero => simp [selectedAlignmentSchedulePrefixState]
  | succ k ih =>
    rw [selectedAlignmentSchedulePrefixState, ih, Option.bind_assoc]
    rfl

theorem selected_alignment_schedule_prefix_mem {n : ℕ} {α : Type*}
    (q₀ : ℕ) (Good : SelectedAlignmentScheduleSuccess n α)
    (schedule : List (AlignmentPlannedPivot n)) (incoming : Finset (Fin n → ℚ))
    (b : Fin n → ℚ) (hb : b ∈ incoming) (x : α) (k : ℕ) (hk : k ≤ schedule.length)
    (c : Fin n → ℚ) (hc : selectedAlignmentSchedulePrefixState q₀ Good schedule b x k = some c) :
    c ∈ selectedAlignmentScheduleIncoming (schedule.take k) incoming := by
  induction schedule generalizing incoming b k with
  | nil =>
    have hk0 : k = 0 := by simpa using hk
    subst k
    have he : b = c := Option.some.inj hc
    exact he ▸ hb
  | cons p later ih =>
    cases k with
    | zero =>
      have he : b = c := Option.some.inj hc
      exact he ▸ hb
    | succ k =>
      rw [selected_alignment_schedule_prefix_cons] at hc
      obtain ⟨d, hd, hc⟩ := Option.bind_eq_some_iff.mp hc
      exact ih _ d (alignmentScheduleStep_contains p incoming b d hb
        (selected_alignment_schedule_advance_scale_mem q₀ Good p later b d x hd)) k
        (by simpa using hk) hc

/-- Equality of all queried predicates gives equality of the deterministic
selector, including its first-success tie breaking. -/
theorem selected_alignment_schedule_advance_congr {n : ℕ} {α : Type*}
    (q₀ : ℕ) (Good : SelectedAlignmentScheduleSuccess n α)
    (p : AlignmentPlannedPivot n) (later : List (AlignmentPlannedPivot n))
    (b : Fin n → ℚ) (x y : α)
    (h : ∀ route ∈ principalPivotRoutes p.plan, Good p later b route x ↔ Good p later b route y) :
    selectedAlignmentScheduleAdvance q₀ Good (p :: later) b x =
      selectedAlignmentScheduleAdvance q₀ Good (p :: later) b y := by
  have he : (fun route : principalPivotRoutes p.plan => Good p later b route.val x) =
      (fun route => Good p later b route.val y) := funext (fun route => propext (h route.val route.property))
  simp only [selectedAlignmentScheduleAdvance, he]

/-- The complete first-success path already contains the actual future-
protected threshold path. No favorable route or final scale is assumed. -/
theorem selected_alignment_schedule_prefix_threshold_path {n : ℕ}
    (G X : Fin n → Type*) (κ : Type*) [∀ i, Group (G i)] [∀ i, MulAction (G i) (X i)]
    (q₀ : ℕ) (L : ∀ i, AlignmentAddingPair n i → G i)
    (obs : ∀ i, Finset (Fin n) → ℚ → X i → κ → ℝ) (θ : ℝ) (centers : ∀ i, X i)
    (schedule : List (AlignmentPlannedPivot n)) (b c : Fin n → ℚ)
    (h : selectedAlignmentSchedulePrefixState q₀
      (fun p later b route (_ : Unit) => ∀ request ∈ selectedAlignmentScheduleRequests later p.pivot,
        principalThresholdRequestHolds q₀ (alignmentJointRouteArithmetic q₀ p.plan b route).1
          (L p.pivot) (obs p.pivot) θ (centers p.pivot) request)
      schedule b () schedule.length = some c) :
    PrincipalThresholdScalePath G X κ q₀ L obs θ centers schedule b c := by
  induction schedule generalizing b with
  | nil =>
    have he : b = c := Option.some.inj h
    subst c
    exact .nil b
  | cons p later ih =>
    rw [List.length_cons, selected_alignment_schedule_prefix_cons] at h
    obtain ⟨d, hd, hrest⟩ := Option.bind_eq_some_iff.mp h
    have hs := selected_alignment_schedule_advance_scale_mem q₀ _ p later b d () hd
    obtain ⟨route, hr, he, hg⟩ := selected_alignment_schedule_advance_spec q₀ _ p later b d () hd
    refine .cons p later b d c hs ?_ (ih d hrest)
    intro request hrequest
    rw [he]
    exact hg _ (List.mem_map.mpr ⟨request, hrequest, rfl⟩)

end Hindman168
