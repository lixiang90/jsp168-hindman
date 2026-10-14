import Hindman168.SelectedAlignmentRouteKernel
import Hindman168.SelectedAlignmentRouteCellInvariance
import Hindman168.SelectedAlignmentRouteShiftBounds

/-! Secured route success is first expressed at a signed pivot. Translation
removal uses this genuine predicate on all integers; only the final original
harmonic support is converted back to a natural raw coordinate. -/
namespace Hindman168
open Filter FiniteMass
open scoped Classical Topology
attribute [local instance] alignmentAddingPairFintype

noncomputable def selectedAlignmentSignedRouteSecured {n M : ℕ} {κ : Type*}
    (f : Fin n ↪o Fin M) (i : Fin n) (F : MasterParameterFamily) (q₀ w : ℕ)
    (x : Fin M → ℕ) (S : Finset (Fin n) → ℚ → κ → ℕ → ℤ → ℝ) (θ : ℝ)
    (plan : List (AlignmentPivotStage n i)) (b : Fin n → ℚ)
    (requests : List (AlignmentPivotRequest n i)) (p : ℤ) : Prop :=
  ∃ route ∈ principalPivotRoutes plan, ∀ request ∈ requests,
    principalThresholdRequestHolds q₀ (alignmentJointRouteArithmetic q₀ plan b route).1
      (principalNativeLetter f) (selectedAlignmentSignedScaleObservation f i F q₀ w x S p) θ 1 request

noncomputable def selectedAlignmentOutsideRouteShift {n M : ℕ}
    (f : Fin n ↪o Fin M) (i : Fin n) (F : MasterParameterFamily) (q₀ w : ℕ)
    (plan : List (AlignmentPivotStage n i)) (b : Fin n → ℚ)
    (route : List (ℕ × List (AlignmentAddingPair n i × ℚ)))
    (x : {j : Fin M // j ≠ f i} → ℕ) : ℤ :=
  alignmentIntegerSlotShift (fun a => alignmentPairResidue q₀ w (F.modulus w) a
    (insertPivotCoordinate (f i) x 0))
    (selectedAlignmentSlotExtension f (alignmentJointRouteArithmetic q₀ plan b route).2.toAdd)

theorem selected_alignment_insert_earlier_eq {M : ℕ} (i : Fin M)
    (x : {j : Fin M // j ≠ i} → ℕ) (p q : ℕ) :
    ∀ j < i, insertPivotCoordinate i x p j = insertPivotCoordinate i x q j := by
  intro j hj
  simp only [insertPivotCoordinate, dif_neg (ne_of_lt hj)]

theorem selected_alignment_signed_route_secured_earlier_eq {n M : ℕ} {κ : Type*}
    (f : Fin n ↪o Fin M) (i : Fin n) (F : MasterParameterFamily) (q₀ w : ℕ)
    (x y : Fin M → ℕ) (hxy : ∀ j < f i, x j = y j)
    (S : Finset (Fin n) → ℚ → κ → ℕ → ℤ → ℝ) (θ : ℝ)
    (plan : List (AlignmentPivotStage n i)) (b : Fin n → ℚ)
    (requests : List (AlignmentPivotRequest n i)) (p : ℤ) :
    selectedAlignmentSignedRouteSecured f i F q₀ w x S θ plan b requests p ↔
      selectedAlignmentSignedRouteSecured f i F q₀ w y S θ plan b requests p := by
  have he (request : AlignmentPivotRequest n i) (a : ℚ) (u) (c : κ) :=
    selected_alignment_signed_observation_earlier_eq f i F q₀ w x y hxy S p
      (insert i request.tail) (by simpa only [alignment_request_factor_target] using request.before) a u c
  simp only [selectedAlignmentSignedRouteSecured, principalThresholdRequestHolds, he]

theorem selected_alignment_raw_route_yields_outside_secured {n M : ℕ} {κ : Type*}
    (f : Fin n ↪o Fin M) (i : Fin n) (F : MasterParameterFamily) (q₀ w : ℕ)
    (x : {j : Fin M // j ≠ f i} → ℕ) (anchor : ℕ)
    (S : Finset (Fin n) → ℚ → κ → ℕ → ℤ → ℝ) (θ : ℝ)
    (plan : List (AlignmentPivotStage n i)) (b : Fin n → ℚ)
    (requests : List (AlignmentPivotRequest n i)) (p : ℤ)
    (hp : p ∈ selectedAlignmentRouteActualSet
      (selectedAlignmentRouteRawReading f i F q₀ w (insertPivotCoordinate (f i) x anchor) S)
      θ q₀ plan b requests (principalPivotRoutes plan)) :
    ∃ route : principalPivotRoutes plan,
      selectedAlignmentSignedRouteSecured f i F q₀ w (insertPivotCoordinate (f i) x 0)
        S θ plan b requests (p + selectedAlignmentOutsideRouteShift f i F q₀ w plan b route.val x) := by
  have hset := selected_alignment_raw_route_set_earlier_eq f i F q₀ w
    (insertPivotCoordinate (f i) x anchor) (insertPivotCoordinate (f i) x 0)
    (selected_alignment_insert_earlier_eq (f i) x anchor 0) S θ plan b requests (principalPivotRoutes plan)
  rw [hset] at hp
  obtain ⟨route,hr,hreq⟩ := (selected_alignment_route_raw_actual_iff f i F q₀ w
    (insertPivotCoordinate (f i) x 0) S θ plan b requests (principalPivotRoutes plan) p).mp hp
  exact ⟨⟨route,hr⟩,route,hr,hreq⟩

theorem selected_alignment_outside_secured_natural {n M : ℕ} {κ : Type*}
    (f : Fin n ↪o Fin M) (i : Fin n) (F : MasterParameterFamily) (q₀ w : ℕ)
    (x : {j : Fin M // j ≠ f i} → ℕ) (p : ℕ)
    (S : Finset (Fin n) → ℚ → κ → ℕ → ℤ → ℝ) (θ : ℝ)
    (plan : List (AlignmentPivotStage n i)) (b : Fin n → ℚ)
    (requests : List (AlignmentPivotRequest n i)) :
    selectedAlignmentSignedRouteSecured f i F q₀ w (insertPivotCoordinate (f i) x 0)
      S θ plan b requests p ↔
    selectedAlignmentSignedRouteSecured f i F q₀ w (insertPivotCoordinate (f i) x p)
      S θ plan b requests ((insertPivotCoordinate (f i) x p) (f i)) := by
  rw [insertPivotCoordinate_self]
  exact selected_alignment_signed_route_secured_earlier_eq f i F q₀ w _ _
    (selected_alignment_insert_earlier_eq (f i) x 0 p) S θ plan b requests p

end Hindman168
