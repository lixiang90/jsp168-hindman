import Hindman168.PositivePrincipalSumFutureThreshold

namespace Hindman168
open scoped Classical

/-- Successful transitions keep the raw centers fixed across pivots. Each
local requirement is the original canonical request enlarged by the actual
later schedule's finite multiplier catalogue. -/
inductive PrincipalThresholdScalePath {n : ℕ} (G X : Fin n → Type*) (κ : Type*)
    [∀ i, Group (G i)] [∀ i, MulAction (G i) (X i)]
    (q₀ : ℕ) (L : ∀ i, AlignmentAddingPair n i → G i)
    (obs : ∀ i, Finset (Fin n) → ℚ → X i → κ → ℝ)
    (θ : ℝ) (centers : ∀ i, X i) :
    List (AlignmentPlannedPivot n) → (Fin n → ℚ) → (Fin n → ℚ) → Prop
  | nil (b) : PrincipalThresholdScalePath G X κ q₀ L obs θ centers [] b b
  | cons (p : AlignmentPlannedPivot n) (later) (b b' bfin)
      (step : b' ∈ alignmentScaleFrontier p.pivot (alignmentForwardOptions p.plan) {b})
      (secured : ∀ request ∈ alignmentCanonicalRequests n p.pivot,
        principalThresholdRequestHolds q₀ b' (L p.pivot) (obs p.pivot) θ (centers p.pivot)
          (alignmentFutureRequest (alignmentPlannedFutureProducts later) request))
      (rest : PrincipalThresholdScalePath G X κ q₀ L obs θ centers later b' bfin) :
      PrincipalThresholdScalePath G X κ q₀ L obs θ centers (p :: later) b bfin

theorem principal_threshold_path_secured {n : ℕ} (G X : Fin n → Type*) (κ : Type*)
    [∀ i, Group (G i)] [∀ i, MulAction (G i) (X i)]
    (q₀ : ℕ) (L : ∀ i, AlignmentAddingPair n i → G i)
    (obs : ∀ i, Finset (Fin n) → ℚ → X i → κ → ℝ) (θ : ℝ) (centers : ∀ i, X i)
    {schedule : List (AlignmentPlannedPivot n)} {b bfin : Fin n → ℚ}
    (h : PrincipalThresholdScalePath G X κ q₀ L obs θ centers schedule b bfin) :
    PrincipalFutureSecuredPath (fun i b => ∀ request ∈ alignmentCanonicalRequests n i,
      principalThresholdRequestHolds q₀ b (L i) (obs i) θ (centers i) request)
      schedule b bfin := by
  induction h with
  | nil b => exact .nil b
  | cons p later b b' bfin hs ha hr ih =>
    refine .cons p later b b' bfin hs ?_ ih
    intro d hd request hrequest
    exact principal_threshold_future_transport q₀ b' d (L p.pivot) (obs p.pivot) θ
      (centers p.pivot) _ hd request (ha request hrequest)

/-- Final scale membership and every pivot requirement are conclusions,
not inputs. This is the cross-pivot preservation used at the end of §8.5. -/
theorem principal_threshold_path_final {n : ℕ} (G X : Fin n → Type*) (κ : Type*)
    [∀ i, Group (G i)] [∀ i, MulAction (G i) (X i)]
    (q₀ : ℕ) (L : ∀ i, AlignmentAddingPair n i → G i)
    (obs : ∀ i, Finset (Fin n) → ℚ → X i → κ → ℝ) (θ : ℝ) (centers : ∀ i, X i)
    {schedule : List (AlignmentPlannedPivot n)} (hcover : schedule.map AlignmentPlannedPivot.pivot = List.finRange n)
    {b bfin : Fin n → ℚ}
    (h : PrincipalThresholdScalePath G X κ q₀ L obs θ centers schedule b bfin) :
    bfin ∈ alignmentScheduleFinalScales schedule {b} ∧ ∀ i,
      ∀ request ∈ alignmentCanonicalRequests n i,
        principalThresholdRequestHolds q₀ bfin (L i) (obs i) θ (centers i) request := by
  have hs := principal_threshold_path_secured G X κ q₀ L obs θ centers h
  obtain ⟨d, hd, hfin⟩ := principal_scale_path_future_factor (principal_secured_path_scale_path hs)
  refine ⟨hfin ▸ alignmentScheduleFinalScales_contains schedule {b} b d
    (Finset.mem_singleton_self _) hd, ?_⟩
  intro i
  have hi : i ∈ schedule.map AlignmentPlannedPivot.pivot := by rw [hcover]; simp
  obtain ⟨p, hp, hpi⟩ := List.mem_map.mp hi
  subst i
  exact principal_secured_path_preserves hs p hp
end Hindman168
