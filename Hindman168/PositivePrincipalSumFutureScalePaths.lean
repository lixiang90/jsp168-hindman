import Hindman168.AlignmentAllPivotPlanning

/-! Actual scale-frontier paths determine, rather than assume, the complete
later multiplier in the finite future catalogue chosen before the models. -/
namespace Hindman168
open scoped Classical

inductive PrincipalScalePath {n : ℕ} :
    List (AlignmentPlannedPivot n) → (Fin n → ℚ) → (Fin n → ℚ) → Prop
  | nil (b) : PrincipalScalePath [] b b
  | cons (p : AlignmentPlannedPivot n) (later) (b b' bfin)
      (step : b' ∈ alignmentScaleFrontier p.pivot (alignmentForwardOptions p.plan) {b})
      (rest : PrincipalScalePath later b' bfin) : PrincipalScalePath (p :: later) b bfin

theorem principal_scale_path_future_factor {n : ℕ}
    {schedule : List (AlignmentPlannedPivot n)} {b bfin : Fin n → ℚ}
    (h : PrincipalScalePath schedule b bfin) :
    ∃ d ∈ alignmentPlannedFutureProducts schedule, bfin = alignmentMultiplyScales b d := by
  induction h with
  | nil b =>
    refine ⟨fun _ => 1, Finset.mem_singleton_self _, ?_⟩
    funext j
    simp [alignmentMultiplyScales]
  | cons p later b b' bfin hs hr ih =>
    rw [alignmentScaleFrontier_singleton_factor] at hs
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨e, he, hfin⟩ := ih
    refine ⟨alignmentMultiplyScales d e,
      alignmentScaleSetProduct_contains _ _ _ _ hd he, ?_⟩
    rw [hfin]
    funext j
    exact mul_assoc (b j) (d j) (e j)

/-- A certificate secured at each pivot protects its original raw sample
for every later multiplier in that pivot's actual prechosen catalogue. -/
inductive PrincipalFutureSecuredPath {n : ℕ}
    (A : Fin n → (Fin n → ℚ) → Prop) :
    List (AlignmentPlannedPivot n) → (Fin n → ℚ) → (Fin n → ℚ) → Prop
  | nil (b) : PrincipalFutureSecuredPath A [] b b
  | cons (p : AlignmentPlannedPivot n) (later) (b b' bfin)
      (step : b' ∈ alignmentScaleFrontier p.pivot (alignmentForwardOptions p.plan) {b})
      (secured : ∀ d ∈ alignmentPlannedFutureProducts later,
        A p.pivot (alignmentMultiplyScales b' d))
      (rest : PrincipalFutureSecuredPath A later b' bfin) :
      PrincipalFutureSecuredPath A (p :: later) b bfin

theorem principal_secured_path_scale_path {n : ℕ}
    {A : Fin n → (Fin n → ℚ) → Prop} {schedule : List (AlignmentPlannedPivot n)}
    {b bfin : Fin n → ℚ} (h : PrincipalFutureSecuredPath A schedule b bfin) :
    PrincipalScalePath schedule b bfin := by
  induction h with
  | nil b => exact .nil b
  | cons p later b b' bfin hs ha hr ih => exact .cons p later b b' bfin hs ih

/-- No separate 'future scales preserve alignment' assumption is needed:
the later actual path supplies its own member of the protected catalogue. -/
theorem principal_secured_path_preserves {n : ℕ}
    {A : Fin n → (Fin n → ℚ) → Prop} {schedule : List (AlignmentPlannedPivot n)}
    {b bfin : Fin n → ℚ} (h : PrincipalFutureSecuredPath A schedule b bfin) :
    ∀ p ∈ schedule, A p.pivot bfin := by
  induction h with
  | nil b => simp
  | cons p later b b' bfin hs ha hr ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · obtain ⟨d, hd, hfin⟩ := principal_scale_path_future_factor
        (principal_secured_path_scale_path hr)
      rw [hfin]
      exact ha d hd
    · exact ih q hq
end Hindman168
