import Hindman168.AlignmentPivotRequests
import Mathlib.Data.List.Induction

/-! A plan is stored last-stage first. Its exact predecessor budgets are
constructed backward from the terminal requests, before any numerical scale. -/

namespace Hindman168
universe u v
open scoped Classical

noncomputable def alignmentBackwardPlanFits {n : ℕ} {i : Fin n} :
    List (AlignmentPivotStage n i) → List (AlignmentPivotRequest n i) → Prop
  | [], requests => requests = []
  | stage :: earlier, requests => ∃ prior,
    requests = prior ++ [stage.target] ∧
      alignmentBackwardPlanFits earlier (prior.map (alignmentPivotPredecessor stage))

def alignmentPivotStageOptions {n : ℕ} {i : Fin n}
    (stage : AlignmentPivotStage n i) : AlignmentStageOptions n i :=
  (stage.target.tail, stage.choices)

def alignmentForwardOptions {n : ℕ} {i : Fin n}
    (plan : List (AlignmentPivotStage n i)) : List (AlignmentStageOptions n i) :=
  plan.reverse.map alignmentPivotStageOptions

theorem alignmentForwardOptions_cons {n : ℕ} {i : Fin n}
    (stage : AlignmentPivotStage n i) (plan : List (AlignmentPivotStage n i)) :
    alignmentForwardOptions (stage :: plan) =
      alignmentForwardOptions plan ++ [alignmentPivotStageOptions stage] := by
  simp only [alignmentForwardOptions, List.reverse_cons, List.map_append, List.map_cons,
    List.map_nil]

theorem alignmentBackwardPlanFits_length {n : ℕ} {i : Fin n}
    (plan : List (AlignmentPivotStage n i)) (requests : List (AlignmentPivotRequest n i))
    (hfit : alignmentBackwardPlanFits plan requests) : plan.length = requests.length := by
  induction plan generalizing requests with
  | nil => rw [hfit]; rfl
  | cons stage plan ih =>
    obtain ⟨prior, rfl, hprior⟩ := hfit
    have h := ih _ hprior
    simp only [List.length_map] at h
    simp only [List.length_cons, List.length_append, List.length_nil]
    omega

theorem alignment_backward_plan_exists {n : ℕ} {i : Fin n} {Color : Type} [Finite Color]
    (s : ℕ) (hrec : HasAlignmentMonomialRecurrence s)
    (requests : List (AlignmentPivotRequest n i)) :
    ∃ plan : List (AlignmentPivotStage n i), alignmentBackwardPlanFits plan requests ∧
      ∀ stage ∈ plan, AlignmentPivotStageWorks.{u, v} s Color stage := by
  have build : ∀ m, ∀ requests : List (AlignmentPivotRequest n i), requests.length = m →
      ∃ plan : List (AlignmentPivotStage n i), alignmentBackwardPlanFits plan requests ∧
        ∀ stage ∈ plan, AlignmentPivotStageWorks.{u, v} s Color stage := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro requests hlen
      induction requests using List.reverseRecOn with
      | nil => exact ⟨[], rfl, by simp only [List.not_mem_nil, false_implies, implies_true]⟩
      | append_singleton prior request _ =>
        obtain ⟨Ω, hΩ⟩ := alignment_pivot_stage_exists.{u, v} (Color := Color) s hrec request
        let stage : AlignmentPivotStage n i := ⟨request, Ω⟩
        have hless : prior.length < m := by
          simp only [List.length_append, List.length_singleton] at hlen
          omega
        obtain ⟨earlier, hfit, hworks⟩ := ih prior.length hless
          (prior.map (alignmentPivotPredecessor stage)) (by simp only [List.length_map])
        refine ⟨stage :: earlier, ⟨prior, rfl, hfit⟩, ?_⟩
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hΩ
        · exact hworks a ha
  exact build requests.length requests rfl

end Hindman168
