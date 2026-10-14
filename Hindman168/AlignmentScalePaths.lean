import Hindman168.AlignmentWordInflation

/-! All incoming, intermediate and terminal rational scales through a
finite schedule of stage alternatives are enumerated before realization. -/

namespace Hindman168
open scoped Classical

abbrev AlignmentStageOptions (n : ℕ) (i : Fin n) :=
  Finset (Fin n) × Finset (ℕ × List (AlignmentAddingPair n i × ℚ))

noncomputable def alignmentScaleStep {n : ℕ} (i : Fin n)
    (stage : AlignmentStageOptions n i) (incoming : Finset (Fin n → ℚ)) :
    Finset (Fin n → ℚ) :=
  incoming.biUnion (fun b => stage.2.image (fun p => alignmentScaleUpdate i stage.1 p.1 b))

noncomputable def alignmentScaleFrontier {n : ℕ} (i : Fin n) :
    List (AlignmentStageOptions n i) → Finset (Fin n → ℚ) → Finset (Fin n → ℚ)
  | [], incoming => incoming
  | stage :: stages, incoming =>
    alignmentScaleFrontier i stages (alignmentScaleStep i stage incoming)

noncomputable def alignmentAllScaleStates {n : ℕ} (i : Fin n) :
    List (AlignmentStageOptions n i) → Finset (Fin n → ℚ) → Finset (Fin n → ℚ)
  | [], incoming => incoming
  | stage :: stages, incoming =>
    incoming ∪ alignmentAllScaleStates i stages (alignmentScaleStep i stage incoming)

theorem alignmentScaleStep_contains {n : ℕ} (i : Fin n)
    (stage : AlignmentStageOptions n i) (incoming : Finset (Fin n → ℚ))
    (b : Fin n → ℚ) (hb : b ∈ incoming)
    (p : ℕ × List (AlignmentAddingPair n i × ℚ)) (hp : p ∈ stage.2) :
    alignmentScaleUpdate i stage.1 p.1 b ∈ alignmentScaleStep i stage incoming :=
  Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩

theorem alignmentScaleStep_positive {n : ℕ} (i : Fin n)
    (stage : AlignmentStageOptions n i) (incoming : Finset (Fin n → ℚ))
    (hin : ∀ b ∈ incoming, ∀ j, 0 < b j)
    (hstage : ∀ p ∈ stage.2, 0 < p.1) :
    ∀ b ∈ alignmentScaleStep i stage incoming, ∀ j, 0 < b j := by
  intro b hb
  obtain ⟨a, ha, himage⟩ := Finset.mem_biUnion.mp hb
  obtain ⟨p, hpChoice, rfl⟩ := Finset.mem_image.mp himage
  exact alignmentScaleUpdate_positive i stage.1 p.1 (hstage p hpChoice) a (hin a ha)

theorem alignmentScaleFrontier_positive {n : ℕ} (i : Fin n)
    (stages : List (AlignmentStageOptions n i)) (incoming : Finset (Fin n → ℚ))
    (hin : ∀ b ∈ incoming, ∀ j, 0 < b j)
    (hstages : ∀ stage ∈ stages, ∀ p ∈ stage.2, 0 < p.1) :
    ∀ b ∈ alignmentScaleFrontier i stages incoming, ∀ j, 0 < b j := by
  induction stages generalizing incoming with
  | nil => exact hin
  | cons stage stages ih =>
    exact ih (alignmentScaleStep i stage incoming)
      (alignmentScaleStep_positive i stage incoming hin
        (hstages stage List.mem_cons_self))
      (fun a ha => hstages a (List.mem_cons_of_mem stage ha))

theorem alignmentAllScaleStates_positive {n : ℕ} (i : Fin n)
    (stages : List (AlignmentStageOptions n i)) (incoming : Finset (Fin n → ℚ))
    (hin : ∀ b ∈ incoming, ∀ j, 0 < b j)
    (hstages : ∀ stage ∈ stages, ∀ p ∈ stage.2, 0 < p.1) :
    ∀ b ∈ alignmentAllScaleStates i stages incoming, ∀ j, 0 < b j := by
  induction stages generalizing incoming with
  | nil => exact hin
  | cons stage stages ih =>
    intro b hb
    rcases Finset.mem_union.mp hb with hb | hb
    · exact hin b hb
    · exact ih (alignmentScaleStep i stage incoming)
        (alignmentScaleStep_positive i stage incoming hin
          (hstages stage List.mem_cons_self))
        (fun a ha => hstages a (List.mem_cons_of_mem stage ha)) b hb

theorem alignmentAllScaleStates_contains_incoming {n : ℕ} (i : Fin n)
    (stages : List (AlignmentStageOptions n i)) (incoming : Finset (Fin n → ℚ)) :
    incoming ⊆ alignmentAllScaleStates i stages incoming := by
  cases stages with
  | nil => exact Finset.Subset.refl incoming
  | cons stage stages => exact Finset.subset_union_left

theorem alignmentScaleFrontier_subset_all {n : ℕ} (i : Fin n)
    (stages : List (AlignmentStageOptions n i)) (incoming : Finset (Fin n → ℚ)) :
    alignmentScaleFrontier i stages incoming ⊆ alignmentAllScaleStates i stages incoming := by
  induction stages generalizing incoming with
  | nil => exact Finset.Subset.refl incoming
  | cons stage stages ih =>
    exact Finset.Subset.trans (ih (alignmentScaleStep i stage incoming)) Finset.subset_union_right

theorem alignmentScaleFrontier_append {n : ℕ} (i : Fin n)
    (first later : List (AlignmentStageOptions n i)) (incoming : Finset (Fin n → ℚ)) :
    alignmentScaleFrontier i (first ++ later) incoming =
      alignmentScaleFrontier i later (alignmentScaleFrontier i first incoming) := by
  induction first generalizing incoming with
  | nil => rfl
  | cons stage stages ih =>
    exact ih (alignmentScaleStep i stage incoming)

theorem alignmentScaleStep_mono {n : ℕ} (i : Fin n)
    (stage : AlignmentStageOptions n i) (first second : Finset (Fin n → ℚ))
    (h : first ⊆ second) :
    alignmentScaleStep i stage first ⊆ alignmentScaleStep i stage second := by
  intro b hb
  obtain ⟨a, ha, hchoice⟩ := Finset.mem_biUnion.mp hb
  exact Finset.mem_biUnion.mpr ⟨a, h ha, hchoice⟩

theorem alignmentScaleFrontier_mono {n : ℕ} (i : Fin n)
    (stages : List (AlignmentStageOptions n i)) (first second : Finset (Fin n → ℚ))
    (h : first ⊆ second) :
    alignmentScaleFrontier i stages first ⊆ alignmentScaleFrontier i stages second := by
  induction stages generalizing first second with
  | nil => exact h
  | cons stage stages ih =>
    exact ih _ _ (alignmentScaleStep_mono i stage first second h)

theorem alignmentAllScaleStates_append {n : ℕ} (i : Fin n)
    (first later : List (AlignmentStageOptions n i)) (incoming : Finset (Fin n → ℚ)) :
    alignmentAllScaleStates i (first ++ later) incoming =
      alignmentAllScaleStates i first incoming ∪
        alignmentAllScaleStates i later (alignmentScaleFrontier i first incoming) := by
  induction first generalizing incoming with
  | nil =>
    exact (Finset.union_eq_right.mpr
      (alignmentAllScaleStates_contains_incoming i later incoming)).symm
  | cons stage stages ih =>
    simp only [List.cons_append, alignmentAllScaleStates, alignmentScaleFrontier, ih,
      Finset.union_assoc]

theorem alignmentAllScaleStates_contains_prefix {n : ℕ} (i : Fin n)
    (first later : List (AlignmentStageOptions n i)) (incoming : Finset (Fin n → ℚ)) :
    alignmentAllScaleStates i first incoming ⊆
      alignmentAllScaleStates i (first ++ later) incoming := by
  rw [alignmentAllScaleStates_append]
  exact Finset.subset_union_left

end Hindman168
