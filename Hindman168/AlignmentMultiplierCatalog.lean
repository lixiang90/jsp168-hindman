import Hindman168.AlignmentFutureWordTransport
import Hindman168.AlignmentScalePaths

/-! Finite products of possible later multipliers and the exact factor
of every reachable scale tuple relative to its arbitrary incoming tuple. -/

namespace Hindman168
open scoped Classical

noncomputable def alignmentScaleSetProduct {n : ℕ} (A B : Finset (Fin n → ℚ)) :
    Finset (Fin n → ℚ) := A.biUnion (fun a => B.image (alignmentMultiplyScales a))

noncomputable def alignmentFutureProducts {n : ℕ} :
    List (Finset (Fin n → ℚ)) → Finset (Fin n → ℚ)
  | [] => {fun _ => 1}
  | A :: later => alignmentScaleSetProduct A (alignmentFutureProducts later)

def alignmentTupleListProduct {n : ℕ} : List (Fin n → ℚ) → (Fin n → ℚ)
  | [] => fun _ => 1
  | a :: later => alignmentMultiplyScales a (alignmentTupleListProduct later)

theorem alignmentScaleSetProduct_contains {n : ℕ} (A B : Finset (Fin n → ℚ))
    (a b : Fin n → ℚ) (ha : a ∈ A) (hb : b ∈ B) :
    alignmentMultiplyScales a b ∈ alignmentScaleSetProduct A B :=
  Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr ⟨b, hb, rfl⟩⟩

theorem alignmentScaleSetProduct_positive {n : ℕ} (A B : Finset (Fin n → ℚ))
    (hA : ∀ a ∈ A, ∀ j, 0 < a j) (hB : ∀ b ∈ B, ∀ j, 0 < b j) :
    ∀ d ∈ alignmentScaleSetProduct A B, ∀ j, 0 < d j := by
  intro d hd
  obtain ⟨a, ha, himage⟩ := Finset.mem_biUnion.mp hd
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp himage
  exact alignmentMultiplyScales_positive a b (hA a ha) (hB b hb)

theorem alignmentFutureProducts_positive {n : ℕ} (families : List (Finset (Fin n → ℚ)))
    (hfamilies : ∀ A ∈ families, ∀ a ∈ A, ∀ j, 0 < a j) :
    ∀ d ∈ alignmentFutureProducts families, ∀ j, 0 < d j := by
  induction families with
  | nil =>
    intro d hd
    have h : d = fun _ => 1 := Finset.mem_singleton.mp hd
    subst d
    intro j
    exact zero_lt_one
  | cons A later ih =>
    exact alignmentScaleSetProduct_positive A _ (hfamilies A List.mem_cons_self)
      (ih (fun B hB => hfamilies B (List.mem_cons_of_mem A hB)))

theorem alignmentFutureProducts_selected_member {n : ℕ}
    (selected : List (Fin n → ℚ)) (families : List (Finset (Fin n → ℚ)))
    (hselected : List.Forall₂ (fun a A => a ∈ A) selected families) :
    alignmentTupleListProduct selected ∈ alignmentFutureProducts families := by
  induction hselected with
  | nil => exact Finset.mem_singleton_self _
  | cons ha _ ih => exact alignmentScaleSetProduct_contains _ _ _ _ ha ih

theorem alignmentScaleUpdate_factor {n : ℕ} (i : Fin n) (T : Finset (Fin n))
    (k : ℕ) (b d : Fin n → ℚ) :
    alignmentScaleUpdate i T k (alignmentMultiplyScales b d) =
      alignmentMultiplyScales b (alignmentScaleUpdate i T k d) := by
  funext j
  exact mul_assoc (b j) (d j) (alignmentMultiplier i T k j)

theorem alignmentScaleStep_factor {n : ℕ} (i : Fin n) (stage : AlignmentStageOptions n i)
    (incoming : Finset (Fin n → ℚ)) (b : Fin n → ℚ) :
    alignmentScaleStep i stage (incoming.image (alignmentMultiplyScales b)) =
      (alignmentScaleStep i stage incoming).image (alignmentMultiplyScales b) := by
  ext c
  constructor
  · intro hc
    obtain ⟨bd, hbd, himage⟩ := Finset.mem_biUnion.mp hc
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hbd
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp himage
    exact Finset.mem_image.mpr ⟨alignmentScaleUpdate i stage.1 p.1 d,
      alignmentScaleStep_contains i stage incoming d hd p hp,
      (alignmentScaleUpdate_factor i stage.1 p.1 b d).symm⟩
  · intro hc
    obtain ⟨d', hd', rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨d, hd, himage⟩ := Finset.mem_biUnion.mp hd'
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp himage
    rw [← alignmentScaleUpdate_factor]
    exact alignmentScaleStep_contains i stage _ _ (Finset.mem_image.mpr ⟨d, hd, rfl⟩) p hp

theorem alignmentScaleFrontier_factor {n : ℕ} (i : Fin n)
    (stages : List (AlignmentStageOptions n i)) (incoming : Finset (Fin n → ℚ))
    (b : Fin n → ℚ) :
    alignmentScaleFrontier i stages (incoming.image (alignmentMultiplyScales b)) =
      (alignmentScaleFrontier i stages incoming).image (alignmentMultiplyScales b) := by
  induction stages generalizing incoming with
  | nil => rfl
  | cons stage stages ih =>
    simp only [alignmentScaleFrontier, alignmentScaleStep_factor, ih]

theorem alignmentScaleFrontier_singleton_factor {n : ℕ} (i : Fin n)
    (stages : List (AlignmentStageOptions n i)) (b : Fin n → ℚ) :
    alignmentScaleFrontier i stages {b} =
      (alignmentScaleFrontier i stages {fun _ => 1}).image (alignmentMultiplyScales b) := by
  have h := alignmentScaleFrontier_factor i stages {fun _ => 1} b
  have hsingle : ({fun _ => (1 : ℚ)} : Finset (Fin n → ℚ)).image
      (alignmentMultiplyScales b) = {b} := by
    rw [Finset.image_singleton]
    congr 1
    funext j
    exact mul_one (b j)
  exact hsingle ▸ h

end Hindman168
