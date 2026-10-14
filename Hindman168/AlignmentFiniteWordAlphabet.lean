import Hindman168.AlignmentJumpTemplates

/-! Finite actual rational-letter word families have finite alphabets.
Encoding and decoding retain every letter occurrence and its order. -/

namespace Hindman168
open scoped Classical

noncomputable def alignmentWordLetters {n : ℕ} {i : Fin n}
    (words : Finset (List (AlignmentAddingPair n i × ℚ))) :
    Finset (AlignmentAddingPair n i × ℚ) := words.biUnion List.toFinset

noncomputable def alignmentEncodeWord {n : ℕ} {i : Fin n}
    (words : Finset (List (AlignmentAddingPair n i × ℚ))) (w : {w // w ∈ words}) :
    List {l // l ∈ alignmentWordLetters words} :=
  w.val.attach.map (fun l => ⟨l.val, Finset.mem_biUnion.mpr
    ⟨w.val, w.property, List.mem_toFinset.mpr l.property⟩⟩)

noncomputable def alignmentEncodedWords {n : ℕ} {i : Fin n}
    (words : Finset (List (AlignmentAddingPair n i × ℚ))) :
    Finset (List {l // l ∈ alignmentWordLetters words}) :=
  words.attach.image (alignmentEncodeWord words)

theorem alignmentEncodeWord_decode {n : ℕ} {i : Fin n}
    (words : Finset (List (AlignmentAddingPair n i × ℚ))) (w : {w // w ∈ words}) :
    (alignmentEncodeWord words w).map Subtype.val = w.val := by
  simp only [alignmentEncodeWord, List.map_map, Function.comp_def]
  exact List.attach_map_subtype_val w.val

theorem alignmentEncodedWords_decode {n : ℕ} {i : Fin n}
    (words : Finset (List (AlignmentAddingPair n i × ℚ))) :
    (alignmentEncodedWords words).image (List.map Subtype.val) = words := by
  unfold alignmentEncodedWords
  rw [Finset.image_image]
  have hfun : ((List.map Subtype.val) ∘ alignmentEncodeWord words) = Subtype.val := by
    funext w
    exact alignmentEncodeWord_decode words w
  rw [hfun, Finset.attach_image_val]

theorem alignmentWordLetters_contains {n : ℕ} {i : Fin n}
    (words : Finset (List (AlignmentAddingPair n i × ℚ)))
    (w : List (AlignmentAddingPair n i × ℚ)) (hw : w ∈ words)
    (l : AlignmentAddingPair n i × ℚ) (hl : l ∈ w) :
    l ∈ alignmentWordLetters words :=
  Finset.mem_biUnion.mpr ⟨w, hw, List.mem_toFinset.mpr hl⟩

end Hindman168
