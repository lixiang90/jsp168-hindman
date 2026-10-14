import Hindman168.AlignmentAddingPairs

/-! Exact old/new-scale word inflation and predecessor requirements.
Words remain ordered products in an arbitrary group, so no commutativity
or fixing of previously processed targets is assumed. Integral letter
interpretation is established separately by finite denominator clearing. -/

namespace Hindman168
open scoped Classical

def alignmentLetterScalar {n : ℕ} {i : Fin n} (b : Fin n → ℚ)
    (l : AlignmentAddingPair n i × ℚ) : ℚ :=
  l.2 * (finiteScaleBlockProduct b (alignmentPairSourceBlock l.1) /
    finiteScaleBlockProduct b (alignmentPairTargetBlock l.1))

noncomputable def alignmentWordValue {n : ℕ} {i : Fin n} {G : Type*} [Group G]
    (q₀ : ℕ) (b : Fin n → ℚ) (L : AlignmentAddingPair n i → G) :
    List (AlignmentAddingPair n i × ℚ) → G
  | [] => 1
  | l :: w => L l.1 ^ ⌊(q₀ : ℚ) * alignmentLetterScalar b l⌋ * alignmentWordValue q₀ b L w

def alignmentInflateWord {n : ℕ} {i : Fin n} (T : Finset (Fin n)) (k : ℕ)
    (w : List (AlignmentAddingPair n i × ℚ)) : List (AlignmentAddingPair n i × ℚ) :=
  w.map (fun l => (l.1, l.2 * (k : ℚ) ^ alignmentPairInflationExponent l.1 T))

def alignmentPaletteRequirement {n : ℕ} {i : Fin n} {G X Color : Type*}
    [Group G] [MulAction G X] (q₀ : ℕ) (b : Fin n → ℚ)
    (L : AlignmentAddingPair n i → G) (B : Finset (Fin n))
    (palette : ℚ → X → Color) (leading : Finset ℚ)
    (words : Finset (List (AlignmentAddingPair n i × ℚ))) (x : X) : Prop :=
  ∀ a ∈ leading, ∀ w ∈ words,
    palette (a * finiteScaleBlockProduct b B) x =
      palette (a * finiteScaleBlockProduct b B) (alignmentWordValue q₀ b L w • x)

noncomputable def alignmentPredecessorLeading {n : ℕ} (i : Fin n)
    (T B : Finset (Fin n)) (k : ℕ) (leading : Finset ℚ) : Finset ℚ :=
  leading.image (fun a => a * finiteScaleBlockProduct (alignmentMultiplier i T k) B)

noncomputable def alignmentPredecessorWords {n : ℕ} {i : Fin n}
    (T : Finset (Fin n)) (k : ℕ) (J : List (AlignmentAddingPair n i × ℚ))
    (words : Finset (List (AlignmentAddingPair n i × ℚ))) :
    Finset (List (AlignmentAddingPair n i × ℚ)) :=
  insert J (words.image (fun w => alignmentInflateWord T k w ++ J))

theorem alignmentLetterScalar_inflation {n : ℕ} {i : Fin n}
    (e : AlignmentAddingPair n i) (T : Finset (Fin n)) (k : ℕ) (hk : 0 < k)
    (b : Fin n → ℚ) (γ : ℚ) :
    alignmentLetterScalar (alignmentScaleUpdate i T k b) (e, γ) =
      alignmentLetterScalar b (e, γ * (k : ℚ) ^ alignmentPairInflationExponent e T) := by
  unfold alignmentLetterScalar
  rw [alignmentPair_ratio_update e T k hk b]
  ring

theorem alignmentWordValue_append {n : ℕ} {i : Fin n} {G : Type*} [Group G]
    (q₀ : ℕ) (b : Fin n → ℚ) (L : AlignmentAddingPair n i → G)
    (v w : List (AlignmentAddingPair n i × ℚ)) :
    alignmentWordValue q₀ b L (v ++ w) =
      alignmentWordValue q₀ b L v * alignmentWordValue q₀ b L w := by
  induction v with
  | nil => simp [alignmentWordValue]
  | cons l v ih => simp only [List.cons_append, alignmentWordValue, ih, mul_assoc]

theorem alignmentWordValue_inflation {n : ℕ} {i : Fin n} {G : Type*} [Group G]
    (q₀ : ℕ) (b : Fin n → ℚ) (L : AlignmentAddingPair n i → G)
    (T : Finset (Fin n)) (k : ℕ) (hk : 0 < k)
    (w : List (AlignmentAddingPair n i × ℚ)) :
    alignmentWordValue q₀ (alignmentScaleUpdate i T k b) L w =
      alignmentWordValue q₀ b L (alignmentInflateWord T k w) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    rcases l with ⟨e, γ⟩
    simp only [alignmentWordValue, alignmentInflateWord, List.map_cons] at ⊢
    rw [alignmentLetterScalar_inflation e T k hk b γ]
    exact congrArg (fun y => L e ^ ⌊(q₀ : ℚ) *
      alignmentLetterScalar b (e, γ * (k : ℚ) ^ alignmentPairInflationExponent e T)⌋ * y) ih

theorem alignment_palette_update_preserves {n : ℕ} {i : Fin n} {G X Color : Type*}
    [Group G] [MulAction G X] (q₀ : ℕ) (b : Fin n → ℚ)
    (L : AlignmentAddingPair n i → G) (T B : Finset (Fin n))
    (k : ℕ) (hk : 0 < k) (palette : ℚ → X → Color)
    (leading oldLeading : Finset ℚ)
    (words oldWords : Finset (List (AlignmentAddingPair n i × ℚ)))
    (J : List (AlignmentAddingPair n i × ℚ)) (x : X)
    (hLeading : ∀ a ∈ leading,
      a * finiteScaleBlockProduct (alignmentMultiplier i T k) B ∈ oldLeading)
    (hJ : J ∈ oldWords)
    (hWords : ∀ w ∈ words, alignmentInflateWord T k w ++ J ∈ oldWords)
    (hreq : alignmentPaletteRequirement q₀ b L B palette oldLeading oldWords x) :
    alignmentPaletteRequirement q₀ (alignmentScaleUpdate i T k b) L B palette leading words
      (alignmentWordValue q₀ b L J • x) := by
  intro a ha w hw
  have hindex : a * finiteScaleBlockProduct (alignmentScaleUpdate i T k b) B =
      (a * finiteScaleBlockProduct (alignmentMultiplier i T k) B) * finiteScaleBlockProduct b B := by
    rw [alignmentScaleUpdate_product]
    ring
  rw [hindex, alignmentWordValue_inflation q₀ b L T k hk w]
  have hj := hreq _ (hLeading a ha) J hJ
  have hwj := hreq _ (hLeading a ha) (alignmentInflateWord T k w ++ J) (hWords w hw)
  rw [alignmentWordValue_append, mul_smul] at hwj
  exact hj.symm.trans hwj

theorem alignment_predecessor_preserves {n : ℕ} {i : Fin n} {G X Color : Type*}
    [Group G] [MulAction G X] (q₀ : ℕ) (b : Fin n → ℚ)
    (L : AlignmentAddingPair n i → G) (T B : Finset (Fin n))
    (k : ℕ) (hk : 0 < k) (palette : ℚ → X → Color)
    (leading : Finset ℚ) (words : Finset (List (AlignmentAddingPair n i × ℚ)))
    (J : List (AlignmentAddingPair n i × ℚ)) (x : X)
    (hreq : alignmentPaletteRequirement q₀ b L B palette
      (alignmentPredecessorLeading i T B k leading) (alignmentPredecessorWords T k J words) x) :
    alignmentPaletteRequirement q₀ (alignmentScaleUpdate i T k b) L B palette leading words
      (alignmentWordValue q₀ b L J • x) := by
  apply alignment_palette_update_preserves q₀ b L T B k hk palette leading _ words _ J x
    (fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩)
    (Finset.mem_insert_self _ _)
    (fun w hw => Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨w, hw, rfl⟩)) hreq

end Hindman168
