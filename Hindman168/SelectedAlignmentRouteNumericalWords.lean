import Hindman168.SelectedAlignmentRouteNumericalPivot

namespace Hindman168
open scoped BigOperators Classical

/-- Every occurrence of an own-target letter contributes its own integer
numerator; repetitions and arbitrary signed word exponents are retained. -/
theorem selected_alignment_array_own_word {n M : ℕ} {i : Fin n}
    (f : Fin n ↪o Fin M) (x : Fin M → ℕ) (modulus : ℕ)
    (ρ : AlignmentAddingPair M (f i) → ℕ) (Δ : AlignmentAddingPair M (f i) → ℤ)
    (Q : AlignmentAddingPair M (f i) → ℕ) (q₀ : ℕ) (b : Fin n → ℚ)
    (T : Finset (Fin n)) (word : List (AlignmentAddingPair n i × ℚ))
    (htarget : ∀ l ∈ word, l.1.targetTail = T)
    (hexact : ∀ l ∈ word, (modulus : ℤ) * Δ (l.1.map f) = (Q (l.1.map f) : ℤ) -
      (alignmentNaturalBlockProduct x (T.image f) : ℤ) * ρ (l.1.map f))
    (p : ℤ) (v u : AlignmentAddingPair M (f i) → ℤ) :
    alignmentIntegerArrayArgument x modulus ρ Δ (T.image f) p
      (v+selectedAlignmentSlotExtension f (alignmentAuxiliaryWord q₀ b word))
      (u+selectedAlignmentSlotExtension f (alignmentAuxiliaryWord q₀ b word)) =
    alignmentIntegerArrayArgument x modulus ρ Δ (T.image f) p v u +
      (word.map (fun l => ⌊(q₀ : ℚ)*alignmentLetterScalar b l⌋ * (Q (l.1.map f) : ℤ))).sum := by
  induction word with
  | nil => simp only [alignmentAuxiliaryWord, selected_alignment_slot_extension_zero,
      add_zero, List.map_nil, List.sum_nil]
  | cons l word ih =>
    have ht := htarget l List.mem_cons_self
    have he := hexact l List.mem_cons_self
    have hunit : Pi.single (l.1.map f) ⌊(q₀ : ℚ)*alignmentLetterScalar b l⌋ =
        alignmentAuxiliaryUnit (l.1.map f) ⌊(q₀ : ℚ)*alignmentLetterScalar b l⌋ := by
      funext j
      simp [alignmentAuxiliaryUnit, Pi.single_apply]
    simp only [alignmentAuxiliaryWord, selected_alignment_slot_extension_add,
      selected_alignment_slot_extension_unit, hunit, List.map_cons, List.sum_cons]
    rw [show v + (alignmentAuxiliaryUnit (l.1.map f) ⌊(q₀ : ℚ)*alignmentLetterScalar b l⌋ +
        selectedAlignmentSlotExtension f (alignmentAuxiliaryWord q₀ b word)) =
      (v+selectedAlignmentSlotExtension f (alignmentAuxiliaryWord q₀ b word)) +
        alignmentAuxiliaryUnit (l.1.map f) ⌊(q₀ : ℚ)*alignmentLetterScalar b l⌋ by abel]
    rw [show u + (alignmentAuxiliaryUnit (l.1.map f) ⌊(q₀ : ℚ)*alignmentLetterScalar b l⌋ +
        selectedAlignmentSlotExtension f (alignmentAuxiliaryWord q₀ b word)) =
      (u+selectedAlignmentSlotExtension f (alignmentAuxiliaryWord q₀ b word)) +
        alignmentAuxiliaryUnit (l.1.map f) ⌊(q₀ : ℚ)*alignmentLetterScalar b l⌋ by abel]
    rw [alignmentIntegerArrayArgument_own_letter x modulus ρ Δ Q (T.image f) (l.1.map f)
      (by simpa only [AlignmentAddingPair.map] using congrArg (fun T => T.image f) ht) he]
    rw [ih (fun a ha => htarget a (List.mem_cons_of_mem _ ha))
      (fun a ha => hexact a (List.mem_cons_of_mem _ ha))]
    abel

/-- For the real master residues and progression shifts, the terminal's
numerical input is the shifted center plus the sum of original numerators. -/
theorem selected_alignment_route_own_word_argument {d n M : ℕ} {i : Fin n}
    {A : Finset ℚ} {P : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A P F) (f : Fin n ↪o Fin M)
    {q₀ w : ℕ} (hq : 0 < q₀) (hw : q₀+1 ≤ w)
    (x : Fin M → ℕ) (hx : ∀ j, Nat.Coprime (x j) (primorial w))
    (T : Finset (Fin n)) (b : Fin n → ℚ) (word : List (AlignmentAddingPair n i × ℚ))
    (htarget : ∀ l ∈ word, l.1.targetTail = T)
    (p : ℤ) (v : AlignmentAddingPair n i → ℤ) :
    alignmentIntegerArrayArgument x (F.modulus w)
      (fun e => alignmentPairResidue q₀ w (F.modulus w) e x)
      (fun e => alignmentPairProgression q₀ w (F.modulus w) e x) (T.image f) p
      (selectedAlignmentSlotExtension f (v+alignmentAuxiliaryWord q₀ b word))
      (selectedAlignmentSlotExtension f (alignmentAuxiliaryWord q₀ b word)) =
    (alignmentNaturalBlockProduct x (T.image f) : ℤ) *
      (p+alignmentIntegerSlotShift (fun e => alignmentPairResidue q₀ w (F.modulus w) e x)
        (selectedAlignmentSlotExtension f v)) +
      (word.map (fun l => ⌊(q₀ : ℚ)*alignmentLetterScalar b l⌋ *
        (alignmentIntegerNumerator q₀ w (l.1.map f) x : ℤ))).sum := by
  have he : ∀ l ∈ word, (F.modulus w : ℤ) * alignmentPairProgression q₀ w (F.modulus w) (l.1.map f) x =
      (alignmentIntegerNumerator q₀ w (l.1.map f) x : ℤ) -
        (alignmentNaturalBlockProduct x (T.image f) : ℤ) * alignmentPairResidue q₀ w (F.modulus w) (l.1.map f) x := by
    intro l hl
    simpa only [AlignmentAddingPair.map, htarget l hl] using
      alignmentPairProgression_exact hF hq hw x hx (l.1.map f)
  have h := selected_alignment_array_own_word f x (F.modulus w)
    (fun e => alignmentPairResidue q₀ w (F.modulus w) e x)
    (fun e => alignmentPairProgression q₀ w (F.modulus w) e x)
    (fun e => alignmentIntegerNumerator q₀ w e x) q₀ b T word htarget he p
    (selectedAlignmentSlotExtension f v) 0
  simpa only [selected_alignment_slot_extension_add, zero_add, alignmentIntegerArrayArgument,
    alignmentIntegerArrayProgression, Pi.zero_apply, zero_mul, ite_self,
    Finset.sum_const_zero, mul_zero, add_zero] using h

/-- A concrete sufficient lower boundary for converting the signed pivot
into a positive natural coordinate, using the proved master residue bound. -/
theorem selected_alignment_route_pivot_positive {d n M : ℕ} {i : Fin n}
    {A : Finset ℚ} {P : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A P F) (f : Fin n ↪o Fin M)
    {q₀ w : ℕ} (hq : 0 < q₀) (hw : q₀+1 ≤ w)
    (x : Fin M → ℕ) (hx : ∀ j, Nat.Coprime (x j) (primorial w))
    (v : AlignmentAddingPair n i → ℤ) (p : ℤ)
    (hp : ((F.modulus w : ℕ)^2 : ℤ) *
      alignmentIntegerSlotWeight (selectedAlignmentSlotExtension f v) < p) :
    0 < p + alignmentIntegerSlotShift
      (fun e => alignmentPairResidue q₀ w (F.modulus w) e x)
      (selectedAlignmentSlotExtension f v) := by
  have hbound := alignmentIntegerSlotShift_bound
    (fun e : AlignmentAddingPair M (f i) => alignmentPairResidue q₀ w (F.modulus w) e x)
    (selectedAlignmentSlotExtension f v) ((F.modulus w : ℕ)^2)
    (fun e => (alignmentPairResidue_master_data hF hq hw x hx e).2.1.le)
  simp only [Nat.cast_pow] at hbound
  have hneg := (abs_le.mp hbound).1
  omega

/-- The actual residue shift preserves the original primorial congruence,
so passing to a nonnegative natural pivot preserves admissibility. -/
theorem selected_alignment_shifted_pivot_coprime {d n M : ℕ} {i : Fin n}
    {A : Finset ℚ} {P : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A P F) (f : Fin n ↪o Fin M)
    {q₀ w : ℕ} (hq : 0 < q₀) (hw : q₀+1 ≤ w)
    (x : Fin M → ℕ) (hx : ∀ j, Nat.Coprime (x j) (primorial w))
    (v : AlignmentAddingPair n i → ℤ) (p : ℕ) (hp : Nat.Coprime p (primorial w))
    (hboundary : 0 ≤ (p : ℤ)+alignmentIntegerSlotShift
      (fun e => alignmentPairResidue q₀ w (F.modulus w) e x)
      (selectedAlignmentSlotExtension f v)) :
    Nat.Coprime ((p : ℤ)+alignmentIntegerSlotShift
      (fun e => alignmentPairResidue q₀ w (F.modulus w) e x)
      (selectedAlignmentSlotExtension f v)).toNat (primorial w) := by
  have hd := alignmentIntegerSlotShift_divisible
    (fun e : AlignmentAddingPair M (f i) => alignmentPairResidue q₀ w (F.modulus w) e x)
    (selectedAlignmentSlotExtension f v) (primorial w)
    (fun e => (alignmentPairResidue_master_data hF hq hw x hx e).2.2.1)
  have hz : Int.ModEq (primorial w) (p : ℤ)
      (((p : ℤ)+alignmentIntegerSlotShift
        (fun e => alignmentPairResidue q₀ w (F.modulus w) e x)
        (selectedAlignmentSlotExtension f v)).toNat : ℤ) := by
    rw [Int.toNat_of_nonneg hboundary, Int.modEq_iff_dvd, add_sub_cancel_left]
    exact hd
  have hn := Int.natCast_modEq_iff.mp hz
  rw [Nat.coprime_iff_gcd_eq_one, ← hn.gcd_eq]
  exact hp

end Hindman168
