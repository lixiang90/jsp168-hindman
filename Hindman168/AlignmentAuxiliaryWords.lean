import Hindman168.AlignmentCanonicalTargets

/-! Auxiliary translations are commutative integer vectors even when
the actual ordered group words are not. Both signs of powers are included. -/

namespace Hindman168
open scoped Classical

theorem alignment_action_integer_translation {G X : Type*} [Group G] [MulAction G X]
    (g : G) (f : X → ℤ) (t : ℤ) (hstep : ∀ x, f (g • x) = f x + t)
    (z : ℤ) (x : X) : f (g ^ z • x) = f x + z * t := by
  have hinv : ∀ x, f (g⁻¹ • x) = f x - t := by
    intro x
    have h := hstep (g⁻¹ • x)
    rw [smul_inv_smul] at h
    omega
  induction z using Int.induction_on generalizing x with
  | zero => simp only [zpow_zero, one_smul, zero_mul, add_zero]
  | succ n ih =>
    rw [zpow_add, zpow_one, mul_smul, ih, hstep]
    ring
  | pred n ih =>
    rw [zpow_sub, zpow_one, mul_smul, ih, hinv]
    ring

noncomputable def alignmentAuxiliaryUnit {n : ℕ} {i : Fin n}
    (e : AlignmentAddingPair n i) (z : ℤ) : AlignmentAddingPair n i → ℤ :=
  fun f => if f = e then z else 0

noncomputable def alignmentAuxiliaryWord {n : ℕ} {i : Fin n}
    (q₀ : ℕ) (b : Fin n → ℚ) : List (AlignmentAddingPair n i × ℚ) → (AlignmentAddingPair n i → ℤ)
  | [] => 0
  | l :: w => alignmentAuxiliaryUnit l.1 ⌊(q₀ : ℚ) * alignmentLetterScalar b l⌋ +
    alignmentAuxiliaryWord q₀ b w

noncomputable def alignmentAuxiliaryWordVisits {n : ℕ} {i : Fin n}
    (q₀ : ℕ) (b : Fin n → ℚ) :
    List (AlignmentAddingPair n i × ℚ) → Finset (AlignmentAddingPair n i → ℤ)
  | [] => {0}
  | l :: w =>
    let z := ⌊(q₀ : ℚ) * alignmentLetterScalar b l⌋
    alignmentAuxiliaryWordVisits q₀ b w ∪
      (Finset.Icc (min 0 z) (max 0 z)).image
        (fun m => alignmentAuxiliaryWord q₀ b w + alignmentAuxiliaryUnit l.1 m)

def alignmentWordActionVisit {n : ℕ} {i : Fin n} {G X : Type*}
    [Group G] [MulAction G X] (q₀ : ℕ) (b : Fin n → ℚ) (L : AlignmentAddingPair n i → G) :
    List (AlignmentAddingPair n i × ℚ) → X → X → Prop
  | [], x, visited => visited = x
  | l :: w, x, visited => alignmentWordActionVisit q₀ b L w x visited ∨
    ∃ m ∈ Finset.Icc (min 0 ⌊(q₀ : ℚ) * alignmentLetterScalar b l⌋)
      (max 0 ⌊(q₀ : ℚ) * alignmentLetterScalar b l⌋),
      visited = L l.1 ^ m • (alignmentWordValue q₀ b L w • x)

theorem alignmentAuxiliaryWord_append {n : ℕ} {i : Fin n}
    (q₀ : ℕ) (b : Fin n → ℚ) (v w : List (AlignmentAddingPair n i × ℚ)) :
    alignmentAuxiliaryWord q₀ b (v ++ w) =
      alignmentAuxiliaryWord q₀ b v + alignmentAuxiliaryWord q₀ b w := by
  induction v with
  | nil => simp only [List.nil_append, alignmentAuxiliaryWord, zero_add]
  | cons l v ih => simp only [List.cons_append, alignmentAuxiliaryWord, ih, add_assoc]

theorem alignmentLetter_auxiliary_translation {n : ℕ} {i : Fin n}
    {G X : Type*} [Group G] [MulAction G X]
    (L : AlignmentAddingPair n i → G) (position : X → AlignmentAddingPair n i → ℤ)
    (hL : ∀ e x f, position (L e • x) f = position x f + if f = e then 1 else 0)
    (e : AlignmentAddingPair n i) (z : ℤ) (x : X) :
    position (L e ^ z • x) = position x + alignmentAuxiliaryUnit e z := by
  funext f
  have h := alignment_action_integer_translation (L e) (fun x => position x f)
    (if f = e then 1 else 0) (fun x => hL e x f) z x
  simpa only [alignmentAuxiliaryUnit, Pi.add_apply, mul_ite, mul_one, mul_zero] using h

theorem alignmentWordValue_auxiliary_translation {n : ℕ} {i : Fin n}
    {G X : Type*} [Group G] [MulAction G X]
    (q₀ : ℕ) (b : Fin n → ℚ) (L : AlignmentAddingPair n i → G)
    (position : X → AlignmentAddingPair n i → ℤ)
    (hL : ∀ e x f, position (L e • x) f = position x f + if f = e then 1 else 0)
    (w : List (AlignmentAddingPair n i × ℚ)) (x : X) :
    position (alignmentWordValue q₀ b L w • x) = position x + alignmentAuxiliaryWord q₀ b w := by
  induction w with
  | nil => simp only [alignmentWordValue, one_smul, alignmentAuxiliaryWord, add_zero]
  | cons l w ih =>
    rw [alignmentWordValue, mul_smul, alignmentLetter_auxiliary_translation L position hL, ih]
    simp only [alignmentAuxiliaryWord]
    abel

theorem alignmentAuxiliaryWordVisits_zero {n : ℕ} {i : Fin n}
    (q₀ : ℕ) (b : Fin n → ℚ) (w : List (AlignmentAddingPair n i × ℚ)) :
    0 ∈ alignmentAuxiliaryWordVisits q₀ b w := by
  induction w with
  | nil => exact Finset.mem_singleton_self _
  | cons l w ih => exact Finset.mem_union_left _ ih

theorem alignmentAuxiliaryWordVisits_endpoint {n : ℕ} {i : Fin n}
    (q₀ : ℕ) (b : Fin n → ℚ) (w : List (AlignmentAddingPair n i × ℚ)) :
    alignmentAuxiliaryWord q₀ b w ∈ alignmentAuxiliaryWordVisits q₀ b w := by
  cases w with
  | nil => exact Finset.mem_singleton_self _
  | cons l w =>
    apply Finset.mem_union_right
    refine Finset.mem_image.mpr ⟨⌊(q₀ : ℚ) * alignmentLetterScalar b l⌋, ?_, ?_⟩
    · exact Finset.mem_Icc.mpr ⟨min_le_right _ _, le_max_right _ _⟩
    · exact add_comm _ _

theorem alignmentAuxiliaryWordVisits_power {n : ℕ} {i : Fin n}
    (q₀ : ℕ) (b : Fin n → ℚ) (l : AlignmentAddingPair n i × ℚ)
    (w : List (AlignmentAddingPair n i × ℚ)) (m : ℤ)
    (hm : m ∈ Finset.Icc (min 0 ⌊(q₀ : ℚ) * alignmentLetterScalar b l⌋)
      (max 0 ⌊(q₀ : ℚ) * alignmentLetterScalar b l⌋)) :
    alignmentAuxiliaryWord q₀ b w + alignmentAuxiliaryUnit l.1 m ∈
      alignmentAuxiliaryWordVisits q₀ b (l :: w) :=
  Finset.mem_union_right _ (Finset.mem_image.mpr ⟨m, hm, rfl⟩)

theorem alignmentWordActionVisit_displacement {n : ℕ} {i : Fin n}
    {G X : Type*} [Group G] [MulAction G X]
    (q₀ : ℕ) (b : Fin n → ℚ) (L : AlignmentAddingPair n i → G)
    (position : X → AlignmentAddingPair n i → ℤ)
    (hL : ∀ e x f, position (L e • x) f = position x f + if f = e then 1 else 0)
    (w : List (AlignmentAddingPair n i × ℚ)) (x visited : X)
    (hvisit : alignmentWordActionVisit q₀ b L w x visited) :
    ∃ d ∈ alignmentAuxiliaryWordVisits q₀ b w, position visited = position x + d := by
  induction w with
  | nil =>
    refine ⟨0, Finset.mem_singleton_self _, ?_⟩
    change visited = x at hvisit
    rw [hvisit, add_zero]
  | cons l w ih =>
    rcases hvisit with htail | ⟨m, hm, rfl⟩
    · obtain ⟨d, hd, heq⟩ := ih htail
      exact ⟨d, Finset.mem_union_left _ hd, heq⟩
    · refine ⟨alignmentAuxiliaryWord q₀ b w + alignmentAuxiliaryUnit l.1 m,
        alignmentAuxiliaryWordVisits_power q₀ b l w m hm, ?_⟩
      rw [alignmentLetter_auxiliary_translation L position hL,
        alignmentWordValue_auxiliary_translation q₀ b L position hL]
      exact add_assoc _ _ _

theorem alignmentWordActionVisit_in_slots {n : ℕ} {i : Fin n}
    {G X : Type*} [Group G] [MulAction G X]
    (q₀ : ℕ) (b : Fin n → ℚ) (L : AlignmentAddingPair n i → G)
    (position : X → AlignmentAddingPair n i → ℤ)
    (hL : ∀ e x f, position (L e • x) f = position x f + if f = e then 1 else 0)
    (w : List (AlignmentAddingPair n i × ℚ)) (x visited : X)
    (slots : Finset (AlignmentAddingPair n i → ℤ))
    (hsafe : ∀ d ∈ alignmentAuxiliaryWordVisits q₀ b w, position x + d ∈ slots)
    (hvisit : alignmentWordActionVisit q₀ b L w x visited) : position visited ∈ slots := by
  obtain ⟨d, hd, heq⟩ := alignmentWordActionVisit_displacement q₀ b L position hL w x visited hvisit
  rw [heq]
  exact hsafe d hd

end Hindman168
