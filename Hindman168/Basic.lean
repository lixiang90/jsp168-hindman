import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic

/-!
# JSP-000168 / Erdős #172: precise target and finite-set interfaces

The mathematical route under audit is OpenAI's September 23, 2026 preprint
"Monochromatic finite sums and products in the positive integers".
The conjecture statement agrees with google-deepmind/formal-conjectures,
FormalConjectures/ErdosProblems/172.lean (Apache-2.0).

This file does not assert the general conjecture as a proved theorem.
The interfaces and elementary reductions below are checked separately.
-/

namespace Hindman168

open scoped BigOperators

/-- A common color for every nonempty subset sum and subset product. -/
def MonoFSFP {r : ℕ} (color : ℕ → Fin r) (A : Finset ℕ) : Prop :=
  ∃ c : Fin r, ∀ S : Finset ℕ, S ⊆ A → S.Nonempty →
    color (∑ x ∈ S, x) = c ∧ color (∏ x ∈ S, x) = c

/-- The full finite sums/products conjecture. This is a definition, not a proof. -/
def FiniteConjecture : Prop :=
  ∀ (r : ℕ) (color : ℕ → Fin r) (m : ℕ),
    ∃ A : Finset ℕ, m ≤ A.card ∧ MonoFSFP color A

/-- The original subtype formulation used by formal-conjectures. -/
def SubtypeConjecture : Prop :=
  ∀ (r : ℕ) (color : ℕ → Fin r) (m : ℕ),
    ∃ A : Finset ℕ, m ≤ A.card ∧ ∃ c : Fin r,
      ∀ S : Finset A, S.Nonempty →
        color (∑ x ∈ S, (x : ℕ)) = c ∧ color (∏ x ∈ S, (x : ℕ)) = c

/-- An indexed version of the paper's conclusion, before additional separation. -/
def IndexedWitness {r m : ℕ} (color : ℕ → Fin r) : Prop :=
  ∃ a : Fin m → ℕ, Function.Injective a ∧ (∀ i, 0 < a i) ∧
    ∃ c : Fin r, ∀ S : Finset (Fin m), S.Nonempty →
      color (∑ i ∈ S, a i) = c ∧ color (∏ i ∈ S, a i) = c

theorem mono_empty {r : ℕ} (color : ℕ → Fin r) : MonoFSFP color ∅ := by
  refine ⟨color 0, ?_⟩
  intro S hS hne
  have hzero : S = ∅ := Finset.subset_empty.mp hS
  subst S
  exact (Finset.not_nonempty_empty hne).elim

theorem mono_singleton {r : ℕ} (color : ℕ → Fin r) (a : ℕ) :
    MonoFSFP color {a} := by
  refine ⟨color a, ?_⟩
  intro S hS hne
  obtain ⟨b, hb⟩ := hne
  have hba : b = a := Finset.mem_singleton.mp (hS hb)
  have ha : a ∈ S := hba ▸ hb
  have heq : S = {a} := Finset.Subset.antisymm hS (by simpa using ha)
  simp [heq]

theorem size_zero {r : ℕ} (color : ℕ → Fin r) :
    ∃ A : Finset ℕ, 0 ≤ A.card ∧ MonoFSFP color A :=
  ⟨∅, Nat.zero_le _, mono_empty color⟩

theorem size_one {r : ℕ} (color : ℕ → Fin r) :
    ∃ A : Finset ℕ, 1 ≤ A.card ∧ MonoFSFP color A := by
  exact ⟨{1}, by simp, mono_singleton color 1⟩

/-- Passage from an injective indexed witness to a set of exactly `m` elements. -/
theorem indexed_to_finset {r m : ℕ} (color : ℕ → Fin r)
    (h : IndexedWitness (m := m) color) :
    ∃ A : Finset ℕ, A.card = m ∧ (∀ x ∈ A, 0 < x) ∧ MonoFSFP color A := by
  classical
  obtain ⟨a, hinj, hpos, c, hcolor⟩ := h
  let A := Finset.univ.image a
  refine ⟨A, ?_, ?_, c, ?_⟩
  · dsimp [A]
    rw [Finset.card_image_of_injective _ hinj]
    simp
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hpos i
  · intro S hsub hne
    let I : Finset (Fin m) := Finset.univ.filter (fun i => a i ∈ S)
    have himage : I.image a = S := by
      ext x
      constructor
      · rintro hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        exact (Finset.mem_filter.mp hi).2
      · intro hx
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (hsub hx)
        refine Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hi⟩
        simpa [hi] using hx
    have hine : I.Nonempty := by
      obtain ⟨x, hx⟩ := hne
      obtain ⟨i, hi, _⟩ := Finset.mem_image.mp (himage ▸ hx)
      exact ⟨i, hi⟩
    have hsum : (∑ x ∈ S, x) = ∑ i ∈ I, a i := by
      rw [← himage, Finset.sum_image hinj.injOn]
    have hprod : (∏ x ∈ S, x) = ∏ i ∈ I, a i := by
      rw [← himage, Finset.prod_image hinj.injOn]
    simpa only [hsum, hprod] using hcolor I hine

/-- The set formulation implies precisely the original subtype formulation. -/
theorem finite_to_subtype (h : FiniteConjecture) : SubtypeConjecture := by
  classical
  intro r color m
  obtain ⟨A, hcard, c, hmono⟩ := h r color m
  refine ⟨A, hcard, c, ?_⟩
  intro S hne
  let T : Finset ℕ := S.image (fun x : A => (x : ℕ))
  have hT : T ⊆ A := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
    exact y.property
  have hTne : T.Nonempty := hne.image _
  have hm := hmono T hT hTne
  dsimp [T] at hm
  simpa only [Finset.sum_image Subtype.val_injective.injOn,
    Finset.prod_image Subtype.val_injective.injOn] using hm

end Hindman168
