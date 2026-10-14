import Hindman168.StrongStatement
import Hindman168.QuantitativeSeparation
import Mathlib.Data.Finset.Sort

/-!
# The elementary implication from the finite conjecture to rapid separation

All results in this module are conditional on `FiniteConjecture`; no new
axiom or proof of that premise is introduced here.
-/

namespace Hindman168
open scoped BigOperators

/-- Refinement and deletion yield arbitrarily large monochromatic sets above
any threshold, with every ordered pair separated by a prescribed real power. -/
theorem finite_implies_separated_sets (h : FiniteConjecture)
    (r : ℕ) (color : ℕ → Fin r) (m T : ℕ) (E : ℝ) (hE : 0 < E) :
    ∃ A : Finset ℕ, m ≤ A.card ∧ (∀ a ∈ A, T < a) ∧
      (∀ a ∈ A, ∀ b ∈ A, 1 < a → a < b → (a : ℝ) ^ E < b) ∧
      MonoFSFP color A := by
  classical
  obtain ⟨K, χ, hχ⟩ := exists_power_separating_coloring E hE
  let e := Fintype.equivFin (Fin r × Fin K)
  let coloring : ℕ → Fin (Fintype.card (Fin r × Fin K)) :=
    fun n => e (color n, χ n)
  obtain ⟨B, hBcard, c, hB⟩ := h _ coloring (m + (T + 1))
  let A := B \ Finset.range (T + 1)
  have hsub : A ⊆ B := Finset.sdiff_subset
  have hmono : ∀ S : Finset ℕ, S ⊆ A → S.Nonempty →
      (color (∑ x ∈ S, x), χ (∑ x ∈ S, x)) = e.symm c ∧
      (color (∏ x ∈ S, x), χ (∏ x ∈ S, x)) = e.symm c := by
    intro S hS hne
    obtain ⟨hs, hp⟩ := hB S (hS.trans hsub) hne
    constructor
    · exact e.injective (by simpa [coloring] using hs)
    · exact e.injective (by simpa [coloring] using hp)
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  · have hi : (B ∩ Finset.range (T + 1)).card ≤ T + 1 := by
      simpa using Finset.card_le_card (Finset.inter_subset_right (s₁ := B)
        (s₂ := Finset.range (T + 1)))
    have hc := Finset.card_sdiff_add_card_inter B (Finset.range (T + 1))
    dsimp [A]
    omega
  · intro a ha
    have := (Finset.mem_sdiff.mp ha).2
    simpa using this
  · intro a ha b hb ha1 hab
    apply hχ a b ha1 hab.le
    have hs := (hmono {b} (by simpa using hb) (by simp)).2
    have hp := (hmono {a, b}
      (Finset.insert_subset_iff.mpr ⟨ha, Finset.singleton_subset_iff.mpr hb⟩)
      (Finset.insert_nonempty _ _)).2
    have hne : a ≠ b := ne_of_lt hab
    have hs' := congrArg Prod.snd hs
    have hp' := congrArg Prod.snd hp
    simpa [hne] using hp'.trans hs'.symm
  · refine ⟨(e.symm c).1, ?_⟩
    intro S hS hne
    obtain ⟨hs, hp⟩ := hmono S hS hne
    exact ⟨congrArg Prod.fst hs, congrArg Prod.fst hp⟩

/-- Increasing enumeration preserves the entire finite-sums/products witness. -/
theorem finite_implies_separated_indexed (h : FiniteConjecture)
    (r : ℕ) (color : ℕ → Fin r) (m T : ℕ) (E : ℝ) (hE : 0 < E) :
    ∃ a : Fin m → ℕ, StrictMono a ∧ (∀ i, T < a i) ∧
      (∀ i j, i < j → 1 < a i → (a i : ℝ) ^ E < a j) ∧
      ∃ c : Fin r, ∀ S : Finset (Fin m), S.Nonempty →
        color (∑ i ∈ S, a i) = c ∧ color (∏ i ∈ S, a i) = c := by
  classical
  obtain ⟨A, hcard, hT, hgap, c, hmono⟩ :=
    finite_implies_separated_sets h r color m T E hE
  let e : Fin A.card ↪o ℕ := A.orderEmbOfFin rfl
  let a : Fin m → ℕ := fun i => e (Fin.castLE hcard i)
  have hamem (i : Fin m) : a i ∈ A := A.orderEmbOfFin_mem rfl _
  have hstrict : StrictMono a := by
    intro i j hij
    exact e.strictMono hij
  refine ⟨a, hstrict, fun i => hT _ (hamem i), ?_, c, ?_⟩
  · intro i j hij hi
    exact hgap _ (hamem i) _ (hamem j) hi (hstrict hij)
  · intro S hS
    have himage : S.image a ⊆ A := by
      intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact hamem i
    have hm := hmono (S.image a) himage (hS.image a)
    simpa [Finset.sum_image hstrict.injective.injOn,
      Finset.prod_image hstrict.injective.injOn] using hm

/-- A crude bound by the largest predecessor converts pairwise power gaps
into the exact sum-plus-product separation in the paper's statement. -/
theorem quantitative_separation_of_pairwise {m : ℕ} (a : Fin m → ℕ)
    (R D : ℝ) (hR : 2 ≤ R) (hD : 1 ≤ D) (hstrict : StrictMono a)
    (hlarge : ∀ i, max 2 (R * ((m : ℝ) + 1) ^ D) < (a i : ℝ))
    (hgap : ∀ i j, i < j → (a i : ℝ) ^ ((m : ℝ) * D + 1) < a j) :
    ∀ i, R * ((∑ j ∈ Finset.univ.filter (fun j : Fin m => j < i), (a j : ℝ)) +
      (∏ j ∈ Finset.univ.filter (fun j : Fin m => j < i), (a j : ℝ))) ^ D < (a i : ℝ) := by
  classical
  intro i
  let S := Finset.univ.filter (fun j : Fin m => j < i)
  have hm : 1 ≤ m := by have := i.isLt; omega
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hR0 : 0 ≤ R := by linarith
  have hD0 : 0 ≤ D := by linarith
  have hcoeff : R ≤ R * ((m : ℝ) + 1) ^ D := by
    have hone : (1 : ℝ) ≤ ((m : ℝ) + 1) ^ D :=
      Real.one_le_rpow (by linarith) hD0
    nlinarith
  by_cases hi : i.val = 0
  · have hS : S = ∅ := by
      ext j
      simp [S, Fin.lt_def, hi]
    change R * ((∑ j ∈ S, (a j : ℝ)) + (∏ j ∈ S, (a j : ℝ))) ^ D < _
    simp only [hS, Finset.sum_empty, Finset.prod_empty, zero_add, Real.one_rpow, mul_one]
    exact lt_of_le_of_lt (le_trans hcoeff (le_max_right _ _)) (hlarge i)
  · let p : Fin m := ⟨i.val - 1, by omega⟩
    have hpi : p < i := by show i.val - 1 < i.val; omega
    let b : ℝ := a p
    have hb : 2 < b := lt_of_le_of_lt (le_max_left _ _) (hlarge p)
    have hb0 : 0 ≤ b := by linarith
    have hb1 : 1 ≤ b := by linarith
    have hbound : ∀ j ∈ S, (a j : ℝ) ≤ b := by
      intro j hj
      have hji := (Finset.mem_filter.mp hj).2
      have hjp : j ≤ p := by
        show j.val ≤ i.val - 1
        have : j.val < i.val := hji
        omega
      change (a j : ℝ) ≤ (a p : ℝ)
      exact_mod_cast hstrict.monotone hjp
    have hcard : S.card ≤ m := by simpa using Finset.card_le_univ S
    have hsum : (∑ j ∈ S, (a j : ℝ)) ≤ (m : ℝ) * b := by
      have hs := Finset.sum_le_card_nsmul S (fun j => (a j : ℝ)) b hbound
      have hc : (S.card : ℝ) ≤ m := by exact_mod_cast hcard
      simp only [nsmul_eq_mul] at hs
      exact hs.trans (mul_le_mul_of_nonneg_right hc hb0)
    have hprod : (∏ j ∈ S, (a j : ℝ)) ≤ b ^ m := by
      have hp : (∏ j ∈ S, (a j : ℝ)) ≤ ∏ _j ∈ S, b :=
        Finset.prod_le_prod (by intro j hj; positivity) hbound
      simp only [Finset.prod_const] at hp
      exact hp.trans (pow_le_pow_right₀ hb1 hcard)
    have hbpow : b ≤ b ^ m := by
      simpa using pow_le_pow_right₀ hb1 hm
    have hboth : (∑ j ∈ S, (a j : ℝ)) + (∏ j ∈ S, (a j : ℝ)) ≤
        ((m : ℝ) + 1) * b ^ m := by nlinarith
    have hboth0 : 0 ≤ (∑ j ∈ S, (a j : ℝ)) + (∏ j ∈ S, (a j : ℝ)) := by
      positivity
    have hpower := Real.rpow_le_rpow hboth0 hboth hD0
    have hpower' : R * ((∑ j ∈ S, (a j : ℝ)) + (∏ j ∈ S, (a j : ℝ))) ^ D ≤
        (R * ((m : ℝ) + 1) ^ D) * b ^ ((m : ℝ) * D) := by
      calc
        _ ≤ R * (((m : ℝ) + 1) * b ^ m) ^ D :=
          mul_le_mul_of_nonneg_left hpower hR0
        _ = _ := by
          rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
            ← Real.rpow_mul hb0]
          ring
    have hcoefb : R * ((m : ℝ) + 1) ^ D < b :=
      lt_of_le_of_lt (le_max_right _ _) (hlarge p)
    have hmul : (R * ((m : ℝ) + 1) ^ D) * b ^ ((m : ℝ) * D) <
        b ^ ((m : ℝ) * D + 1) := by
      rw [Real.rpow_add (by linarith), Real.rpow_one]
      have hpos : 0 < b ^ ((m : ℝ) * D) := Real.rpow_pos_of_pos (by linarith) _
      nlinarith
    exact lt_trans (lt_of_le_of_lt hpower' hmul) (hgap p i hpi)

/-- The rapid separation in the strong statement costs no additional
conjectural input beyond the finite sums/products conjecture itself. -/
theorem finite_implies_strong (h : FiniteConjecture) : StrongConjecture := by
  intro r color m R D hR hD
  have hD0 : 0 ≤ D := by linarith
  have hE : 0 < (m : ℝ) * D + 1 := by positivity
  obtain ⟨T, hT⟩ := exists_nat_gt (max 2 (R * ((m : ℝ) + 1) ^ D))
  obtain ⟨a, hstrict, haT, hgap, c, hmono⟩ :=
    finite_implies_separated_indexed h r color m T ((m : ℝ) * D + 1) hE
  have hlarge : ∀ i, max 2 (R * ((m : ℝ) + 1) ^ D) < (a i : ℝ) := by
    intro i
    exact hT.trans (by exact_mod_cast haT i)
  have htwo (i) : (2 : ℝ) < a i := (le_max_left _ _).trans_lt (hlarge i)
  refine ⟨a, hstrict, ?_, ?_, c, hmono⟩
  · intro i
    have := htwo i
    exact_mod_cast (show (0 : ℝ) < a i by linarith)
  · apply quantitative_separation_of_pairwise a R D hR hD hstrict hlarge
    intro i j hij
    apply hgap i j hij
    have := htwo i
    exact_mod_cast (show (1 : ℝ) < a i by linarith)

/-- This equivalence is conditional mathematics, not a proof of either conjecture. -/
theorem finite_iff_strong : FiniteConjecture ↔ StrongConjecture :=
  ⟨finite_implies_strong, strong_implies_finite⟩

end Hindman168
