import Hindman168.UpstreamNilpotentRecurrence
import Hindman168.AlignmentMonomialRecurrenceInput

/-!
The recurrence input of the original finite-word plan, discharged by the
actual nilpotent polynomial recurrence proof. Ordered words and handedness
are preserved exactly; the parameter is strictly positive.
-/
namespace Hindman168
open Polynomial

/-- The polynomial-word encoding evaluates to the existing ordered monomial word. -/
theorem alignmentMonomialWord_polynomial_encoding {E G : Type*} [Group G]
    (L : E → G) (degree : E → ℕ) (w : List E) (k : ℕ) :
    OAI.ConstructedWordPlan.NilpotentPolynomialRecurrence.word
      (w.map (fun e => (L e, (X : Polynomial ℤ)^degree e))) (k : ℤ) =
      alignmentMonomialWord L degree w k := by
  induction w with
  | nil => simp [OAI.ConstructedWordPlan.NilpotentPolynomialRecurrence.word, alignmentMonomialWord]
  | cons e w ih =>
      simpa only [List.map_cons, OAI.ConstructedWordPlan.NilpotentPolynomialRecurrence.word,
        List.prod_cons, Polynomial.eval_pow, Polynomial.eval_X, ← Nat.cast_pow, zpow_natCast,
        alignmentMonomialWord] using congrArg (fun z => L e ^ (k ^ degree e) * z) ih

/-- Actual recurrence in every nilpotent group, for the exact monomial-word API. -/
theorem alignment_nilpotent_monomial_recurrence {E G Color : Type*}
    [Group G] [Group.IsNilpotent G] [Finite Color]
    (L : E → G) (degree : E → ℕ) (hdegree : ∀ e, 0 < degree e)
    (words : Finset (List E)) (χ : G → Color) (N : ℕ) :
    ∃ k J, N < k ∧ ∀ w ∈ words,
      χ J = χ (alignmentMonomialWord L degree w k * J) := by
  classical
  letI : Fintype Color := Fintype.ofFinite Color
  let encode : List E → List (G × Polynomial ℤ) :=
    List.map (fun e => (L e, (X : Polynomial ℤ)^degree e))
  have hzero : ∀ w ∈ words.image encode, ∀ ap ∈ w, ap.2.eval 0 = 0 := by
    intro w hw ap hap
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hap
    simp only [Polynomial.eval_pow, Polynomial.eval_X]
    exact zero_pow (hdegree e).ne'
  obtain ⟨k, hk, J, hJ⟩ :=
    OAI.ConstructedWordPlan.NilpotentPolynomialRecurrence.coloring_recurrence
      (words.image encode) hzero χ N
  refine ⟨k, J, hk, ?_⟩
  intro w hw
  have h := hJ (encode w) (Finset.mem_image.mpr ⟨w, hw, rfl⟩)
  rw [alignmentMonomialWord_polynomial_encoding] at h
  exact h.symm

/-- The previously explicit recurrence obligation of Alignment is now a theorem. -/
theorem hasAlignmentMonomialRecurrence (s : ℕ) : HasAlignmentMonomialRecurrence s := by
  intro E Color _ _ degree hdegree words χ
  letI : Group.IsNilpotent (AlignmentFreeNilpotent E s) :=
    Subgroup.nilpotent_iff_lowerCentralSeries.mpr
      ⟨s, alignmentFreeNilpotent_lowerCentralSeries E s⟩
  exact alignment_nilpotent_monomial_recurrence (alignmentFreeGenerator s) degree
    hdegree words χ 0

end Hindman168
