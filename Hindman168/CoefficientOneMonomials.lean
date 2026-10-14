import Hindman168.MaskFlattenedCoefficients

/-! Coefficient-one monomials are stable under the actual row operations. -/

namespace Hindman168

open scoped BigOperators Classical

def CoefficientOneMonomial {σ : Type*} (P : MvPolynomial σ ℤ) : Prop :=
  ∃ e : σ →₀ ℕ, P = MvPolynomial.monomial e 1

theorem coefficientOneMonomial_one (σ : Type*) : CoefficientOneMonomial (1 : MvPolynomial σ ℤ) :=
  ⟨0, rfl⟩

theorem coefficientOneMonomial_X {σ : Type*} (i : σ) :
    CoefficientOneMonomial (MvPolynomial.X i : MvPolynomial σ ℤ) :=
  ⟨Finsupp.single i 1, rfl⟩

theorem CoefficientOneMonomial.mul {σ : Type*} {P Q : MvPolynomial σ ℤ}
    (hP : CoefficientOneMonomial P) (hQ : CoefficientOneMonomial Q) :
    CoefficientOneMonomial (P * Q) := by
  obtain ⟨e, rfl⟩ := hP
  obtain ⟨f, rfl⟩ := hQ
  exact ⟨e + f, by simp⟩

theorem CoefficientOneMonomial.rename {σ τ : Type*} {P : MvPolynomial σ ℤ}
    (hP : CoefficientOneMonomial P) (j : σ → τ) :
    CoefficientOneMonomial (MvPolynomial.rename j P) := by
  obtain ⟨e, rfl⟩ := hP
  exact ⟨e.mapDomain j, MvPolynomial.rename_monomial j e 1⟩

theorem CoefficientOneMonomial.ne_zero {σ : Type*} {P : MvPolynomial σ ℤ}
    (hP : CoefficientOneMonomial P) : P ≠ 0 := by
  obtain ⟨e, rfl⟩ := hP
  simp

theorem flattenedFreshMaskMultiplier_monomial (n : ℕ) (b : Bool) (t : Fin 3) :
    CoefficientOneMonomial (flattenedFreshMaskMultiplier n b t) := by
  unfold flattenedFreshMaskMultiplier
  split_ifs
  · exact coefficientOneMonomial_one _
  · exact coefficientOneMonomial_X _
  · exact coefficientOneMonomial_X _

theorem flattenedFreshMaskMultiplier_vars_iff (n : ℕ) (b : Bool) (t : Fin 3)
    (v : Fin (2 + n)) :
    v ∈ (flattenedFreshMaskMultiplier n b t).vars ↔
      (t = 1 ∧ v = freshMaskNewSlot n b) ∨
      (t = 2 ∧ v = freshMaskNewSlot n (!b)) := by
  fin_cases t <;> simp [flattenedFreshMaskMultiplier, MvPolynomial.vars_one]

theorem flattenedFreshMaskMultiplier_vars_no_old (n : ℕ) (b : Bool) (t : Fin 3) (k : Fin n) :
    freshMaskOldSlot n k ∉ (flattenedFreshMaskMultiplier n b t).vars := by
  intro hv
  rcases (flattenedFreshMaskMultiplier_vars_iff n b t _).mp hv with ⟨_, h⟩ | ⟨_, h⟩
  · exact freshMaskNewSlot_ne_old n b k h.symm
  · exact freshMaskNewSlot_ne_old n (!b) k h.symm

theorem flattenedFreshMaskMultiplier_vars_collision (n : ℕ) (b : Bool) (s t : Fin 3)
    (v : Fin (2 + n))
    (hs : v ∈ (flattenedFreshMaskMultiplier n b s).vars)
    (ht : v ∈ (flattenedFreshMaskMultiplier n b t).vars) : s = t ∧ s ≠ 0 := by
  rcases (flattenedFreshMaskMultiplier_vars_iff n b s v).mp hs with ⟨rfl, hv1⟩ | ⟨rfl, hv1⟩
  <;> rcases (flattenedFreshMaskMultiplier_vars_iff n b t v).mp ht with ⟨rfl, hv2⟩ | ⟨rfl, hv2⟩
  · exact ⟨rfl, by decide⟩
  · have h := freshMaskNewSlot_injective n (hv1.symm.trans hv2)
    cases b <;> cases h
  · have h := freshMaskNewSlot_injective n (hv1.symm.trans hv2)
    cases b <;> cases h
  · exact ⟨rfl, by decide⟩

end Hindman168
