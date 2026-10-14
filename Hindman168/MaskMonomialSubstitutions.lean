import Hindman168.MaskDescendantProductSplit

/-! Integer monomials under a chosen mask substitution. Balanced
integer division is used only on its admissible locus; after absorption
all surviving supports have a genuine integer scalar parameter. -/

namespace Hindman168

open scoped BigOperators Classical

variable {m : ℕ}

noncomputable def maskCoordinateMonomial (V : Finset (Fin (m + 1)))
    (z : Fin (m + 1) → ℤ) : ℤ := ∏ j ∈ V, z j

namespace MaskColumnPlan

variable {S U : Finset (Fin (m + 1))}

noncomputable def monomialScalar (P : MaskColumnPlan S U) (p q : ℕ)
    (V : Finset (Fin (m + 1))) : ℤ :=
  ∏ j ∈ V, (P.absorbedScalar p q (P.tag j) : ℤ)

theorem absorbedCoordinates_scaled (P : MaskColumnPlan S U) (p q : ℕ)
    (z : Fin (m + 1) → ℤ) (j : Fin (m + 1)) :
    P.absorbedCoordinates p q z j = (P.absorbedScalar p q (P.tag j) : ℤ) * z j := by
  cases P with
  | outside u hu hU =>
    by_cases hj : j = u
    all_goals simp [absorbedCoordinates, absorbedScalar, tag, maskSingleScalar, hj]
  | balanced u v hu hv huU hvU hne =>
    by_cases hj : j = u
    all_goals by_cases hv' : j = v
    all_goals simp [absorbedCoordinates, maskAbsorbedCoordinates, absorbedScalar, tag,
      maskAbsorbedScalar, hj, hv', hne, Ne.symm hne]

theorem monomial_absorbed (P : MaskColumnPlan S U) (p q : ℕ)
    (V : Finset (Fin (m + 1))) (z : Fin (m + 1) → ℤ) :
    maskCoordinateMonomial V (P.absorbedCoordinates p q z) =
      P.monomialScalar p q V * maskCoordinateMonomial V z := by
  unfold maskCoordinateMonomial monomialScalar
  simp_rw [P.absorbedCoordinates_scaled p q z]
  exact Finset.prod_mul_distrib

theorem monomialScalar_outside (u : Fin (m + 1)) (hu : u ∈ S) (hU : u ∉ U)
    (p q : ℕ) (V : Finset (Fin (m + 1))) :
    (MaskColumnPlan.outside u hu hU).monomialScalar p q V = if u ∈ V then (p : ℤ) else 1 := by
  simp [monomialScalar, absorbedScalar, tag, maskSingleScalar, Finset.prod_ite_eq']

theorem monomialScalar_balanced (u v : Fin (m + 1)) (hu : u ∈ S) (hv : v ∈ S)
    (huU : u ∈ U) (hvU : v ∈ U) (hne : u ≠ v) (p q : ℕ)
    (V : Finset (Fin (m + 1))) :
    (MaskColumnPlan.balanced u v hu hv huU hvU hne).monomialScalar p q V =
      (if u ∈ V then (q : ℤ) else 1) * (if v ∈ V then (p : ℤ) else 1) := by
  have h : ∀ j : Fin (m + 1),
      ((MaskColumnPlan.balanced u v hu hv huU hvU hne).absorbedScalar p q
        ((MaskColumnPlan.balanced u v hu hv huU hvU hne).tag j) : ℤ) =
        (if j = u then (q : ℤ) else 1) * (if j = v then (p : ℤ) else 1) := by
    intro j
    by_cases hj : j = u
    all_goals by_cases hjv : j = v
    all_goals simp [absorbedScalar, tag, maskAbsorbedScalar, hj, hjv, hne, Ne.symm hne]
  unfold monomialScalar
  simp_rw [h]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_ite_eq']

theorem monomial_preserved (P : MaskColumnPlan S U) (p : ℕ)
    (z : Fin (m + 1) → ℤ) (hd : P.admissible p z) :
    maskCoordinateMonomial U (P.coordinates p z) = maskCoordinateMonomial U z := by
  cases P with
  | outside u hu hU =>
    unfold maskCoordinateMonomial
    apply Finset.prod_congr rfl
    intro j hj
    have hjn : j ≠ u := ne_of_mem_of_not_mem hj hU
    simp [coordinates, hjn]
  | balanced u v hu hv huU hvU hne =>
    exact maskBalancedCoordinates_preserves_product U u v huU hvU hne p z hd

end MaskColumnPlan

end Hindman168
