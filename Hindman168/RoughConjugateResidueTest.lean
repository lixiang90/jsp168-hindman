import Hindman168.RoughConjugateOrbitMap
import Mathlib.Tactic.Group
import Mathlib.Data.Real.Basic

namespace Hindman168

theorem rough_conjugate_residue_test {G : Type*} [Group G]
    (Γ L : Subgroup G) (σ ell right : G) (h : L)
    (hcoset : (QuotientGroup.mk right : G ⧸ Γ) = QuotientGroup.mk σ)
    (F : G ⧸ Γ → ℝ) (f : L ⧸ (roughConjugateSubgroup Γ σ).comap L.subtype → ℝ)
    (ε : ℝ)
    (happrox : ∀ x, |F (roughConjugateOrbitMap Γ L σ ell x)-f x| ≤ ε) :
    |F (QuotientGroup.mk (ell*h.val*right))-f (QuotientGroup.mk h)| ≤ ε := by
  have he : (QuotientGroup.mk (ell*h.val*right) : G ⧸ Γ) =
      QuotientGroup.mk (ell*h.val*σ) := by
    apply QuotientGroup.eq.mpr
    have hg : (ell*h.val*right)⁻¹*(ell*h.val*σ) = right⁻¹*σ := by group
    rw [hg]
    exact QuotientGroup.eq.mp hcoset
  rw [he]
  exact happrox (QuotientGroup.mk h)

theorem rough_frozen_conjugate_residue_test {G : Type*} [Group G]
    (Γ L : Subgroup G) (σ ell right g : G) (h : L)
    (hcoset : (QuotientGroup.mk right : G ⧸ Γ) = QuotientGroup.mk σ)
    (F : G ⧸ Γ → ℝ) (f : L ⧸ (roughConjugateSubgroup Γ σ).comap L.subtype → ℝ)
    (εfreeze εapprox : ℝ)
    (hfreeze : |F (QuotientGroup.mk g)-F (QuotientGroup.mk (ell*h.val*right))| ≤ εfreeze)
    (happrox : ∀ x, |F (roughConjugateOrbitMap Γ L σ ell x)-f x| ≤ εapprox) :
    |F (QuotientGroup.mk g)-f (QuotientGroup.mk h)| ≤ εfreeze+εapprox := by
  exact (abs_sub_le _ _ _).trans (add_le_add hfreeze
    (rough_conjugate_residue_test Γ L σ ell right h hcoset F f εapprox happrox))

end Hindman168
