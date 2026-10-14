import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Group.Subgroup.Lattice

/-! Exact coordinate elimination in arbitrary groups. Parameters live in an
additive group; no real topology, floor function, or lattice is needed. -/

namespace Hindman168

variable {G A : Type*} [Group G] [AddGroup A]

 theorem triangularZeroCoordinates_fin_reduction {d : ℕ} (Γ : Subgroup G)
    (c : G → Fin d → A) (u : Fin d → A → G)
    (hu : ∀ i z, u i z ∈ Γ)
    (hearlier : ∀ g i z j, j < i → c (g * u i z) j = c g j)
    (hpivot : ∀ g i z, c (g * u i z) i = c g i + z)
    (g : G) : ∃ x γ, γ ∈ Γ ∧ g = x * γ ∧ ∀ i, c x i = 0 := by
  have hstep : ∀ k ≤ d, ∃ x γ, γ ∈ Γ ∧ g = x * γ ∧
      ∀ i : Fin d, i.val < k → c x i = 0 := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨g, 1, Γ.one_mem, by simp, by intro i hi; omega⟩
    | succ k ih =>
      intro hk
      obtain ⟨x, γ, hγ, hg, hcoord⟩ := ih (by omega)
      let i : Fin d := ⟨k, by omega⟩
      let z : A := -c x i
      refine ⟨x * u i z, (u i z)⁻¹ * γ,
        Γ.mul_mem (Γ.inv_mem (hu i z)) hγ, ?_, ?_⟩
      · simpa only [mul_assoc, mul_inv_cancel_left] using hg
      · intro j hj
        by_cases hjk : j.val < k
        · rw [hearlier x i z j hjk]
          exact hcoord j hjk
        · have hji : j = i := Fin.ext (by dsimp [i]; omega)
          subst j
          rw [hpivot]
          exact add_neg_cancel (c x i)
  obtain ⟨x, γ, hγ, hg, hcoord⟩ := hstep d le_rfl
  exact ⟨x, γ, hγ, hg, fun i => hcoord i i.isLt⟩

 theorem triangularZeroCoordinates_ordered_reduction {ι : Type*} [Fintype ι] [LinearOrder ι]
    (Γ : Subgroup G) (c : G → ι → A) (u : ι → A → G)
    (hu : ∀ i z, u i z ∈ Γ)
    (hearlier : ∀ g i z j, j < i → c (g * u i z) j = c g j)
    (hpivot : ∀ g i z, c (g * u i z) i = c g i + z)
    (g : G) : ∃ x γ, γ ∈ Γ ∧ g = x * γ ∧ ∀ i, c x i = 0 := by
  let e := Fintype.orderIsoFinOfCardEq ι rfl
  obtain ⟨x, γ, hγ, hg, hc⟩ := triangularZeroCoordinates_fin_reduction Γ
    (fun g i => c g (e i)) (fun i z => u (e i) z)
    (fun i z => hu (e i) z)
    (fun g i z j hj => hearlier g (e i) z (e j) (e.lt_iff_lt.mpr hj))
    (fun g i z => hpivot g (e i) z) g
  exact ⟨x, γ, hγ, hg, fun i => by simpa using hc (e.symm i)⟩

 theorem triangularZeroCoordinates_subgroup_eq_top {ι : Type*} [Fintype ι] [LinearOrder ι]
    (Γ : Subgroup G) (c : G → ι → A) (u : ι → A → G)
    (hinj : Function.Injective c) (hone : ∀ i, c 1 i = 0)
    (hu : ∀ i z, u i z ∈ Γ)
    (hearlier : ∀ g i z j, j < i → c (g * u i z) j = c g j)
    (hpivot : ∀ g i z, c (g * u i z) i = c g i + z) : Γ = ⊤ := by
  apply eq_top_iff.mpr
  intro g _
  obtain ⟨x, γ, hγ, hg, hc⟩ := triangularZeroCoordinates_ordered_reduction Γ c u hu hearlier hpivot g
  have hx : x = 1 := hinj (funext fun i => (hc i).trans (hone i).symm)
  rw [hx, one_mul] at hg
  exact hg.symm ▸ hγ

end Hindman168
