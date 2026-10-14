import Hindman168.CompactQuotientRepresentatives
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Finset.Sort
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-! Integer right translations reduce triangular coordinates without any
commutativity assumption on the group. The hypotheses state coordinate laws,
not cocompactness or the existence of bounded representatives. -/

namespace Hindman168
open Set Topology

variable {G : Type*} [Group G]

 theorem triangularCoordinates_fin_reduction {d : ℕ} (Γ : Subgroup G)
    (c : G → Fin d → ℝ) (u : Fin d → ℤ → G)
    (hu : ∀ i z, u i z ∈ Γ)
    (hearlier : ∀ g i z j, j < i → c (g * u i z) j = c g j)
    (hpivot : ∀ g i z, c (g * u i z) i = c g i + (z : ℝ))
    (g : G) :
    ∃ x γ, γ ∈ Γ ∧ g = x * γ ∧ ∀ i, c x i ∈ Ico 0 1 := by
  have hstep : ∀ k ≤ d, ∃ x γ, γ ∈ Γ ∧ g = x * γ ∧
      ∀ i : Fin d, i.val < k → c x i ∈ Ico 0 1 := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨g, 1, Γ.one_mem, by simp, by intro i hi; omega⟩
    | succ k ih =>
      intro hk
      obtain ⟨x, γ, hγ, hg, hcoord⟩ := ih (by omega)
      let i : Fin d := ⟨k, by omega⟩
      let z : ℤ := -⌊c x i⌋
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
          have hlo := Int.floor_le (c x i)
          have hhi := Int.lt_floor_add_one (c x i)
          change 0 ≤ c x i + ((-⌊c x i⌋ : ℤ) : ℝ) ∧
            c x i + ((-⌊c x i⌋ : ℤ) : ℝ) < 1
          push_cast
          constructor <;> linarith
  obtain ⟨x, γ, hγ, hg, hcoord⟩ := hstep d le_rfl
  exact ⟨x, γ, hγ, hg, fun i => hcoord i i.isLt⟩

 theorem triangularCoordinates_ordered_reduction {ι : Type*} [Fintype ι]
    [LinearOrder ι] (Γ : Subgroup G) (c : G → ι → ℝ) (u : ι → ℤ → G)
    (hu : ∀ i z, u i z ∈ Γ)
    (hearlier : ∀ g i z j, j < i → c (g * u i z) j = c g j)
    (hpivot : ∀ g i z, c (g * u i z) i = c g i + (z : ℝ))
    (g : G) :
    ∃ x γ, γ ∈ Γ ∧ g = x * γ ∧ ∀ i, c x i ∈ Ico 0 1 := by
  let e := Fintype.orderIsoFinOfCardEq ι rfl
  obtain ⟨x, γ, hγ, hg, hc⟩ := triangularCoordinates_fin_reduction Γ
    (fun g i => c g (e i)) (fun i z => u (e i) z)
    (fun i z => hu (e i) z)
    (fun g i z j hj => hearlier g (e i) z (e j) (e.lt_iff_lt.mpr hj))
    (fun g i z => hpivot g (e i) z) g
  exact ⟨x, γ, hγ, hg, fun i => by simpa using hc (e.symm i)⟩

variable [TopologicalSpace G]

 theorem triangularCoordinates_compact_quotient {ι : Type*} [Fintype ι]
    [LinearOrder ι] (Γ : Subgroup G) (c : G ≃ₜ (ι → ℝ)) (u : ι → ℤ → G)
    (hu : ∀ i z, u i z ∈ Γ)
    (hearlier : ∀ g i z j, j < i → c (g * u i z) j = c g j)
    (hpivot : ∀ g i z, c (g * u i z) i = c g i + (z : ℝ)) :
    CompactSpace (G ⧸ Γ) := by
  let C : Set (ι → ℝ) := pi univ (fun _ => Icc 0 1)
  have hC : IsCompact C := isCompact_univ_pi fun _ => isCompact_Icc
  apply compactSpace_of_lattice_representatives Γ (c.symm '' C)
    (hC.image c.symm.continuous)
  intro g
  obtain ⟨x, γ, hγ, hg, hc⟩ := triangularCoordinates_ordered_reduction
    Γ c u hu hearlier hpivot g
  refine ⟨x, ?_, γ, hγ, hg⟩
  refine ⟨c x, ?_, c.symm_apply_apply x⟩
  exact mem_pi.mpr fun i _ => ⟨(hc i).1, (hc i).2.le⟩

end Hindman168
