import Hindman168.Ramsey
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

/-! Uniform finite Ramsey selection of jointly binned energies.
The bound is chosen before the energy data, and depends only on the
number of labels, maximum tuple size, desired set size and bin width. -/

namespace Hindman168

theorem energy_bin_distance {δ a b : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (he : ⌊a / δ⌋₊ = ⌊b / δ⌋₊) : |a - b| < δ := by
  have ha0 := Nat.floor_le (div_nonneg ha hδ.le)
  have hb0 := Nat.floor_le (div_nonneg hb hδ.le)
  have ha1 := Nat.lt_floor_add_one (a / δ)
  have hb1 := Nat.lt_floor_add_one (b / δ)
  rw [he] at ha0 ha1
  have hab : a / δ - b / δ < 1 := by linarith
  have hba : b / δ - a / δ < 1 := by linarith
  rw [← sub_div, div_lt_one hδ] at hab hba
  exact abs_lt.mpr ⟨by linarith, hab⟩

theorem finite_energy_homogeneous_bound (ι : Type*) [Fintype ι] (K n : ℕ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ energy : Finset ℕ → ι → ℝ,
      (∀ A a, 0 ≤ energy A a ∧ energy A a ≤ 1) →
      ∃ S : Finset ℕ, S ⊆ Finset.range N ∧ S.card = n ∧
        ∀ A B : Finset ℕ, A ⊆ S → B ⊆ S → A.card = B.card → A.card ≤ K →
          ∀ a, |energy A a - energy B a| < δ := by
  classical
  let q := ⌊(1 : ℝ) / δ⌋₊ + 1
  let Palette := ι → Fin q
  obtain ⟨N, hN⟩ := Ramsey.finite_size_homogeneous_bound (Fintype.card Palette) K n
  refine ⟨N, ?_⟩
  intro energy henergy
  let bins (A : Finset ℕ) : Palette := fun a =>
    ⟨⌊energy A a / δ⌋₊, Nat.lt_succ_of_le (Nat.floor_mono
      (div_le_div_of_nonneg_right (henergy A a).2 hδ.le))⟩
  let color := fun A => (Fintype.equivFin Palette) (bins A)
  obtain ⟨S, hSN, hScard, hS⟩ := hN color
  refine ⟨S, hSN, hScard, ?_⟩
  intro A B hAS hBS hcard hAK a
  obtain ⟨c, hc⟩ := hS A.card hAK
  have he : bins A = bins B := (Fintype.equivFin Palette).injective
    ((hc A hAS rfl).trans (hc B hBS hcard.symm).symm)
  have hb : ⌊energy A a / δ⌋₊ = ⌊energy B a / δ⌋₊ :=
    congrArg Fin.val (congrFun he a)
  exact energy_bin_distance hδ (henergy A a).1 (henergy B a).1 hb

end Hindman168
