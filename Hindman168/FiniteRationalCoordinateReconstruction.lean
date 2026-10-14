import Hindman168.RationalPolynomialIntegerDilation
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.StdBasis

namespace Hindman168
open scoped BigOperators Classical

theorem finite_rational_coordinate_reconstruction {ι X : Type*} [Fintype ι]
    (T : Finset X) (v : X → (ι → ℚ))
    (hspan : Submodule.span ℚ (v '' (T : Set X)) = ⊤) :
    ∃ D : ℕ, 0 < D ∧ ∃ m : ι → ↥T → ℤ, ∀ i j,
      ∑ t : ↥T, (m i t : ℚ)*v t.val j = if j=i then (D : ℚ) else 0 := by
  have hex : ∀ i : ι, ∃ c : ↥T → ℚ, ∑ t : ↥T, c t • v t.val = Pi.single i 1 := by
    intro i
    apply (Submodule.mem_span_image_finset_iff_exists_fun ℚ).mp
    rw [hspan]
    trivial
  choose c hc using hex
  obtain ⟨D, hD, hclear⟩ := rational_finite_family_integer_multiplier
    (Finset.univ : Finset (ι × ↥T)) (fun z => c z.1 z.2)
  have hint : ∀ i t, ∃ m : ℤ, (D : ℚ)*c i t = (m : ℚ) := by
    intro i t
    obtain ⟨m, hm⟩ := hclear (i,t) (Finset.mem_univ _)
    exact ⟨m, hm.symm⟩
  choose m hm using hint
  refine ⟨D, hD, m, ?_⟩
  intro i j
  have he : (∑ t : ↥T, (m i t : ℚ) • v t.val) = (D : ℚ) • Pi.single i 1 := by
    simp_rw [← hm, mul_smul]
    rw [← Finset.smul_sum, hc]
  have h := congrFun he j
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
    mul_ite, mul_one, mul_zero, eq_comm] using h

theorem finite_rational_reconstruction_uniform_bound {ι X : Type*} [Fintype ι]
    (A : Finset X) (v : X → (ι → ℚ)) :
    ∃ B : ℕ, 0 < B ∧ ∀ T : Finset X, T ⊆ A →
      Submodule.span ℚ (v '' (T : Set X)) = ⊤ →
      ∃ D : ℕ, 0 < D ∧ D ≤ B ∧ ∃ m : ι → ↥T → ℤ,
        (∀ i, ∑ t : ↥T, (m i t).natAbs ≤ B) ∧
        ∀ i j, ∑ t : ↥T, (m i t : ℚ)*v t.val j = if j=i then (D : ℚ) else 0 := by
  let F := A.powerset.filter (fun T : Finset X => Submodule.span ℚ (v '' (T : Set X)) = ⊤)
  have hex : ∀ t : ↥F, ∃ D : ℕ, 0 < D ∧ ∃ m : ι → ↥t.val → ℤ,
      ∀ i j, ∑ x : ↥t.val, (m i x : ℚ)*v x.val j = if j=i then (D : ℚ) else 0 := by
    intro t
    exact finite_rational_coordinate_reconstruction t.val v (Finset.mem_filter.mp t.property).2
  choose D hD m hm using hex
  let b := fun t : ↥F => D t + ∑ i : ι, ∑ x : ↥t.val, (m t i x).natAbs
  let B := 1 + ∑ t : ↥F, b t
  refine ⟨B, by dsimp only [B]; omega, ?_⟩
  intro T hT hspan
  let t : ↥F := ⟨T, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hT, hspan⟩⟩
  have hbt : b t ≤ B := (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)).trans
    (by dsimp only [B]; omega)
  refine ⟨D t, hD t, ?_, m t, ?_, hm t⟩
  · have hDb : D t ≤ b t := by dsimp only [b]; omega
    exact hDb.trans hbt
  · intro i
    change (∑ x : ↥t.val, (m t i x).natAbs) ≤ B
    have hi := Finset.single_le_sum (fun k _ => Nat.zero_le (∑ x : ↥t.val, (m t k x).natAbs))
      (Finset.mem_univ i)
    have hib : (∑ k : ι, ∑ x : ↥t.val, (m t k x).natAbs) ≤ b t := Nat.le_add_left _ _
    exact hi.trans (hib.trans hbt)

end Hindman168
