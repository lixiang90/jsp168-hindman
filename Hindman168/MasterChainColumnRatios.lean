import Hindman168.MasterColumnCoefficients

/-!
The actual coefficients of an ordered master chain have integer ratios.
Every earlier-to-later ratio is a multiple of the actual primorial.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical

theorem naturalRatio_W_divisible {ci cj W t : ℕ} (hcj : 0 < cj)
    (hr : (ci : ℚ) / cj = (W : ℚ) * t) : cj ∣ ci ∧ W ∣ ci / cj := by
  have hcj0 : (cj : ℚ) ≠ 0 := by exact_mod_cast hcj.ne'
  have heq := (div_eq_iff hcj0).mp hr
  have heQ : (ci : ℚ) = (cj : ℚ) * ((W : ℚ) * t) := by
    calc
      _ = (W : ℚ) * t * cj := heq
      _ = _ := by ring
  have he : ci = cj * (W * t) := by exact_mod_cast heQ
  refine ⟨⟨W * t, he⟩, ?_⟩
  rw [he, Nat.mul_div_cancel_left _ hcj]
  exact dvd_mul_right _ _

theorem MasterParameterConditions.chain_column_ratios {n N b : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (a : Fin b → ℚ)
    (ha : ∀ k, a k ∈ A) (C : ℕ → Chain b)
    (hC : ∀ w k, (C w).block k ⊆ Finset.range N) :
    ∀ᶠ w in atTop, ∀ i j : Fin b, i < j →
      masterColumnCoefficient N a (fun w => (C w).block) w j ∣
        masterColumnCoefficient N a (fun w => (C w).block) w i ∧
      primorial w ∣ masterColumnCoefficient N a (fun w => (C w).block) w i /
        masterColumnCoefficient N a (fun w => (C w).block) w j := by
  have hcoeff := hF.column_coefficients a ha (fun w => (C w).block) hC
    (fun w k => (C w).block_nonempty k)
  filter_upwards [hcoeff, hF.chain_ratios] with w hw hratio
  intro i j hij
  obtain ⟨t, ht⟩ := hratio (a i) (ha i) (a j) (ha j) b (C w) (hC w) i j hij
  rw [(hw i).2.1, (hw j).2.1] at ht
  exact naturalRatio_W_divisible (hw j).1 ht

end Hindman168
