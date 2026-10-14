import Hindman168.PolynomialRowNormalization
import Mathlib.Algebra.Order.Floor.Ring

/-! Actual positive natural master coefficients, defined by rational floor. -/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical

noncomputable def masterColumnCoefficient {b : ℕ} (N : ℕ)
    (a : Fin b → ℚ) (block : ℕ → Fin b → Finset ℕ) (w : ℕ) (k : Fin b) : ℕ :=
  ⌊(masterScale (primorial w) w N (block w k) : ℚ) * a k⌋₊

theorem MasterParameterConditions.column_coefficients {n N b : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (a : Fin b → ℚ)
    (ha : ∀ k, a k ∈ A) (block : ℕ → Fin b → Finset ℕ)
    (hblock : ∀ w k, block w k ⊆ Finset.range N)
    (hnonempty : ∀ w k, (block w k).Nonempty) :
    ∀ᶠ w in atTop, ∀ k, 0 < masterColumnCoefficient N a block w k ∧
      (masterScale (primorial w) w N (block w k) : ℚ) * a k =
        (masterColumnCoefficient N a block w k : ℚ) ∧
      (primorial w) ^ (F.exponent w + 1) * masterColumnCoefficient N a block w k ∣
        (F.modulus w : ℕ) := by
  filter_upwards [hF.coefficients] with w hw
  intro k
  obtain ⟨c, hc, he, habs⟩ := hw (a k) (ha k) (block w k) (hblock w k) (hnonempty w k)
  have hvalue : masterColumnCoefficient N a block w k = c := by
    simp only [masterColumnCoefficient, he, Nat.floor_natCast]
  simpa only [hvalue] using (show 0 < c ∧
    (masterScale (primorial w) w N (block w k) : ℚ) * a k = (c : ℚ) ∧
    (primorial w) ^ (F.exponent w + 1) * c ∣ (F.modulus w : ℕ) from ⟨hc, he, habs⟩)

theorem MasterParameterConditions.column_coefficients_bounds {n N b : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (a : Fin b → ℚ)
    (ha : ∀ k, a k ∈ A) (block : ℕ → Fin b → Finset ℕ)
    (hblock : ∀ w k, block w k ⊆ Finset.range N)
    (hnonempty : ∀ w k, (block w k).Nonempty) :
    ∀ᶠ w in atTop, ∀ k, 0 < masterColumnCoefficient N a block w k ∧
      masterColumnCoefficient N a block w k ∣ (F.modulus w : ℕ) ∧
      masterColumnCoefficient N a block w k ≤ (F.modulus w : ℕ) := by
  filter_upwards [hF.column_coefficients a ha block hblock hnonempty] with w hw
  intro k
  have hd := (dvd_mul_left (masterColumnCoefficient N a block w k)
    ((primorial w) ^ (F.exponent w + 1))).trans (hw k).2.2
  exact ⟨(hw k).1, hd, Nat.le_of_dvd (F.modulus w).pos hd⟩

end Hindman168
