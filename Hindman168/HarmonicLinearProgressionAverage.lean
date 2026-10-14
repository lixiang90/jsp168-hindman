import Hindman168.AffineProgressionAverage
import Hindman168.FinitePivotCoordinates

/-! Average a progression restriction through one harmonic coordinate of an
actual finite product law. The offset may depend arbitrarily on the other
coordinates; its size is irrelevant to the residue permutation estimate. -/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

theorem integerLinearSum_insertPivot {ι : Type*} [Fintype ι]
    (c : ι → ℤ) (j : ι) (rest : {i : ι // i ≠ j} → ℤ) (z h : ℤ) :
    (∑ i, c i * insertPivotCoordinate j rest z i) + h =
      c j * z + ((∑ i : {i : ι // i ≠ j}, c i.val * rest i) + h) := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ j, insertPivotCoordinate_self]
  have he : (∑ i : {i : ι // i ≠ j}, c i.val * insertPivotCoordinate j rest z i.val) =
      ∑ i : {i : ι // i ≠ j}, c i.val * rest i := by
    apply Fintype.sum_congr
    intro i
    rw [congrFun (insertPivotCoordinate_rest j rest z) i]
  rw [he, add_assoc]

theorem harmonic_linear_progression_average_error {ι : Type*} [Fintype ι]
    {X W k : ℕ} [NeZero k] (ν : ι → Mass ℤ)
    (hν : ∀ i z, 0 ≤ ν i z) (htν : ∀ i, total (ν i) = 1)
    (j : ι) (hj : ν j = integerMass X W) (c : ι → ℤ) (h : ℤ)
    (μ : Mass ℤ) (hμ : ∀ y, 0 ≤ μ y) (htμ : total μ = 1)
    (hX : 2 ≤ X) (hW : 0 < W) (hco : W.Coprime k)
    (hlog : (W : ℝ) / X < Real.log X) (hc : IsUnit (c j : ZMod k))
    (f : ℤ → ℝ) (B : ℝ) (hB : 0 ≤ B) (hf : ∀ y, |f y| ≤ B) :
    |expectation (piMass ν) (fun z =>
        expectation (residueClassMass μ k (((∑ i, c i * z i) + h : ℤ) : ZMod k)) f) -
      expectation μ f| ≤ (k : ℝ) * B * residueError X W k := by
  rw [expectation_piMass_pivot ν j]
  simp_rw [integerLinearSum_insertPivot]
  rw [hj]
  let ρ := piMass (fun i : {i : ι // i ≠ j} => ν i.val)
  have htρ : total ρ = 1 := piMass_total_one _ (fun i => htν i.val)
  calc
    _ = |expectation ρ (fun rest => expectation (integerMass X W) (fun z =>
        expectation (residueClassMass μ k
          ((c j * z + ((∑ i : {i : ι // i ≠ j}, c i.val * rest i) + h) : ℤ) : ZMod k)) f)) -
        expectation ρ (fun _ => expectation μ f)| := by
      rw [expectation_const, htρ, one_mul]
    _ ≤ total ρ * ((k : ℝ) * B * residueError X W k) := by
      apply expectation_difference_support_bound ρ (piMass_nonneg _ (fun i => hν i.val))
      intro rest _
      exact harmonic_progression_average_error μ hμ htμ (c j)
        ((∑ i : {i : ι // i ≠ j}, c i.val * rest i) + h) hX hW hco hlog hc f B hB hf
    _ = _ := by rw [htρ, one_mul]

end Hindman168
