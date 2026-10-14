import Hindman168.PeriodicComplexCorrelation
import Hindman168.NativeNilmanifoldData

namespace Hindman168
open scoped Classical
universe u

theorem quotient_linear_orbit_shift {G : Type*} [Group G] (Γ : Subgroup G)
    (g x : G) (n t : ℤ) :
    (g ^ (n + t) * x : G ⧸ Γ) = (g ^ n * (g ^ t * x) : G ⧸ Γ) := by
  rw [zpow_add, mul_assoc]

/-- Selecting a period only translates the original nilsequence basepoint.
The quotient, group element and observable are retained literally. -/
theorem linear_nilsequence_period_correlation_extract {G : Type*} [Group G]
    (Γ : Subgroup G) (K q : ℕ) [NeZero q] (hK : 0 < K)
    (v : ZMod q → ℂ) (obs : (G ⧸ Γ) → ℂ) (g x : G) (δ : ℝ)
    (hδ : δ ≤ ‖finiteComplexMean (fun n : Fin (K * q) =>
      v (n.val : ZMod q) * obs (g ^ (n.val : ℤ) * x))‖) :
    ∃ j : Fin K, δ ≤ ‖finiteComplexMean (fun z : Fin q =>
      v (z.val : ZMod q) * obs (g ^ (z.val : ℤ) * (g ^ ((j.val * q : ℕ) : ℤ) * x)))‖ := by
  obtain ⟨j, hj⟩ := periodic_complex_correlation_extract K q hK v
    (fun n => obs (g ^ (n : ℤ) * x)) δ hδ
  refine ⟨j, ?_⟩
  have he (z : Fin q) :
      (g ^ ((j.val * q + z.val : ℕ) : ℤ) * x : G ⧸ Γ) =
        (g ^ (z.val : ℤ) * (g ^ ((j.val * q : ℕ) : ℤ) * x) : G ⧸ Γ) := by
    rw [Nat.cast_add, add_comm ((j.val * q : ℕ) : ℤ), quotient_linear_orbit_shift]
  simpa only [he] using hj

/-- On the original native nilmanifold, the selected correlator uses the
same manifold, lattice, metric, step bound, translating element and observable.
Any original observable bounds therefore remain unchanged. -/
theorem native_nilsequence_period_correlation_extract {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (K q : ℕ) [NeZero q] (hK : 0 < K)
    (v : ZMod q → ℂ) (obs : C(D.G ⧸ D.Γ, ℂ)) (g x : D.G) (δ : ℝ)
    (hδ : δ ≤ ‖finiteComplexMean (fun n : Fin (K * q) =>
      v (n.val : ZMod q) * obs (g ^ (n.val : ℤ) * x))‖) :
    ∃ (j : Fin K) (x' : D.G), x' = g ^ ((j.val * q : ℕ) : ℤ) * x ∧
      δ ≤ ‖finiteComplexMean (fun z : Fin q => v (z.val : ZMod q) * obs (g ^ (z.val : ℤ) * x'))‖ := by
  obtain ⟨j, hj⟩ := linear_nilsequence_period_correlation_extract D.Γ K q hK v obs g x δ hδ
  exact ⟨j, g ^ ((j.val * q : ℕ) : ℤ) * x, rfl, hj⟩

end Hindman168
