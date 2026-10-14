import Hindman168.NativePeriodicIntervalInverseOne
import Hindman168.MaskGeneratedOriginalTemplates

namespace Hindman168
open scoped Manifold ContDiff
universe u

/-- Raising only the nilpotency upper bound preserves the original group,
lattice, metric and every actual observation definitionally. -/
noncomputable def finalNativeNilmanifoldRaise {s t : ℕ}
    (D : NativeNilmanifoldData.{u} s) (hst : s ≤ t) : NativeNilmanifoldData.{u} t :=
  { D with step_le := D.step_le.trans hst }

theorem native_periodic_interval_inverse_step_mono {s t d : ℕ} (hst : s ≤ t)
    (hinv : HasNativePeriodicIntervalInverse.{u} s d) :
    HasNativePeriodicIntervalInverse.{u} t d := by
  intro δ hδ
  obtain ⟨L,hL,D,Lip,γ,hγ,h⟩ := hinv δ hδ
  refine ⟨L,hL,(fun i => finalNativeNilmanifoldRaise (D i) hst),Lip,γ,hγ,?_⟩
  intro q _ K v hv hg
  exact h q K v hv hg

/-- One common model step suffices for every finite row-order required by
prediction, from the original degree-minus-one inverse statements. -/
theorem native_inverse_mask_family_of_degree_minus_one
    (hinverse : ∀ t : ℕ, 2 ≤ t → HasNativePeriodicIntervalInverse.{u} (t-1) t)
    (m : ℕ) : ∃ s : ℕ, ∀ d : ℕ, d ≤ maskRowCountBound m →
      HasNativePeriodicIntervalInverse.{u} s (2^d+2^d-1) := by
  let s := 2^(maskRowCountBound m)+2^(maskRowCountBound m)-1
  refine ⟨s,?_⟩
  intro d hd
  by_cases hz : d=0
  · subst d
    simpa using native_periodic_interval_inverse_one (s := s)
  · have hp : 2 ≤ 2^d := by
      calc
        2 = (2:ℕ)^1 := by norm_num
        _ ≤ 2^d := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hle : 2^d ≤ 2^(maskRowCountBound m) := Nat.pow_le_pow_right (by norm_num) hd
    apply native_periodic_interval_inverse_step_mono (s := (2^d+2^d-1)-1)
      (t := s) (by dsimp [s]; omega)
    exact hinverse _ (by omega)
end Hindman168
