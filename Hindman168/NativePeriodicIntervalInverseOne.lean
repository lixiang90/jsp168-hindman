import Hindman168.IntegerIntervalGowersDimensionOne
import Hindman168.NativePeriodicIntervalInverseThreshold
import Hindman168.NativeNilmanifoldTrivial

/-! An actual unconditional instance of the native interval inverse statement.

For U¹, the norm is the absolute mean and the single zero-dimensional
nilmanifold with constant observable one supplies the correlation. This is
only the elementary first-order case; it does not assert the higher-order
GTZ theorem used in the main proof. -/

namespace Hindman168
open scoped Classical Topology
universe u

/-- Genuine U¹ inverse with one fixed trivial native nilmanifold, Lipschitz
constant zero, and correlation threshold δ/4. The all-length mean identity
also covers K=0, without cancelling any zero interval denominator. -/
theorem native_periodic_interval_inverse_one (s : ℕ) :
    HasNativePeriodicIntervalInverse.{u} s 1 := by
  intro δ hδ
  let D : NativeNilmanifoldData.{u} s := trivialNativeNilmanifold s
  refine ⟨1, by decide, (fun _ => D), (fun _ => 0), δ / 4, by positivity, ?_⟩
  intro q _ K v _hv hn
  refine ⟨0, ?_⟩
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) :=
    D.metric.toUniformSpace.toTopologicalSpace
  refine ⟨ContinuousMap.const _ (1 : ℂ), (1 : D.G), (1 : D.G), ?_, ?_, ?_⟩
  · intro z
    simp
  · exact LipschitzWith.const (1 : ℂ)
  · simpa only [ContinuousMap.const_apply, mul_one,
      integerIntervalPeriodicGowersValue_one_eq_complexMean_norm] using hn

end Hindman168
