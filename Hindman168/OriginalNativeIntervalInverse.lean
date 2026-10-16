import Hindman168.OriginalNativeIntervalInverseMenu
import Hindman168.OriginalInverseNormalizationEmpty
import Hindman168.OriginalInverseNormalizationTransport
import OAI.Combinatorics.Progressions.Estimates.AxisCompression

/-!
UNCOMPILED: canonical library adapter prepared for Lake DAG verification.

The finite-menu/linear-orbit bridge is supplied by
`Hindman168.OriginalNativeIntervalInverseMenu`; the inverse endpoint is
OpenAI's `exists_native_inverse_on_cyclic_encoding`, fixed at commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

The complete source closure has been restored, but this adapter and its
proof chain have not yet been compiled. This file is not imported by the
old canonical aggregate. The preserved work-in-progress snapshot declares
these same theorem names: never import both versions into one environment.
-/

namespace Hindman168
open OAI.Erdos3 OriginalBoundedNativeModels
open scoped BigOperators Classical NNReal Topology

attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

/-- Exact interval specialization of the upstream cyclic-encoding inverse.
The doubled interval modulus gives density exactly one half, and the existing
supported-cube equivalence preserves the interval norm without a degree shift.
The zero-length case is excluded by its positive norm hypothesis. -/
theorem original_interval_niltest_inverse_from_openai (s : ℕ) (hs : 1 ≤ s) :
    HasUniformOriginalIntervalNiltestInverse s (s + 1) := by
  obtain ⟨C, _hC, hinverse⟩ := exists_native_inverse_on_cyclic_encoding s hs
  intro δ hδ
  refine ⟨originalInverseComplexityBudget δ C,
    originalInverseComplexityBudget_nonneg δ C,
    originalInverseCorrelationBudget δ C,
    originalInverseCorrelationBudget_pos δ C, ?_⟩
  intro q _ K v hv hnorm
  have hlength : 0 < K * q := originalInverse_interval_length_positive v hδ hnorm
  letI : NeZero (2 * (K * q)) := ⟨by omega⟩
  let f : (Unit → ℤ) → ℂ := fun x => (v (x () : ZMod q) : ℂ)
  have hf : ∀ x ∈ originalInverseInterval (K * q), ‖f x‖ ≤ 1 := by
    intro x _hx
    simpa only [f, Complex.norm_real, Real.norm_eq_abs] using hv (x () : ZMod q)
  have hGowers : Real.exp (-originalInverseLogParameter δ) ≤
      finiteSupportGowersNorm (s + 1) (originalInverseInterval (K * q)) f := by
    rw [originalInverseInterval_gowersNorm]
    exact (originalInverseLogParameter_exp_le hδ).trans hnorm
  obtain ⟨V, hVnorm⟩ := hinverse
    (N := 2 * (K * q))
    (originalInverseInterval (K * q)) (originalInverseInterval_nonempty hlength)
    originalInverseIntervalEval.toAddMonoidHom
    (originalInverseInterval_encoding_reflectsPairSums hlength)
    (fun x hx => originalInverseInterval_encoding_representatives x hx)
    (p := originalInverseLogParameter δ) (q := 1)
    (originalInverseLogParameter_ge_two δ) (by norm_num)
    (originalInverseInterval_encoding_density hlength) f hf hGowers
  let A : RationalGeometry s := { L := V.L, dim := V.dim, model := V.model }
  refine ⟨A, V.test, V.complexity, hVnorm, ?_⟩
  have hcorr := V.correlation
  change originalInverseCorrelationBudget δ C ≤
    ‖𝔼 x ∈ originalInverseInterval (K * q),
      (v (x () : ZMod q) : ℂ) * star (V.test.eval x)‖ at hcorr
  rw [originalInverseInterval_periodic_mean] at hcorr
  simpa only [originalInverseIntervalPoint] using hcorr

/-- The genuine higher-order native interval inverse, at precisely step `s`
for Gowers order `s+1`, obtained from the fixed upstream inverse theorem. -/
theorem native_periodic_interval_inverse_from_openai (s : ℕ) (hs : 1 ≤ s) :
    HasNativePeriodicIntervalInverse.{0} s (s + 1) :=
  native_periodic_interval_inverse_of_original_niltests s (s + 1) hs
    (original_interval_niltest_inverse_from_openai s hs)

/-- The complete family expected by `strongConjecture_of_native_inverse`.
Universe zero already suffices to apply that existing theorem. -/
theorem native_periodic_interval_inverse_family_from_openai (t : ℕ) (ht : 2 ≤ t) :
    HasNativePeriodicIntervalInverse.{0} (t - 1) t := by
  have hdegree : t - 1 + 1 = t := by omega
  simpa only [hdegree] using
    native_periodic_interval_inverse_from_openai (t - 1) (by omega)

end Hindman168
