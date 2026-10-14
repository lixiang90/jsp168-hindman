import Hindman168.UniformIntervalTranslation
import Hindman168.SamplingAsymptotics
import Hindman168.FiniteTensor

/-!
# Uniform auxiliary interval errors at every inverse-power scale

The interval length, rather than its location, must dominate each fixed
power of the auxiliary budget. Moduli and signed translations may vary
within their caps. Eventual positivity of the length is derived from
growth and is not assumed separately.
-/

namespace Hindman168

open Filter Asymptotics
open scoped Topology

noncomputable def uniformIntervalError (T B : ℕ) : ℝ := 2 * (B : ℝ) / T

theorem uniformIntervalError_nonneg (T B : ℕ) : 0 ≤ uniformIntervalError T B :=
  div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg B)) (Nat.cast_nonneg T)

theorem uniform_interval_eventually_positive {α : Type*} {l : Filter α}
    {T K H V : α → ℕ}
    (hD : PowerDominates l (fun w => (T w : ℝ))
      (fun w => (samplingSize 0 (K w) (H w) (V w) : ℝ))) :
    ∀ᶠ w in l, 0 < T w :=
  (sampling_eventually_geometry hD).mono (fun _ hw => by omega)

theorem uniform_interval_cap_rapid {α : Type*} {l : Filter α}
    {T K H V B : α → ℕ}
    (hD : PowerDominates l (fun w => (T w : ℝ))
      (fun w => (samplingSize 0 (K w) (H w) (V w) : ℝ)))
    (hV : ∀ᶠ w in l, 1 ≤ V w)
    (hB : ∀ᶠ w in l, B w ≤ samplingSize 0 (K w) (H w) (V w)) :
    RapidlySmall l (fun w => (V w : ℝ)) (fun w => uniformIntervalError (T w) (B w)) := by
  have hT := uniform_interval_eventually_positive hD
  apply rapid_of_polynomial_majorant hD
    (hT.mono (fun _ hw => by exact_mod_cast hw))
    (hV.mono (fun w hw => ⟨by exact_mod_cast hw,
      by exact_mod_cast (samplingSize_bounds 0 (K w) (H w) (V w)).2.2.2.2⟩))
    1 (by norm_num : (0 : ℝ) < 2)
  filter_upwards [hT, hB] with w hTw hBw
  rw [abs_of_nonneg (uniformIntervalError_nonneg _ _), uniformIntervalError, pow_one]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hBw) (by norm_num)) (Nat.cast_nonneg _)

theorem uniform_interval_residue_cap_rapid {α : Type*} {l : Filter α}
    {T K H V : α → ℕ}
    (hD : PowerDominates l (fun w => (T w : ℝ))
      (fun w => (samplingSize 0 (K w) (H w) (V w) : ℝ)))
    (hV : ∀ᶠ w in l, 1 ≤ V w) :
    RapidlySmall l (fun w => (V w : ℝ)) (fun w => uniformIntervalError (T w) (K w)) :=
  uniform_interval_cap_rapid hD hV (Eventually.of_forall (fun w =>
    (samplingSize_bounds 0 (K w) (H w) (V w)).2.2.1))

theorem uniform_interval_translation_cap_rapid {α : Type*} {l : Filter α}
    {T K H V : α → ℕ}
    (hD : PowerDominates l (fun w => (T w : ℝ))
      (fun w => (samplingSize 0 (K w) (H w) (V w) : ℝ)))
    (hV : ∀ᶠ w in l, 1 ≤ V w) :
    RapidlySmall l (fun w => (V w : ℝ)) (fun w => uniformIntervalError (T w) (H w)) :=
  uniform_interval_cap_rapid hD hV (Eventually.of_forall (fun w =>
    (samplingSize_bounds 0 (K w) (H w) (V w)).2.2.2.1))

theorem uniform_interval_residue_rapid {α : Type*} {l : Filter α}
    {A : α → ℤ} {T K H V k : α → ℕ} (hk : ∀ w, 0 < k w)
    (hD : PowerDominates l (fun w => (T w : ℝ))
      (fun w => (samplingSize 0 (K w) (H w) (V w) : ℝ)))
    (hV : ∀ᶠ w in l, 1 ≤ V w) (hK : ∀ᶠ w in l, k w ≤ K w) :
    RapidlySmall l (fun w => (V w : ℝ)) (fun w =>
      FiniteMass.distance (intervalResidueMass (A w) (T w) (k w) (hk w)) (uniformResidueMass (k w))) := by
  apply (uniform_interval_residue_cap_rapid hD hV).of_abs_le
  filter_upwards [uniform_interval_eventually_positive hD, hK] with w hTw hKw
  rw [abs_of_nonneg (FiniteMass.distance_nonneg _ _),
    abs_of_nonneg (uniformIntervalError_nonneg _ _), uniformIntervalError]
  exact (uniform_interval_residue_paper_bound (A w) hTw (hk w)).trans
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hKw) (by norm_num)) (Nat.cast_nonneg _))

theorem uniform_interval_translation_rapid {α : Type*} {l : Filter α}
    {A u : α → ℤ} {T K H V : α → ℕ}
    (hD : PowerDominates l (fun w => (T w : ℝ))
      (fun w => (samplingSize 0 (K w) (H w) (V w) : ℝ)))
    (hV : ∀ᶠ w in l, 1 ≤ V w) (hu : ∀ᶠ w in l, (u w).natAbs ≤ H w) :
    RapidlySmall l (fun w => (V w : ℝ)) (fun w =>
      FiniteMass.distance ((uniformIntervalMass (A w) (T w)).mapDomain (fun z => z + u w))
        (uniformIntervalMass (A w) (T w))) := by
  apply (uniform_interval_translation_cap_rapid hD hV).of_abs_le
  filter_upwards [uniform_interval_eventually_positive hD, hu] with w hTw huw
  rw [abs_of_nonneg (FiniteMass.distance_nonneg _ _),
    abs_of_nonneg (uniformIntervalError_nonneg _ _), uniformIntervalError]
  have hh : |(u w : ℝ)| ≤ H w := by
    have he : ((u w).natAbs : ℝ) = |(u w : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
    rw [← he]
    exact_mod_cast huw
  exact (uniform_interval_translation_linear (A w) hTw (u w)).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hh (by norm_num)) (Nat.cast_nonneg _))

end Hindman168
