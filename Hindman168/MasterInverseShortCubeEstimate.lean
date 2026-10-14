import Hindman168.MasterUniformShortCubeThreshold
import Hindman168.NativePeriodicIntervalInverseThreshold

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Topology Classical
universe u

/-- Given the displayed interval inverse existence input, the original
short-cube statistic is small when the actual fine projection is small.
Both the quotient J and projection threshold are chosen before N, the
polynomial data, gaps, original laws and unit Hilbert family. -/
theorem master_inverse_shortCube_uniform_threshold (s d : ℕ)
    (hinverse : HasNativePeriodicIntervalInverse.{u} s (2 ^ d + 2 ^ d - 1))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ J : ℕ, 0 < J ∧ ∃ κ : ℝ, 0 < κ ∧
      ∀ {n N : ℕ} (D : Finset (MvPolynomial (Fin n) ℤ)) (hD : ∀ f ∈ D, f ≠ 0)
        (pol : MvPolynomial (Fin n) ℤ) (_hpol : pol ∈ D)
        (T : Finset (MvPolynomial (Fin n) ℤ)) (_hT : ∀ f ∈ T, f ≠ 0) (_hpolT : pol ∈ T)
        (gap pivot : ℕ → Fin N) (_horder : ∀ᶠ w in atTop, (gap w).val ≤ (pivot w).val),
      let F := constructedMasterFamily N D hD
      ∀ (U : Ultrafilter ℕ) (_hU : (U : Filter ℕ) ≤ atTop)
        (h : boundedHilbertFamilies (fun w =>
          FiniteMassL2 (integerMass (F.cutoff w (pivot w).val) (primorial w))))
        (_hf : ∀ w y, |h.val w y| ≤ 1),
      ‖(nativeNilHilbertSubspace.{u} s F
        (fun w => integerMass (F.cutoff w (pivot w).val) (primorial w)) U gap).starProjection
          (hilbertFamilyToCompletion _ U h)‖ < κ →
      ∀ᶠ w in (U : Filter ℕ),
        let μ := conditionMass (dyadicPoolTupleMass
          (fun _ : Fin n => F.pool w (gap w).val)) (primeSampleGood T)
        expectation μ (fun x => |integerPredictionShortCubeStatistic w (F.modulus w : ℕ)
          (F.gap w (gap w).val) (F.cutoff w (pivot w).val) d J pol (fun y => h.val w y) x|) < ε := by
  obtain ⟨J, hJ, θ, hθ, hshort⟩ := master_shortCube_uniform_global_threshold d ε hε
  have hk : (0 : ℕ) < 2 ^ d := by positivity
  have ht : (0 : ℕ) < 2 ^ d + 2 ^ d - 1 := by omega
  obtain ⟨κ, hκ, hproject⟩ := native_interval_inverse_uniform_projection_threshold
    s (2 ^ d + 2 ^ d - 1) ht hinverse θ hθ
  refine ⟨J, hJ, κ, hκ, ?_⟩
  intro n N D hD pol hpol T hT hpolT gap pivot horder F U hU h hf hp
  let hF := constructedMasterFamily_conditions N ∅ (by simp) D hD
  have hnorm := hproject hF U hU gap pivot horder h hf hp
  have hstat := hshort D hD pol hpol T hT hpolT gap pivot horder
  filter_upwards [hU hstat, hnorm] with w hw hn
  letI : NeZero (F.gap w (gap w).val / (F.modulus w : ℕ)) :=
    ⟨Nat.ne_of_gt (hF.common_cyclic_order_positive w (gap w).val)⟩
  exact hw (fun y => h.val w y) (hf w) hn.le

end Hindman168
