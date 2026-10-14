import Hindman168.IntegerResidueLaws
import Hindman168.UniformIntervalAsymptotics
import Hindman168.JointSamplingAsymptotics
import Hindman168.FiniteEventComparison

/-!
# Mixed original base-coordinate laws

The harmonic coordinates and the uniform auxiliary coordinates are sampled
independently. Interval locations are arbitrary. A common modulus cap and
lower bounds on the interval lengths give a uniform joint L1 bound.
-/

namespace Hindman168

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

noncomputable def mixedIntegerBaseMass {d : ℕ} (H : Finset (Fin d))
    (X : Fin d → ℕ) (W : ℕ) (A : Fin d → ℤ) (T : Fin d → ℕ) : Mass (Fin d → ℤ) :=
  piMass (fun j => if j ∈ H then integerMass (X j) W else uniformIntervalMass (A j) (T j))

noncomputable def mixedBaseResidueError {d : ℕ} (H : Finset (Fin d))
    (X : Fin d → ℕ) (W : ℕ) (Tmin : Fin d → ℕ) (B : ℕ) : ℝ :=
  ∑ j, if j ∈ H then residueError (X j) W B else uniformIntervalError (Tmin j) B

theorem mixedIntegerBaseMass_nonneg {d : ℕ} (H : Finset (Fin d))
    (X : Fin d → ℕ) (W : ℕ) (A : Fin d → ℤ) (T : Fin d → ℕ)
    (hH : ∀ j ∈ H, 0 < harmonicNormalizer (X j) W) (y : Fin d → ℤ) :
    0 ≤ mixedIntegerBaseMass H X W A T y := by
  apply piMass_nonneg
  intro j z
  split_ifs with hj
  · exact integerMass_nonneg (hH j hj) z
  · exact uniformIntervalMass_nonneg _ _ z

theorem mixedIntegerBaseMass_total {d : ℕ} (H : Finset (Fin d))
    (X : Fin d → ℕ) (W : ℕ) (A : Fin d → ℤ) (T : Fin d → ℕ)
    (hH : ∀ j ∈ H, 0 < harmonicNormalizer (X j) W)
    (hT : ∀ j, j ∉ H → 0 < T j) : total (mixedIntegerBaseMass H X W A T) = 1 := by
  apply piMass_total_one
  intro j
  split_ifs with hj
  · exact integerMass_total (hH j hj)
  · exact uniformIntervalMass_total _ (hT j hj)

theorem mixedBaseResidueError_nonneg {d : ℕ} (H : Finset (Fin d))
    (X : Fin d → ℕ) (W : ℕ) (Tmin : Fin d → ℕ) (B : ℕ)
    (hlog : ∀ j ∈ H, (W : ℝ) / X j < Real.log (X j : ℝ)) :
    0 ≤ mixedBaseResidueError H X W Tmin B := by
  apply Finset.sum_nonneg
  intro j _
  split_ifs with hj
  · unfold residueError
    exact div_nonneg (by positivity) (mul_nonneg (Nat.cast_nonneg _) (sub_pos.mpr (hlog j hj)).le)
  · exact uniformIntervalError_nonneg _ _

theorem mixed_integer_base_zmod_distance {d : ℕ} (H : Finset (Fin d))
    (X : Fin d → ℕ) (W : ℕ) (A : Fin d → ℤ) (T Tmin : Fin d → ℕ)
    {k B : ℕ} [NeZero k] (hW : 0 < W) (hco : W.Coprime k) (hcap : k ≤ B)
    (hX : ∀ j ∈ H, 2 ≤ X j)
    (hlog : ∀ j ∈ H, (W : ℝ) / X j < Real.log (X j : ℝ))
    (hT : ∀ j, j ∉ H → 0 < Tmin j ∧ Tmin j ≤ T j) :
    distance ((mixedIntegerBaseMass H X W A T).mapDomain
        (fun y : Fin d → ℤ => fun j => (y j : ZMod k)))
      (uniformFintypeMass (Fin d → ZMod k)) ≤ mixedBaseResidueError H X W Tmin B := by
  let μ := fun j => if j ∈ H then integerMass (X j) W else uniformIntervalMass (A j) (T j)
  have hμ (j : Fin d) (z : ℤ) : 0 ≤ μ j z := by
    dsimp [μ]
    split_ifs with hj
    · exact integerMass_nonneg (harmonicNormalizer_pos (hX j hj) hW (hlog j hj)) z
    · exact uniformIntervalMass_nonneg _ _ z
  have htμ (j : Fin d) : total (μ j) = 1 := by
    dsimp [μ]
    split_ifs with hj
    · exact integerMass_total (harmonicNormalizer_pos (hX j hj) hW (hlog j hj))
    · exact uniformIntervalMass_total _ (lt_of_lt_of_le (hT j hj).1 (hT j hj).2)
  have he (j : Fin d) : distance ((μ j).mapDomain (fun z : ℤ => (z : ZMod k)))
      (uniformFintypeMass (ZMod k)) ≤
        if j ∈ H then residueError (X j) W B else uniformIntervalError (Tmin j) B := by
    dsimp [μ]
    split_ifs with hj
    · exact (harmonic_integer_zmod_distance (hX j hj) hW hco (hlog j hj)).trans
        (residueError_mono (hX j hj) hcap (hlog j hj))
    · have hpos : (0 : ℝ) < Tmin j := by exact_mod_cast (hT j hj).1
      have hlen : (Tmin j : ℝ) ≤ T j := by exact_mod_cast (hT j hj).2
      have hkc : (k : ℝ) ≤ B := by exact_mod_cast hcap
      refine (uniform_interval_zmod_distance (A j)
        (lt_of_lt_of_le (hT j hj).1 (hT j hj).2)).trans ?_
      calc
        (k : ℝ) / T j ≤ B / T j := div_le_div_of_nonneg_right hkc (Nat.cast_nonneg _)
        _ ≤ B / Tmin j := div_le_div_of_nonneg_left (Nat.cast_nonneg B) hpos hlen
        _ ≤ uniformIntervalError (Tmin j) B := by
          unfold uniformIntervalError
          exact div_le_div_of_nonneg_right (by nlinarith [show (0 : ℝ) ≤ B from Nat.cast_nonneg B]) hpos.le
  change distance ((piMass μ).mapDomain _) _ ≤ _
  rw [piMass_map, uniformFintypeMass_pi]
  exact (piMass_probability_distance_sum d _ _
    (fun j => push_nonneg _ _ (hμ j)) (fun _ => uniformFintypeMass_nonneg _)
    (fun j => by rw [total_push, htμ j]) (fun _ => uniformFintypeMass_total _)).trans
      (Finset.sum_le_sum (fun j _ => he j))

theorem mixedBaseResidueError_rapid {α : Type*} {l : Filter α} {d : ℕ}
    (H : Finset (Fin d)) (X : α → Fin d → ℕ) (W B V : α → ℕ)
    (Tmin : α → Fin d → ℕ)
    (hX : ∀ j ∈ H, PowerDominates l (fun w => (X w j : ℝ))
      (fun w => (samplingSize (W w) (B w) 0 (V w) : ℝ)))
    (hT : ∀ j, j ∉ H → PowerDominates l (fun w => (Tmin w j : ℝ))
      (fun w => (samplingSize 0 (B w) 0 (V w) : ℝ)))
    (hV : ∀ᶠ w in l, 1 ≤ V w) :
    RapidlySmall l (fun w => (V w : ℝ))
      (fun w => mixedBaseResidueError H (X w) (W w) (Tmin w) (B w)) := by
  apply RapidlySmall.finset_sum
  intro j _
  by_cases hj : j ∈ H
  · simpa only [if_pos hj] using residueError_rapid (hX j hj) hV
  · simpa only [if_neg hj] using uniform_interval_residue_cap_rapid (hT j hj) hV

end Hindman168
