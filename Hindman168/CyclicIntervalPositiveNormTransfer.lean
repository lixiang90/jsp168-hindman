import Hindman168.CyclicIntervalCubeTransfer
import Hindman168.SubgroupGowersRoot

namespace Hindman168
open scoped Classical

/-- The dyadic real root of the actual interval cube mean. Root identities
are used below only after the actual cube mean has been proved nonnegative. -/
noncomputable def integerIntervalPeriodicGowersValue (q d L : ℕ) (f : ZMod q → ℝ) : ℝ :=
  (integerIntervalPeriodicCubeMean q d L f) ^ ((2 ^ d : ℕ)⁻¹ : ℝ)

theorem integerIntervalPeriodicGowersValue_pow (q d L : ℕ) (f : ZMod q → ℝ)
    (hm : 0 ≤ integerIntervalPeriodicCubeMean q d L f) :
    integerIntervalPeriodicGowersValue q d L f ^ (2 ^ d) =
      integerIntervalPeriodicCubeMean q d L f :=
  Real.rpow_inv_natCast_pow hm (pow_ne_zero _ (by decide))

theorem integerIntervalPeriodicGowersValue_nonneg (q d L : ℕ) (f : ZMod q → ℝ)
    (hm : 0 ≤ integerIntervalPeriodicCubeMean q d L f) :
    0 ≤ integerIntervalPeriodicGowersValue q d L f :=
  Real.rpow_nonneg hm _

/-- One fixed number of periods, depending only on dimension and the
positive cyclic norm threshold, retains half that threshold on every cell. -/
theorem cyclic_positive_norm_interval_transfer (d : ℕ) (hd : 0 < d)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℕ, d + 1 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (f : ZMod q → ℝ),
      (∀ x, |f x| ≤ 1) →
      δ ≤ subgroupGowersValue (⊤ : AddSubgroup (ZMod q)) d f →
        0 < integerIntervalPeriodicCubeMean q d (K * q) f ∧
          δ / 2 ≤ integerIntervalPeriodicGowersValue q d (K * q) f := by
  have hn : (2 : ℕ) ^ d ≠ 0 := pow_ne_zero _ (by decide)
  have hhalf : 0 < δ / 2 := by positivity
  have hgap : 0 < δ ^ (2 ^ d) - (δ / 2) ^ (2 ^ d) :=
    sub_pos.mpr (pow_lt_pow_left₀ (by linarith) hhalf.le hn)
  let ε := δ ^ (2 ^ d) - (δ / 2) ^ (2 ^ d)
  obtain ⟨N, hN⟩ := exists_nat_gt (integerIntervalCubeTransferConstant d / ε)
  let K := max (d + 1) N
  have hK : d + 1 ≤ K := le_max_left _ _
  have hKp : 0 < K := lt_of_lt_of_le (Nat.succ_pos d) hK
  have hKr : (0 : ℝ) < K := by exact_mod_cast hKp
  have hlarge : integerIntervalCubeTransferConstant d / ε < (K : ℝ) :=
    hN.trans_le (by exact_mod_cast le_max_right (d + 1) N)
  have hcost : integerIntervalCubeTransferConstant d / K < ε := by
    apply (div_lt_iff₀ hKr).mpr
    have hb := (div_lt_iff₀ hgap).mp hlarge
    nlinarith
  refine ⟨K, hK, ?_⟩
  intro q _ f hf hg
  have hcyclic : δ ^ (2 ^ d) ≤ subgroupCubeAverage (⊤ : AddSubgroup (ZMod q)) d f := by
    rw [← subgroupGowersValue_pow _ d hd]
    exact pow_le_pow_left₀ hδ.le hg _
  have he := integerIntervalPeriodicCubeMean_period_error q d K hK f hf
  have hlower : (δ / 2) ^ (2 ^ d) < integerIntervalPeriodicCubeMean q d (K * q) f := by
    have hb := (abs_le.mp he).1
    dsimp only [ε] at hcost
    linarith
  have hm : 0 < integerIntervalPeriodicCubeMean q d (K * q) f :=
    (pow_pos hhalf _).trans hlower
  refine ⟨hm, ?_⟩
  apply le_of_pow_le_pow_left₀ hn
    (integerIntervalPeriodicGowersValue_nonneg q d (K * q) f hm.le)
  rw [integerIntervalPeriodicGowersValue_pow q d (K * q) f hm.le]
  exact hlower.le

end Hindman168
