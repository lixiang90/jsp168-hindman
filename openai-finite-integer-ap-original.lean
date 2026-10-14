import OAI.Combinatorics.Progressions.Model
import OAI.Combinatorics.Progressions.FixedDensity.Conclusions
import OAI.Combinatorics.Progressions.FixedDensity.CountExtraction
import OAI.Combinatorics.Progressions.FixedDensity.ShortInterval

/-! Attributed excerpt from OpenAI math at the pinned commit.
Original: Probability/RelativeSourceDensityParameter.lean.
Only the natural-progression, cyclic interval and fixed-density extraction
declarations are retained. Their mathematical statements and proof bodies
are unchanged here. Apache-2.0; copyright original OpenAI contributors.
See FINITE-INTEGER-AP-PROVENANCE.json for exact whole-source/excerpt hashes.
-/

namespace OAI
section

namespace Erdos3.FixedDensity

theorem exists_naturalAP_of_cyclicAPVal_shortInterval
    {A : Set ℕ} {k N : ℕ} [NeZero N]
    (a d : ZMod N) (hd : d ≠ 0) (hk : 2 ≤ k)
    (L U : ℤ)
    (hinterval :
      ∀ j : ℕ, j < k →
        L ≤ cyclicAPVal a d j ∧ cyclicAPVal a d j ≤ U)
    (hwidth : 2 * (U - L) < (N : ℤ))
    (hA : ∀ j : ℕ, j < k → cyclicAPVal a d j ∈ A) :
    ∃ x step : ℕ, 1 ≤ step ∧
      ∀ j : ℕ, j < k → x + step * j ∈ A := by
  obtain ⟨s, hs, haffine⟩ :=
    cyclicAPVal_isIntegerAP a d hd L U hinterval hwidth
  rcases lt_or_gt_of_ne hs with hsneg | hspos
  · let step : ℕ := (-s).toNat
    have hstep_cast : (step : ℤ) = -s := by
      exact Int.natCast_toNat_eq_self.mpr (neg_nonneg.mpr hsneg.le)
    have hstep_pos : 0 < step := by omega
    refine ⟨cyclicAPVal a d (k - 1), step, hstep_pos, ?_⟩
    intro j hj
    have hlast : k - 1 < k := by omega
    have hrev : k - 1 - j < k := by omega
    have hindex :
        ((k - 1 - j : ℕ) : ℤ) = (k - 1 : ℕ) - (j : ℤ) := by
      omega
    have hterm :
        cyclicAPVal a d (k - 1) + step * j =
          cyclicAPVal a d (k - 1 - j) := by
      apply Int.ofNat_inj.mp
      push_cast
      rw [hstep_cast, haffine (k - 1) hlast,
        haffine (k - 1 - j) hrev, hindex]
      ring
    rw [hterm]
    exact hA (k - 1 - j) hrev
  · let step : ℕ := s.toNat
    have hstep_cast : (step : ℤ) = s := by
      exact Int.natCast_toNat_eq_self.mpr hspos.le
    have hstep_pos : 0 < step := by omega
    refine ⟨cyclicAPVal a d 0, step, hstep_pos, ?_⟩
    intro j hj
    have hterm :
        cyclicAPVal a d 0 + step * j = cyclicAPVal a d j := by
      apply Int.ofNat_inj.mp
      push_cast
      rw [hstep_cast, haffine j hj]
      ring
    rw [hterm]
    exact hA j hj

end Erdos3.FixedDensity

namespace Erdos3

open FixedDensity

noncomputable def cyclicIntervalSet (S : Finset ℕ) (m : ℕ) [NeZero m] : Finset (ZMod m) := by
  classical
  exact Finset.univ.filter fun x => x.val ∈ S

theorem cyclicIntervalSet_card {S : Finset ℕ} {N m : ℕ} [NeZero m]
    (hS : S ⊆ Finset.range N) (hNm : N ≤ m) : (cyclicIntervalSet S m).card = S.card := by
  classical
  symm
  apply Finset.card_bij (fun (x : ℕ) _ => (x : ZMod m))
  · intro x hx
    have hxm : x < m := (Finset.mem_range.mp (hS hx)).trans_le hNm
    simpa only [cyclicIntervalSet, Finset.mem_filter, Finset.mem_univ, true_and,
      ZMod.val_natCast_of_lt hxm] using hx
  · intro x hx y hy hxy
    have hxm : x < m := (Finset.mem_range.mp (hS hx)).trans_le hNm
    have hym : y < m := (Finset.mem_range.mp (hS hy)).trans_le hNm
    simpa only [ZMod.val_natCast_of_lt hxm, ZMod.val_natCast_of_lt hym] using
      congrArg (ZMod.val : ZMod m → ℕ) hxy
  · intro z hz
    have hzS : z.val ∈ S := (Finset.mem_filter.mp hz).2
    exact ⟨z.val, hzS, ZMod.natCast_zmod_val z⟩

theorem fixed_density_hasAP (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀, ∀ S : Finset ℕ,
      S ⊆ Finset.range N → δ * N ≤ (S.card : ℝ) → HasAP (S : Set ℕ) k := by
  classical
  let K := max 2 k
  obtain ⟨c, hc, hcount⟩ := FixedDensity.szemeredi K (le_max_left _ _)
    (div_pos hδ (by norm_num : (0 : ℝ) < 4))
  let N₀ := ⌈1 / c⌉₊ + 1
  refine ⟨N₀, by dsimp [N₀]; omega, ?_⟩
  intro N hN S hS hdensity
  have hN0 : 0 < N := by dsimp [N₀] at hN; omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have hNc : 1 / c < (N : ℝ) := by
    have hlo := Nat.le_ceil (1 / c)
    have hhi : (⌈1 / c⌉₊ : ℝ) + 1 ≤ N := by exact_mod_cast hN
    linarith
  let m := 4 * N
  let : NeZero m := ⟨by dsimp [m]; omega⟩
  let T := cyclicIntervalSet S m
  have hNm : N ≤ m := by dsimp [m]; omega
  have hmR : (0 : ℝ) < m := by dsimp [m]; positivity
  have hmean : δ / 4 ≤ mean (finsetIndicator T) := by
    rw [mean_finsetIndicator, cyclicIntervalSet_card hS hNm, ZMod.card]
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4) hmR).mpr
    dsimp [m]
    push_cast
    nlinarith
  have hcyclic := hcount m T hmean
  have hf0 : ∀ x : ZMod m, 0 ≤ finsetIndicator T x := by
    intro x
    unfold finsetIndicator
    split <;> norm_num
  have hf1 : ∀ x : ZMod m, finsetIndicator T x ≤ 1 := by
    intro x
    unfold finsetIndicator
    split <;> norm_num
  have hmean1 : mean (finsetIndicator T) ≤ 1 := mean_le_of_le_const hf1
  have hmc : 1 < (m : ℝ) * c := by
    have hNc' := (div_lt_iff₀ hc).mp hNc
    have hNmR : (N : ℝ) ≤ m := by exact_mod_cast hNm
    exact hNc'.trans_le (mul_le_mul_of_nonneg_right hNmR hc.le)
  have hoff : 0 < cyclicAPOffDiagMass K m (finsetIndicator T) := by
    apply cyclicAPOffDiagMass_pos_of_count (by dsimp [K]; omega) hf0 hf1
    calc
      _ = mean (finsetIndicator T) := by simp
      _ ≤ 1 := hmean1
      _ < (m : ℝ) * c := hmc
      _ ≤ _ := mul_le_mul_of_nonneg_left hcyclic hmR.le
  obtain ⟨a, d, hd, hpos⟩ := exists_cyclicAP_of_offDiagMass_pos hf0 hoff
  have hterms (j : ℕ) (hj : j < K) : cyclicAPVal a d j ∈ S := by
    have hpositive := hpos (⟨j, hj⟩ : Fin K)
    have hmem : cyclicAPTerm a d (⟨j, hj⟩ : Fin K) ∈ T := by
      by_contra hn
      rw [finsetIndicator_of_not_mem hn] at hpositive
      linarith
    simpa only [T, cyclicIntervalSet, Finset.mem_filter, Finset.mem_univ, true_and,
      cyclicAPVal, cyclicAPTerm] using hmem
  have hinterval : ∀ j < K, (0 : ℤ) ≤ cyclicAPVal a d j ∧ (cyclicAPVal a d j : ℤ) ≤ N := by
    intro j hj
    have hlt := Finset.mem_range.mp (hS (hterms j hj))
    exact ⟨by positivity, by exact_mod_cast hlt.le⟩
  have hwidth : 2 * ((N : ℤ) - 0) < (m : ℤ) := by dsimp [m]; omega
  obtain ⟨a', d', hd', hAP⟩ := exists_naturalAP_of_cyclicAPVal_shortInterval
    a d hd (le_max_left _ _) 0 N hinterval hwidth hterms
  refine ⟨a', d', by omega, ?_⟩
  intro j hj
  simpa only [mul_comm] using hAP j (hj.trans_le (le_max_right 2 k))

end Erdos3

end
end OAI
