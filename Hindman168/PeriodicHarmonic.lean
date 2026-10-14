import Hindman168.ResidueHarmonic
import Mathlib.Data.Nat.Totient

/-!
# Periodic harmonic sampling with the paper's exact error constant

Chinese remainder gives `totient W` allowed classes modulo `W*k` when
`k` is coprime to `W`. They are disjoint. Summing the sharp one-class
estimate yields the original `totient W / A` bound, with real endpoints.
-/

namespace Hindman168

open scoped BigOperators

def unitResidues (W k a : ℕ) : Finset ℕ :=
  (Finset.range (W * k)).filter (fun b => b.Coprime W ∧ b % k = a)

noncomputable def roughResidueWindow (A B : ℝ) (W k a : ℕ) : Finset ℕ :=
  (Finset.Ico ⌈A⌉₊ ⌈B⌉₊).filter (fun n => n.Coprime W ∧ n % k = a)

noncomputable def roughResidueHarmonic (A B : ℝ) (W k a : ℕ) : ℝ :=
  ∑ n ∈ roughResidueWindow A B W k a, (n : ℝ)⁻¹

noncomputable def unitDensity (W : ℕ) : ℝ := (W.totient : ℝ) / W

theorem unitResidues_card {W k a : ℕ} (hW : 0 < W) (hk : 0 < k)
    (hco : W.Coprime k) (ha : a < k) : (unitResidues W k a).card = W.totient := by
  classical
  let V := (Finset.range W).filter (fun b => W.Coprime b)
  have hc : (unitResidues W k a).card = V.card := by
    apply Finset.card_bij (fun b _ => b % W)
    · intro b hb
      obtain ⟨_, hbc, _⟩ := Finset.mem_filter.mp hb
      have hg : (b % W).Coprime W := by
        change (b % W).gcd W = 1
        rw [(Nat.mod_modEq b W).gcd_eq]
        exact hbc
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt b hW), hg.symm⟩
    · intro b hb c hc heq
      obtain ⟨hb, _, hbmod⟩ := Finset.mem_filter.mp hb
      obtain ⟨hc, _, hcmod⟩ := Finset.mem_filter.mp hc
      have hm : Nat.ModEq (W * k) b c :=
        (Nat.modEq_and_modEq_iff_modEq_mul hco).mp ⟨heq, hbmod.trans hcmod.symm⟩
      exact hm.eq_of_lt_of_lt (Finset.mem_range.mp hb) (Finset.mem_range.mp hc)
    · intro b hb
      obtain ⟨hbW, hbc⟩ := Finset.mem_filter.mp hb
      have hbW' := Finset.mem_range.mp hbW
      let z := Nat.chineseRemainder hco b a
      have hzW : z.val % W = b := by
        have h := z.property.1
        change z.val % W = b % W at h
        simpa only [Nat.mod_eq_of_lt hbW'] using h
      have hzk : z.val % k = a := by
        have h := z.property.2
        change z.val % k = a % k at h
        simpa only [Nat.mod_eq_of_lt ha] using h
      have hzc : z.val.Coprime W := by
        change z.val.gcd W = 1
        rw [z.property.1.gcd_eq]
        exact hbc.symm
      refine ⟨z.val, ?_, hzW⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
        (Nat.chineseRemainder_lt_mul hco b a hW.ne' hk.ne'), hzc, hzk⟩
  exact hc.trans (Nat.totient_eq_card_coprime W).symm

theorem roughResidueWindow_partition {A B : ℝ} {W k a : ℕ} (hW : 0 < W) (hk : 0 < k) :
    roughResidueWindow A B W k a =
      (unitResidues W k a).biUnion (fun b => residueWindow A B (W * k) b) := by
  classical
  ext n
  constructor
  · intro hn
    obtain ⟨hnI, hnc, hna⟩ := Finset.mem_filter.mp hn
    let b := n % (W * k)
    have hm : Nat.ModEq (W * k) b n := Nat.mod_modEq n (W * k)
    have hbc : b.Coprime W := by
      change b.gcd W = 1
      rw [(hm.of_mul_right k).gcd_eq]
      exact hnc
    have hbka : b % k = a := by
      have h := hm.of_mul_left W
      change b % k = n % k at h
      exact h.trans hna
    apply Finset.mem_biUnion.mpr
    refine ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (Nat.mod_lt n (Nat.mul_pos hW hk)), hbc, hbka⟩, ?_⟩
    exact Finset.mem_filter.mpr ⟨hnI, rfl⟩
  · intro hn
    obtain ⟨b, hb, hnb⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨hbq, hbc, hbka⟩ := Finset.mem_filter.mp hb
    obtain ⟨hnI, hnb⟩ := Finset.mem_filter.mp hnb
    have hm : Nat.ModEq (W * k) n b := by
      change n % (W * k) = b % (W * k)
      simpa only [Nat.mod_eq_of_lt (Finset.mem_range.mp hbq)] using hnb
    have hnc : n.Coprime W := by
      change n.gcd W = 1
      rw [(hm.of_mul_right k).gcd_eq]
      exact hbc
    have hna : n % k = a := by
      have h := hm.of_mul_left W
      change n % k = b % k at h
      exact h.trans hbka
    exact Finset.mem_filter.mpr ⟨hnI, hnc, hna⟩

theorem roughResidueHarmonic_partition {A B : ℝ} {W k a : ℕ} (hW : 0 < W) (hk : 0 < k) :
    roughResidueHarmonic A B W k a =
      ∑ b ∈ unitResidues W k a, residueHarmonic A B (W * k) b := by
  classical
  have hd : (↑(unitResidues W k a) : Set ℕ).PairwiseDisjoint
      (fun b => residueWindow A B (W * k) b) := by
    intro b _ c _ hbc
    apply Finset.disjoint_left.mpr
    intro n hnb hnc
    exact hbc ((Finset.mem_filter.mp hnb).2.symm.trans (Finset.mem_filter.mp hnc).2)
  rw [roughResidueHarmonic, roughResidueWindow_partition hW hk, Finset.sum_biUnion hd]
  rfl

/-- Paper, sampling lemma, equation `periodic-harmonic`, with no endpoint
rounding loss and with the original constant `phi(W)/A`. -/
theorem periodic_harmonic_error {A B : ℝ} {W k a : ℕ}
    (hA : 0 < A) (hAB : A < B) (hW : 0 < W) (hk : 0 < k)
    (hco : W.Coprime k) (ha : a < k) :
    |roughResidueHarmonic A B W k a - unitDensity W / k * Real.log (B / A)| ≤
      (W.totient : ℝ) / A := by
  classical
  have hc := unitResidues_card hW hk hco ha
  have hm : (∑ b ∈ unitResidues W k a, Real.log (B / A) / (W * k : ℕ)) =
      unitDensity W / k * Real.log (B / A) := by
    rw [Finset.sum_const, nsmul_eq_mul, hc]
    simp only [unitDensity, Nat.cast_mul, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [← hm, roughResidueHarmonic_partition hW hk, ← Finset.sum_sub_distrib]
  calc
    |∑ b ∈ unitResidues W k a,
        (residueHarmonic A B (W * k) b - Real.log (B / A) / (W * k : ℕ))| ≤
        ∑ b ∈ unitResidues W k a,
          |residueHarmonic A B (W * k) b - Real.log (B / A) / (W * k : ℕ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b ∈ unitResidues W k a, A⁻¹ := by
      apply Finset.sum_le_sum
      intro b hb
      exact residue_harmonic_error hA hAB (Nat.mul_pos hW hk)
        (Finset.mem_range.mp (Finset.mem_filter.mp hb).1)
    _ = (W.totient : ℝ) / A := by rw [Finset.sum_const, nsmul_eq_mul, hc]; rfl

end Hindman168
