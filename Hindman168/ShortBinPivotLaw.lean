import Hindman168.ShortBinHarmonic
import Hindman168.FiniteConditionalLikelihood
import Hindman168.CompleteResidueCellMass

/-!
# Short-bin conditioning of the original harmonic pivot law

Cutoff containment is explicit. The prescribed residue is a unit for the
roughness modulus, which divides the residue modulus. Thus its roughness
test is automatic, and the original common harmonic normalizer cancels
in the posterior domination bound.
-/

namespace Hindman168

open FiniteMass
open scoped BigOperators Classical

theorem mem_residueWindow {A B : ℝ} {q a n : ℕ} :
    n ∈ residueWindow A B q a ↔ A ≤ (n : ℝ) ∧ (n : ℝ) < B ∧ n % q = a := by
  simp only [residueWindow, Finset.mem_filter, Finset.mem_Ico, Nat.ceil_le,
    Nat.lt_ceil, and_assoc]

theorem shortBin_rawMass_event {Q V t : ℝ} {X W q a : ℕ}
    (ht : 0 < t) (hlo : (X : ℝ) ≤ Q / t)
    (hhi : (Q + V) / t ≤ (X ^ 2 : ℕ)) (hWq : W ∣ q) (ha : a.Coprime W) :
    event (rawMass X W) (fun p => Q ≤ t * p ∧ t * p < Q + V ∧ p % q = a) =
      residueHarmonic (Q / t) ((Q + V) / t) q a / harmonicNormalizer X W := by
  have hs : (rawMass X W).support ⊆ harmonicWindow X W := by
    intro p hp
    by_contra hn
    have hz : rawMass X W p = 0 := by rw [rawMass_apply]; simp [harmonicWeight, hn]
    exact (Finsupp.mem_support_iff.mp hp) hz
  have he : (harmonicWindow X W).filter
      (fun p : ℕ => Q ≤ t * p ∧ t * p < Q + V ∧ p % q = a) =
      residueWindow (Q / t) ((Q + V) / t) q a := by
    ext p
    simp only [Finset.mem_filter, mem_residueWindow]
    constructor
    · rintro ⟨_, hp, hp', hres⟩
      exact ⟨(div_le_iff₀ ht).mpr (by simpa [mul_comm] using hp),
        (lt_div_iff₀ ht).mpr (by simpa [mul_comm] using hp'), hres⟩
    · rintro ⟨hp, hp', hres⟩
      have hpX : X ≤ p := by exact_mod_cast hlo.trans hp
      have hpX' : p < X ^ 2 := by exact_mod_cast hp'.trans_le hhi
      refine ⟨?_, ?_, ?_, hres⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hpX, hpX'⟩,
          (residue_coprime_iff W q a p hWq hres).mpr ha⟩
      · simpa [mul_comm] using (div_le_iff₀ ht).mp hp
      · simpa [mul_comm] using (lt_div_iff₀ ht).mp hp'
  rw [event_eq_sum _ _ hs]
  trans ∑ p ∈ (harmonicWindow X W).filter
    (fun p : ℕ => Q ≤ t * p ∧ t * p < Q + V ∧ p % q = a), rawMass X W p
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    split_ifs <;> rfl
  rw [he, residueHarmonic, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' : p ∈ harmonicWindow X W := (Finset.mem_filter.mp (he ▸ hp)).1
  rw [rawMass_apply, harmonicWeight, if_pos hp']

theorem shortBin_pivot_posterior_domination {α : Type*} (μ : Mass α) (t : α → ℝ)
    (B : α → Prop) {Q tlo R C : ℝ} {X W q a : ℕ}
    (hμ : ∀ x, 0 ≤ μ x) (hμt : total μ = 1)
    (hQ : 0 < Q) (htlo : 0 < tlo) (hR : 0 < R) (hWQ : tlo * R ≤ Q)
    (ht : ∀ x ∈ μ.support, 0 < t x)
    (htC : ∀ x ∈ μ.support, t x ≤ C * tlo)
    (hlo : ∀ x ∈ μ.support, (X : ℝ) ≤ Q / t x)
    (hhi : ∀ x ∈ μ.support, (Q + tlo * R) / t x ≤ (X ^ 2 : ℕ))
    (hq : 0 < q) (ha : a < q) (hWq : W ∣ q) (hunit : a.Coprime W)
    (hZ : 0 < harmonicNormalizer X W) (hsmall : 2 * C * q / R ≤ 1 / 2) :
    event (conditionMass (conditionalJoint μ (fun _ => rawMass X W))
      (fun xp => Q ≤ t xp.1 * xp.2 ∧ t xp.1 * xp.2 < Q + tlo * R ∧ xp.2 % q = a))
      (fun xp => B xp.1) ≤ 3 * event μ B := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  let m := Real.log ((Q + tlo * R) / Q) / q
  have hm : 0 < m := div_pos (shortBin_log_pos hQ (mul_pos htlo hR)) hqR
  apply conditionJoint_outer_domination μ (fun _ => rawMass X W) _ B hμ hμt
    (b := (m / 2) / harmonicNormalizer X W) (div_pos (by positivity) hZ) (by norm_num)
  · intro x hx
    rw [shortBin_rawMass_event (ht x hx) (hlo x hx) (hhi x hx) hWq hunit]
    exact div_le_div_of_nonneg_right
      (shortBin_harmonic_half_bounds hQ htlo hR hWQ (ht x hx) (htC x hx) hq ha hsmall).1 hZ.le
  · intro x hx
    rw [shortBin_rawMass_event (ht x hx) (hlo x hx) (hhi x hx) hWq hunit]
    have hb := div_le_div_of_nonneg_right
      (shortBin_harmonic_half_bounds hQ htlo hR hWQ (ht x hx) (htC x hx) hq ha hsmall).2 hZ.le
    simpa only [m, mul_div_assoc] using hb

end Hindman168
