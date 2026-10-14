import Hindman168.HarmonicCutoffBands

/-! A discarded short bin forces its actual pivot near a cutoff endpoint.
The witness to failure may use a different tail product from the sample.
All preimages are checked on the entire common tail-product range. -/

namespace Hindman168

theorem shortBin_preimage_contained {Q V tlo C L U t : ℝ}
    (htlo : 0 < tlo) (hL : 0 ≤ L) (hU : 0 ≤ U)
    (ht : tlo ≤ t) (htC : t ≤ C * tlo)
    (hlo : (C * tlo) * L ≤ Q) (hhi : Q + V ≤ tlo * U) :
    L ≤ Q / t ∧ (Q + V) / t ≤ U := by
  have htpos := htlo.trans_le ht
  constructor
  · apply (le_div_iff₀ htpos).mpr
    simpa only [mul_comm L] using (mul_le_mul_of_nonneg_right htC hL).trans hlo
  · apply (div_le_iff₀ htpos).mpr
    simpa only [mul_comm U] using hhi.trans (mul_le_mul_of_nonneg_right ht hU)

theorem shortBin_failed_preimage_endpoints {Q V tlo C L U : ℝ}
    (htlo : 0 < tlo) (hL : 0 ≤ L) (hU : 0 ≤ U)
    (hbad : ∃ t, tlo ≤ t ∧ t ≤ C * tlo ∧ (Q / t < L ∨ U < (Q + V) / t)) :
    Q < (C * tlo) * L ∨ tlo * U < Q + V := by
  by_contra hh
  have hlo : (C * tlo) * L ≤ Q := le_of_not_gt (fun h => hh (Or.inl h))
  have hhi : Q + V ≤ tlo * U := le_of_not_gt (fun h => hh (Or.inr h))
  obtain ⟨t, ht, htC, hb⟩ := hbad
  have hc := shortBin_preimage_contained htlo hL hU ht htC hlo hhi
  rcases hb with hb | hb
  · exact (not_lt_of_ge hc.1) hb
  · exact (not_lt_of_ge hc.2) hb

theorem shortBin_bad_endpoints_pivot_band {Q tlo C X R t p : ℝ}
    (htlo : 0 < tlo) (hC : 1 ≤ C) (hX : 1 ≤ X) (hR : 0 ≤ R) (hsmall : 6 * R ≤ X)
    (ht : tlo ≤ t) (htC : t ≤ C * tlo) (hp : 0 ≤ p)
    (hbinLo : Q ≤ t * p) (hbinHi : t * p < Q + tlo * R)
    (hbad : Q < (C * tlo) * (X + 2 * R) ∨ tlo * (X ^ 2 - 2 * R) < Q + tlo * R) :
    p < (2 * C) * X ∨ X ^ 2 / (2 * C) ≤ p := by
  have hc : 0 < C := by linarith
  rcases hbad with hb | hb
  · left
    have hpLo := mul_le_mul_of_nonneg_right ht hp
    have hpre : tlo * p < tlo * (C * (X + 2 * R) + R) := by nlinarith
    have hpbound : p < C * (X + 2 * R) + R := by nlinarith
    have hcr := mul_le_mul_of_nonneg_left hsmall hc.le
    have hrC := mul_le_mul_of_nonneg_right hC hR
    have hend : C * (X + 2 * R) + R ≤ (2 * C) * X := by nlinarith
    exact hpbound.trans_le hend
  · right
    have hpHi := mul_le_mul_of_nonneg_right htC hp
    have hpre : tlo * (X ^ 2 - 3 * R) < tlo * (C * p) := by nlinarith
    have hpbound : X ^ 2 - 3 * R < C * p := by nlinarith
    apply (div_le_iff₀ (by positivity : 0 < 2 * C)).mpr
    have hxsq : X ≤ X ^ 2 := by nlinarith
    nlinarith

theorem shortBin_failed_cutoff_pivot_band {Q tlo C X R t p : ℝ}
    (htlo : 0 < tlo) (hC : 1 ≤ C) (hX : 1 ≤ X) (hR : 0 ≤ R) (hsmall : 6 * R ≤ X)
    (ht : tlo ≤ t) (htC : t ≤ C * tlo) (hp : 0 ≤ p)
    (hbinLo : Q ≤ t * p) (hbinHi : t * p < Q + tlo * R)
    (hbad : ∃ t', tlo ≤ t' ∧ t' ≤ C * tlo ∧
      (Q / t' < X + 2 * R ∨ X ^ 2 - 2 * R < (Q + tlo * R) / t')) :
    p < (2 * C) * X ∨ X ^ 2 / (2 * C) ≤ p := by
  have hL : 0 ≤ X + 2 * R := by linarith
  have hU : 0 ≤ X ^ 2 - 2 * R := by nlinarith
  exact shortBin_bad_endpoints_pivot_band htlo hC hX hR hsmall ht htC hp hbinLo hbinHi
    (shortBin_failed_preimage_endpoints htlo hL hU hbad)

end Hindman168
