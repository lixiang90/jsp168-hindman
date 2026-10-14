import Hindman168.ShortBinCutoffProbability

namespace Hindman168

theorem shortBin_bad_endpoints_failed_normalized {Q tlo C X R t : ℝ} (p : ℕ)
    (htlo : 0 < tlo) (hC : 1 ≤ C) (hR : 0 ≤ R)
    (ht : tlo ≤ t) (htC : t ≤ C * tlo)
    (hbinLo : Q ≤ t * p) (hbinHi : t * p < Q + tlo * R)
    (hbad : Q < X * (C * tlo) ∨ X ^ 2 * tlo < Q + tlo * R) :
    failedCutoffShortBin X R 1 C p := by
  have hc : 0 < C := by linarith
  refine ⟨Q / tlo, t / tlo, ?_, ?_, ?_, ?_, ?_⟩
  · exact (le_div_iff₀ htlo).mpr (by simpa only [one_mul] using ht)
  · simpa only [mul_one] using (div_le_iff₀ htlo).mpr htC
  · apply (div_le_iff₀ htlo).mpr
    calc
      Q ≤ t * p := hbinLo
      _ = (t / tlo * p) * tlo := by field_simp
  · have hh : t * p / tlo < Q / tlo + R := by
      apply (div_lt_iff₀ htlo).mpr
      calc
        t * p < Q + tlo * R := hbinHi
        _ = (Q / tlo + R) * tlo := by field_simp
    simpa only [div_mul_eq_mul_div, one_mul] using hh
  · rcases hbad with hb | hb
    · refine ⟨C, hC, by simp, Or.inl ?_⟩
      have hq : Q / tlo / C < X := by
        apply (div_lt_iff₀ hc).mpr
        apply (div_lt_iff₀ htlo).mpr
        nlinarith [hb]
      exact hq.trans_le (by linarith)
    · refine ⟨1, le_rfl, by simpa only [mul_one] using hC, Or.inr ?_⟩
      simp only [one_mul, div_one]
      have hq : X ^ 2 < Q / tlo + R := by
        have he : (Q / tlo + R) * tlo = Q + tlo * R := by field_simp
        nlinarith
      linarith

end Hindman168
