from pathlib import Path

src = Path('Hindman168/RoughNativeRescaledPieceSelection.lean').read_text(encoding='utf-8')
src = src.replace('import Hindman168.RoughDependentRescaledSelection', '''import Hindman168.RoughNativeRescaledPieceSelection
import Hindman168.RoughDependentRescaledSelection
import Hindman168.RoughRescaledPieceGeometry
import Hindman168.RoughNativeKernelSpatialPolynomial
import Hindman168.RoughNativeKernelDegreeBound''')
src = src.replace('theorem rough_native_rescaled_piece_selection', 'theorem rough_native_piece_descent', 1)
needle = '      let Q := fun j : Fin K =>'
src = src.replace(needle, '''      ∀ (pLog : RoughVectorMvPolynomial (Option κ) D.E)
        (_hpLog : ∀ x, roughVectorMvEval pLog x =
          nativeLieGlobalLogarithm (E := D.E) (I := D.I) (P x))
        (degree : ℕ) (_ha : a.totalDegree ≤ degree) (_hm : m.totalDegree ≤ degree)
        (_hdegree : RoughVectorMvDegreeLE pLog degree),
''' + needle)
src = src.replace('          (∀ j, c*Z ≤ (r j : ℝ)-l j) →', '''          (∀ j, c*Z ≤ (r j : ℝ)-l j) →
          (∀ j, (2*N*K : ℤ) ≤ r j-l j) → 1 ≤ Z/K →''')
src = src.replace('            0 < (alignmentBoxClass lo hi v t).card ∧', '''            ∃ pNew : RoughVectorMvPolynomial (Option κ) (family (indices p)).E,
            Module.finrank ℝ (family (indices p)).E < Module.finrank ℝ D.E ∧
            RoughVectorMvDegreeLE pNew (roughKernelDegreeFactor step*degree) ∧
            (∀ (z' : ℝ) (y : κ → ℝ), roughVectorMvEval pNew (Option.elim · z' y) =
              nativeLieGlobalLogarithm (E := (family (indices p)).E) (I := (family (indices p)).I)
                (Q (indices p) (Option.elim · z' (fun j => (u j : ℝ)+(K : ℝ)*y j)))) ∧
            (∀ j, (c/(4*N))*(Z/K) ≤ (hi j : ℝ)-lo j ∧
              (hi j : ℝ)-lo j ≤ (4*C/N)*(Z/K) ∧
              |(lo j : ℝ)| ≤ (C+1)*(Z/K) ∧ |(hi j : ℝ)| ≤ (C+1)*(Z/K)) ∧
            0 < (alignmentBoxClass lo hi v t).card ∧''')
start = src.index('  obtain ⟨N, L, hN, hstage⟩')
src = src[:start] + '''  obtain ⟨N, L, hN, hstage⟩ := rough_native_rescaled_piece_selection D S hS χ hχ hQ V hVr hVS hχV
    K hK hperiod support d hd A C B hA hC hB Lip hεf hεa
  refine ⟨N, L, hN, ?_⟩
  intro w H q z Z P0 theta M0 M hmodels hz hZ h0 hconst l r hlen hside hl hr F hF hbound m a P hP hchar
    pLog hpLog degree ha hm hdegree Q
  obtain ⟨indices, tests, hlip, hsup, hselect⟩ := hstage w H q z Z P0 theta M0 M
    hmodels hz hZ h0 hconst l r hlen hside hl hr F hF hbound P hP hchar
  refine ⟨indices, tests, hlip, hsup, ?_⟩
  intro a0 t ht hcop c θ η hc htZ hlen' hpiece hscale hgap hbad
  obtain ⟨p, v, hp, hfull, hdisc⟩ := hselect a0 t ht hcop c θ η hc htZ hlen' hgap hbad
  let u : κ → ℤ := fun j => (p.2 j).val
  obtain ⟨pNew, hdNew, heNew⟩ := rough_native_kernel_spatial_log_polynomial D S hS χ hχ hQ V hVr
    ((indices p).val : ℤ) hVS hχV a m P hP hchar pLog hpLog degree ha hm hdegree
    (fun j => (u j : ℝ)) (K : ℝ)
  refine ⟨p, v, pNew, ?_, rough_native_kernel_degree_uniform D hdNew, heNew, ?_, hp, hfull, hdisc⟩
  · exact roughNativeKernelNilmanifold_finrank_lt D S hS χ hχ hQ V hVr _ hVS
      (by rw [hχV]; norm_num)
  · exact rough_rescaled_piece_geometry l r N K hN hK hpiece c C Z hlen' hside hl hr hscale p

end Hindman168
'''
Path('Hindman168/RoughNativePieceDescent.lean').write_text(src, encoding='utf-8')
