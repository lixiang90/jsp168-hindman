from pathlib import Path

old = Path('Hindman168/RoughNativeModelPieceDescent.lean').read_text(encoding='utf-8')
prefix, tail = old.split('theorem rough_native_model_piece_descent', 1)
prefix = prefix.replace('namespace Hindman168', 'import Hindman168.RoughNativeBadIndex\nimport Hindman168.RoughNativeModelPieceDescent\n\nnamespace Hindman168')
header = 'theorem rough_native_model_bad_index' + tail[:tail.index('      ∃ indices :')]
start = tail.index('        ∀ (a0 : κ → ℤ)')
end = tail.index('          ∃ (p : (κ → Fin N)')
header += tail[start:end]
header += '''          ∃ (u : κ → Fin K) (j : Fin K),
            Module.finrank ℝ (family j).E < Module.finrank ℝ D.E ∧
            (∃ pNew : RoughVectorMvPolynomial (Option κ) (family j).E,
              RoughVectorMvDegreeLE pNew (roughKernelDegreeFactor step*q) ∧
              ∀ (z' : ℝ) (y : κ → ℝ), roughVectorMvEval pNew (Option.elim · z' y) =
                nativeLieGlobalLogarithm (E := (family j).E) (I := (family j).I)
                  (Q j (Option.elim · z' (fun k => ((u k).val : ℝ)+(K : ℝ)*y k)))) ∧
            RoughNativeBadIndex (family j)
              (fun x => Q j (Option.elim · (x none)
                (fun k => ((u k).val : ℝ)+(K : ℝ)*x (some k))))
              z t (Z/K) (c/(4*N)) (max (4*C/N) (C+1)) L B θ := by
  intro family
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ j, MetricSpace ((family j).G ⧸ (family j).Γ) := fun j => (family j).metric
  letI : ∀ j, TopologicalSpace ((family j).G ⧸ (family j).Γ) := fun j =>
    (family j).metric.toUniformSpace.toTopologicalSpace
  obtain ⟨N, L, hN, hstage⟩ := rough_native_model_piece_descent D S hS χ hχ hQ V hVr hVS hχV
    K hK hperiod support d hd A C B hA hC hB Lip hεf hεa
  refine ⟨N, L, hN, ?_⟩
  intro w H q z Z P0 theta M0 M hmodels hz hZ h0 hconst l r hlen hside hl hr F hF hbound
    hM0 he hP0 htheta m a P hP hchar pLog hpLog hdegree hsplit Q
  obtain ⟨indices, tests, hlip, hsup, hselect⟩ := hstage w H q z Z P0 theta M0 M
    hmodels hz hZ h0 hconst l r hlen hside hl hr F hF hbound
    hM0 he hP0 htheta P hP hchar pLog hpLog hdegree
  intro a0 t ht hcop c θ η hc htZ hlen' hpiece hscale hgap hbad
  obtain ⟨p, v, pNew, hdim, hdeg, hlog, hbox, hstep, hfull, hdisc⟩ :=
    hselect a0 t ht hcop c θ η hc htZ hlen' hpiece hscale hgap hbad
  refine ⟨p.2, indices p, hdim, ⟨pNew, hdeg, hlog⟩, ?_⟩
  refine ⟨_, _, v, tests p, hlip p, hsup p, ?_, hstep, hfull, ?_⟩
  · intro k
    have hscale0 : 0 ≤ Z/K := hscale.trans' (by norm_num)
    exact ⟨(hbox k).1,
      (hbox k).2.1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hscale0),
      (hbox k).2.2.1.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hscale0),
      (hbox k).2.2.2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hscale0)⟩
  · simpa only [Option.elim_none, Option.elim_some, roughResidueBoxAffine, Nat.cast_add,
      Int.cast_add, Int.cast_mul, Int.cast_natCast] using hdisc

end Hindman168
'''
Path('Hindman168/RoughNativeModelBadIndex.lean').write_text(prefix+header, encoding='utf-8')

old = Path('Hindman168/RoughNativeKernelLabelThinning.lean').read_text(encoding='utf-8')
prefix = old[:old.index('theorem rough_native_kernel_label_thinning')]
prefix = prefix.replace('namespace Hindman168', 'import Hindman168.RoughNativeBadIndex\nimport Hindman168.RoughNativeKernelLabelThinning\n\nnamespace Hindman168')
header = old[old.index('theorem rough_native_kernel_label_thinning'):old.index('    (K H : ℕ)')]
header = header.replace('theorem rough_native_kernel_label_thinning', 'theorem rough_native_bad_progression_thinning')
header += '''    (K H : ℕ) (hH : 0 < H) :
    ∃ N : ℕ, 0 < N ∧ ∀
    (a m : MvPolynomial (Option κ) ℝ) (P : (Option κ → ℝ) → D.G)
    (hP : ∀ x, P x ∈ nativeLieSubalgebraSubgroup (E := D.E) S)
    (hchar : ∀ x, nativeLieLogarithmCharacter (I := D.I) (G := D.G) χ (P x) =
      MvPolynomial.eval x a + MvPolynomial.eval x m)
    (p : RoughVectorMvPolynomial (Option κ) D.E)
    (_hp : ∀ x, roughVectorMvEval p x = nativeLieGlobalLogarithm (E := D.E) (I := D.I) (P x))
    (d : ℕ) (_ha : a.totalDegree ≤ d) (_hm : m.totalDegree ≤ d) (_hd : RoughVectorMvDegreeLE p d),
    ∀ (w t diff : ℕ) (Z Scale c C : ℝ) (L : NNReal) (B η : ℝ),
      0 < diff → N ≤ w →
      (∀ prime : ℕ, prime.Prime → prime ∣ diff → prime ≤ w) →
      (∀ z : ℕ, z < N → Scale ≤ (t+diff*z : ℕ) ∧ (t+diff*z : ℕ) < 2*Scale) →
      (∀ z : ℕ, z < N → (primorial w).Coprime (t+diff*z)) →
      (∀ z : ℕ, z < N → ∃ (u : κ → Fin K) (j : Fin K),
        RoughNativeBadIndex (roughNativeKernelNilmanifold D S hS χ hχ hQ V hVr (j.val : ℤ))
          (fun x => roughNativeKernelMap D S hS χ hχ hQ V hVr (j.val : ℤ) hVS hχV a m P hP hchar
            (Option.elim · (x none) (fun k => ((u k).val : ℝ)+(K : ℝ)*x (some k))))
          z (t+diff*z) Z c C L B η) →
      ∃ (a0 b : ℕ) (u : κ → Fin K) (j : Fin K),
        let Dnew := roughNativeKernelNilmanifold D S hS χ hχ hQ V hVr (j.val : ℤ)
        ∃ Qnew : (Option κ → ℝ) → Dnew.G,
        0 < b ∧ b ≤ N ∧ Module.finrank ℝ Dnew.E < Module.finrank ℝ D.E ∧
        (∀ x, Qnew x = roughNativeKernelMap D S hS χ hχ hQ V hVr (j.val : ℤ) hVS hχV a m P hP hchar
          (Option.elim · ((a0 : ℝ)+(b : ℝ)*x none)
            (fun k => ((u k).val : ℝ)+(K : ℝ)*x (some k)))) ∧
        (∃ pNew : RoughVectorMvPolynomial (Option κ) Dnew.E,
          RoughVectorMvDegreeLE pNew (roughKernelDegreeFactor s*d) ∧
          ∀ (z : ℝ) (y : κ → ℝ), roughVectorMvEval pNew (Option.elim · z y) =
            nativeLieGlobalLogarithm (E := Dnew.E) (I := Dnew.I) (Qnew (Option.elim · z y))) ∧
        0 < b*diff ∧ (∀ prime : ℕ, prime.Prime → prime ∣ b*diff → prime ≤ w) ∧
        ∀ z : ℕ, z < H → a0+b*z < N ∧
          Scale ≤ ((t+diff*a0)+(b*diff)*z : ℕ) ∧
          ((t+diff*a0)+(b*diff)*z : ℕ) < 2*Scale ∧
          (primorial w).Coprime ((t+diff*a0)+(b*diff)*z) ∧
          RoughNativeBadIndex Dnew Qnew z ((t+diff*a0)+(b*diff)*z) Z c C L B η := by
  obtain ⟨N, hN, hthin⟩ := rough_native_kernel_label_thinning (κ := κ) D S hS χ hχ hQ V hVr hVS hχV K H hH
  refine ⟨N, hN, ?_⟩
  intro a m P hP hchar p hp d ha hm hd w t diff Z Scale c C L B η hdiff hNw hsmooth hsize hrough hbad
  let bad := fun z : ℕ => fun label : (κ → Fin K) × Fin K =>
    RoughNativeBadIndex (roughNativeKernelNilmanifold D S hS χ hχ hQ V hVr (label.2.val : ℤ))
      (fun x => roughNativeKernelMap D S hS χ hχ hQ V hVr (label.2.val : ℤ) hVS hχV a m P hP hchar
        (Option.elim · (x none) (fun k => ((label.1 k).val : ℝ)+(K : ℝ)*x (some k))))
      z (t+diff*z) Z c C L B η
  have hex : ∀ z : ℕ, z < N → ∃ label, bad z label := by
    intro z hz
    obtain ⟨u, j, hh⟩ := hbad z hz
    exact ⟨(u,j), hh⟩
  obtain ⟨a0, b, label, hb, hbN, hdim, hmono, pNew, hdegree, hlog⟩ :=
    hthin a m P hP hchar p hp d ha hm hd bad hex
  let Dnew := roughNativeKernelNilmanifold D S hS χ hχ hQ V hVr (label.2.val : ℤ)
  let Qbase : (Option κ → ℝ) → Dnew.G := fun x =>
    roughNativeKernelMap D S hS χ hχ hQ V hVr (label.2.val : ℤ) hVS hχV a m P hP hchar
      (Option.elim · (x none) (fun k => ((label.1 k).val : ℝ)+(K : ℝ)*x (some k)))
  let Qnew : (Option κ → ℝ) → Dnew.G := fun x =>
    Qbase (Option.elim · ((a0 : ℝ)+(b : ℝ)*x none) (fun k => x (some k)))
  obtain ⟨hbdiff, hsmooth', hvalues⟩ := rough_smooth_progression_reparametrization
    w N H t diff a0 b Scale hdiff hb hbN hNw hsmooth
    (fun z hz => (hmono z hz).1) hsize hrough
  refine ⟨a0, b, label.1, label.2, Qnew, hb, hbN, hdim, fun _ => rfl,
    ⟨pNew, hdegree, ?_⟩, hbdiff, hsmooth', ?_⟩
  · simpa only [Qnew, Qbase, Option.elim_none, Option.elim_some] using hlog
  · intro z hz
    obtain ⟨he, hlow, hhigh, hr⟩ := hvalues z hz
    refine ⟨(hmono z hz).1, hlow, hhigh, hr, ?_⟩
    have hh := rough_native_bad_index_reparametrize Dnew Qbase a0 b z (t+diff*(a0+b*z))
      Z c C L B η (hmono z hz).2
    simpa only [he] using hh

end Hindman168
'''
Path('Hindman168/RoughNativeBadProgressionThinning.lean').write_text(prefix+header, encoding='utf-8')

text = prefix+header
prefix2 = text[:text.index('theorem rough_native_bad_progression_thinning')]
prefix2 = prefix2.replace('namespace Hindman168', 'import Hindman168.RoughNativeBadFamily\nimport Hindman168.RoughNativeBadProgressionThinning\n\nnamespace Hindman168')
header2 = text[text.index('theorem rough_native_bad_progression_thinning'):text.index('      ∃ (a0 b : ℕ)')]
header2 = header2.replace('theorem rough_native_bad_progression_thinning', 'theorem rough_native_smaller_bad_family')
header2 += '''      ∃ j : Fin K,
        let Dnew := roughNativeKernelNilmanifold D S hS χ hχ hQ V hVr (j.val : ℤ)
        Module.finrank ℝ Dnew.E < Module.finrank ℝ D.E ∧
        RoughNativeBadFamily (κ := κ) Dnew H w Scale Z
          (roughKernelDegreeFactor s*d) c C L B η := by
  obtain ⟨N, hN, hthin⟩ := rough_native_bad_progression_thinning (κ := κ) D S hS χ hχ hQ V hVr hVS hχV K H hH
  refine ⟨N, hN, ?_⟩
  intro a m P hP hchar p hp d ha hm hd w t diff Z Scale c C L B η hdiff hNw hsmooth hsize hrough hbad
  obtain ⟨a0, b, u, j, Qnew, hb, hbN, hdim, hQnew, pNewData, hdiff', hsmooth', hindices⟩ :=
    hthin a m P hP hchar p hp d ha hm hd w t diff Z Scale c C L B η
      hdiff hNw hsmooth hsize hrough hbad
  obtain ⟨pNew, hdeg, hlog⟩ := pNewData
  refine ⟨j, hdim, Qnew, pNew, t+diff*a0, b*diff, hdeg, hlog, hdiff', hsmooth', ?_⟩
  intro z hz
  exact (hindices z hz).2

end Hindman168
'''
Path('Hindman168/RoughNativeSmallerBadFamily.lean').write_text(prefix2+header2, encoding='utf-8')
