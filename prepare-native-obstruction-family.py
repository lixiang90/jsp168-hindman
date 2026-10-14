from pathlib import Path

src = Path('Hindman168/RoughNativeIntegerizedBadFamily.lean').read_text(encoding='utf-8')
prefix = src[:src.index('theorem rough_native_integerized_bad_family')]
prefix = prefix.replace('namespace Hindman168', 'import Hindman168.RoughNativeIntegerizedBadFamily\nimport Hindman168.RoughActualAffineObstructionModels\n\nnamespace Hindman168')
head = src[src.index('theorem rough_native_integerized_bad_family'):src.index(' := by\n  intro family')]
head = head.replace('theorem rough_native_integerized_bad_family', 'theorem rough_native_obstruction_bad_family')
head = head.replace('    (support : Finset (κ →₀ ℕ)) (d : ℕ) (hd : ∀ J ∈ support, (∑ j, J j) ≤ d)',
    '    (s : Finset (κ → ℕ)) (q : ℕ) (he : ∀ I ∈ s, 0 < (∑ j, I j) ∧ (∑ j, I j) ≤ q)')
head = head.replace('    (A C B : ℝ) (hA : 0 ≤ A)', '    (A0 C B : ℝ) (hA0 : 0 < A0)')
head = head.replace('    (q : ℕ) (c η : ℝ)', '    (c η : ℝ)')
head = head.replace('    (hg : PowerDominates atTop Z Scale) (hScale : ∀ᶠ w in atTop, 1 ≤ Scale w)\n    (hZ : ∀ᶠ w in atTop, 0 ≤ Z w) :', '''    (hScale : Tendsto Scale atTop atTop)
    (hr : ∀ a : ℝ, 0 < a → Tendsto (fun w => Z w/(Scale w)^a) atTop atTop) :
    let support := roughFiniteMultiindices s''')
head = head.replace('        (M : (κ →₀ ℕ) → Polynomial ℚ),\n        (∀ J ∈ support, RoughCoefficientModel w N q (∑ j, J j) (Z w) A (theta J) (M J)) →', '''        (pOb : (κ → ℕ) → ℕ → ℕ) (bOb : (κ → ℕ) → ℕ → κ → ℕ),''')
head = head.replace('          (∀ J ∈ support, (∑ j, J j) ≤ q) →\n', '')
start = head.index('          (∀ z : ℕ, z < N →\n            η ≤ |')
ob = '''          (∀ I ∈ s, ∀ z : ℕ, z < N → pOb I z = 1 ∨ pOb I z = t+diff*z) →
          (∀ I ∈ s, ∀ z : ℕ, z < N → ∀ j, bOb I z j ≤ pOb I z) →
          (∀ I ∈ s, ∀ z : ℕ, z < N →
            ‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm I)
              (roughMvAffineSubstitution (fun j => (bOb I z j : ℝ)) (fun _ => (pOb I z : ℝ))
                (roughSpatialFixedPolynomial support (P0.eval (z : ℝ))
                  (fun J => (theta J).eval (z : ℝ)))) : ℝ) : UnitAddCircle)‖ ≤
              A0*((pOb I z : ℝ)/(Z w))^(∑ j, I j)) →
'''
head = head[:start]+ob+head[start:]
proof = ''' := by
  intro support family
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ j, MetricSpace ((family j).G ⧸ (family j).Γ) := fun j => (family j).metric
  letI : ∀ j, TopologicalSpace ((family j).G ⧸ (family j).Γ) := fun j =>
    (family j).metric.toUniformSpace.toTopologicalSpace
  have hn : ∀ n : ℕ, 0 < n → Tendsto (fun w => Z w/(Scale w)^n) atTop atTop := by
    intro n hn
    simpa only [Real.rpow_natCast] using hr (n : ℝ) (by exact_mod_cast hn)
  obtain ⟨hg, hScale1, hZpos⟩ := rough_interpolation_growth_from_ratios hScale hn
  let A := roughDescentConstant q s.card A0 (2^q) q
  have hA : 0 < A := roughDescentConstant_pos q s.card hA0 (by positivity) q
  have he' : ∀ J ∈ support, (∑ j, J j) ≤ q :=
    roughFiniteMultiindices_degree s q (fun I hI => (he I hI).2)
  obtain ⟨Part, L, hPart, hglobal⟩ := rough_native_integerized_bad_family D S hS χ hχ hQ V hVr hVS hχV
    K hK hperiod support q he' A C B hA.le hC hB Lip q c η hc hη Scale Z hg hScale1
    (hZpos.mono fun _ h => h.le)
  refine ⟨Part, L, hPart, ?_⟩
  intro H hH
  obtain ⟨Len, hLen, hstage⟩ := hglobal H hH
  let N := max Len (2*q+2)
  have hN : 0 < N := hLen.trans_le (le_max_left _ _)
  have hLenN : Len ≤ N := le_max_left _ _
  have hobs := rough_actual_affine_obstruction_models tendsto_id hScale hr s q N
    (le_max_right _ _) he A0 hA0
  refine ⟨N, hN, ?_⟩
  filter_upwards [hstage, hobs] with w hw hob
  intro t diff P0 theta pOb bOb lo hi a0 F hmin hside hlo hhi hLip hbound hP0 htheta
    P hP hchar pLog hpLog hdegree hdiff hsmooth hsize hrough hpOb hbOb hOb hbad
  have hprod : ∀ I ∈ s,
      ((Polynomial.C (t : ℝ)+Polynomial.C (diff : ℝ)*Polynomial.X)^(∑ j, I j)*
        theta (Finsupp.equivFunOnFinite.symm I)).natDegree ≤ q := by
    intro I hI
    apply rough_linear_step_weighted_degree
    have hh := htheta (Finsupp.equivFunOnFinite.symm I) (Finset.mem_map.mpr ⟨I, hI, rfl⟩)
    have heq : (Finsupp.equivFunOnFinite.symm I).sum (fun _ e => e) = ∑ j, I j :=
      Finsupp.sum_fintype _ _ (fun _ => rfl)
    rwa [heq] at hh
  obtain ⟨M, hM⟩ := hob t diff (fun I => theta (Finsupp.equivFunOnFinite.symm I)) P0 pOb bOb
    hdiff hsmooth hsize hrough hprod hpOb hbOb (by
      intro I hI z hz
      simpa only [Finsupp.equivFunOnFinite_symm_coe] using hOb I hI z hz)
  have hmodels : ∀ J ∈ support, RoughCoefficientModel w Len q (∑ j, J j) (Z w) A (theta J) (M J) := by
    intro J hJ
    obtain ⟨I, hI, rfl⟩ := Finset.mem_map.mp hJ
    have hh := hM I hI
    refine ⟨hh.1, hh.2.1, ?_⟩
    intro z hz
    exact hh.2.2 z (hz.trans_le hLenN)
  exact hw t diff P0 theta (fun J => M J) hmodels lo hi a0 F
    (fun z hz => hmin z (hz.trans_le hLenN)) (fun z hz => hside z (hz.trans_le hLenN))
    (fun z hz => hlo z (hz.trans_le hLenN)) (fun z hz => hhi z (hz.trans_le hLenN))
    (fun z hz => hLip z (hz.trans_le hLenN)) (fun z hz => hbound z (hz.trans_le hLenN))
    he' hP0 htheta P hP hchar pLog hpLog hdegree hdiff hsmooth
    (fun z hz => hsize z (hz.trans_le hLenN)) (fun z hz => hrough z (hz.trans_le hLenN))
    (fun z hz => hbad z (hz.trans_le hLenN))

end Hindman168
'''
Path('Hindman168/RoughNativeObstructionBadFamily.lean').write_text(prefix+head+proof, encoding='utf-8')
