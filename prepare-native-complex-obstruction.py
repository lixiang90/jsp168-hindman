from pathlib import Path

source = Path('Hindman168/RoughNativeObstructionBadFamily.lean').read_text(encoding='utf-8')
head = source[:source.index(' := by\n')]
head = 'import Hindman168.RoughNativeObstructionBadFamily\nimport Hindman168.ComplexRealObservable\n\n'+head
head = head.replace('theorem rough_native_obstruction_bad_family',
                    'theorem rough_native_complex_obstruction_bad_family')
head = head.replace('(F : ℕ → (D.G ⧸ D.Γ) → ℝ)', '(F : ℕ → (D.G ⧸ D.Γ) → ℂ)')
head = head.replace('|F z v|', '‖F z v‖')
head = head.replace('η ≤ |FiniteMass.expectation', 'η ≤ ‖FiniteMass.complexExpectation')
head = head.replace('FiniteMass.expectation', 'FiniteMass.complexExpectation')
head = head.replace('(fun x => F z (QuotientGroup.mk (P (Option.elim · (z : ℝ) (fun j => (x j : ℝ))))))|)',
                    '(fun x => F z (QuotientGroup.mk (P (Option.elim · (z : ℝ) (fun j => (x j : ℝ))))))‖)')
head = head.replace('L B (η/2)', 'L B (η/4)')
proof = ''' := by
  intro support family
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ j, MetricSpace ((family j).G ⧸ (family j).Γ) := fun j => (family j).metric
  letI : ∀ j, TopologicalSpace ((family j).G ⧸ (family j).Γ) := fun j =>
    (family j).metric.toUniformSpace.toTopologicalSpace
  obtain ⟨Part, L, hPart, hglobal⟩ := rough_native_obstruction_bad_family D S hS χ hχ hQ V hVr hVS hχV
    K hK hperiod s q he A0 C B hA0 hC hB Lip c (η/2) hc (by positivity) Scale Z hScale hr
  refine ⟨Part, L, hPart, ?_⟩
  intro H hH
  obtain ⟨N, hN, hstage⟩ := hglobal H hH
  refine ⟨N, hN, ?_⟩
  filter_upwards [hstage] with w hw
  intro t diff P0 theta pOb bOb lo hi a0 F hmin hside hlo hhi hLip hbound hP0 htheta
    P hP hchar pLog hpLog hdegree hdiff hsmooth hsize hrough hpOb hbOb hOb hbad
  have hG : ∀ z : ℕ, z < N → ∃ G : (D.G ⧸ D.Γ) → ℝ,
      LipschitzWith Lip G ∧ (∀ v, |G v| ≤ B) ∧
      ‖FiniteMass.complexExpectation
        (FiniteMass.uniformFinsetMass (alignmentBoxClass (lo z) (hi z) (a0 z) (t+diff*z)))
        (fun x => F z (QuotientGroup.mk (P (Option.elim · (z : ℝ) (fun j => (x j : ℝ))))))-
        FiniteMass.complexExpectation
          (FiniteMass.uniformFinsetMass (Fintype.piFinset (fun j => Finset.Ico (lo z j) (hi z j))))
          (fun x => F z (QuotientGroup.mk (P (Option.elim · (z : ℝ) (fun j => (x j : ℝ))))))‖/2 ≤
      |FiniteMass.expectation
        (FiniteMass.uniformFinsetMass (alignmentBoxClass (lo z) (hi z) (a0 z) (t+diff*z)))
        (fun x => G (QuotientGroup.mk (P (Option.elim · (z : ℝ) (fun j => (x j : ℝ))))))-
        FiniteMass.expectation
          (FiniteMass.uniformFinsetMass (Fintype.piFinset (fun j => Finset.Ico (lo z j) (hi z j))))
          (fun x => G (QuotientGroup.mk (P (Option.elim · (z : ℝ) (fun j => (x j : ℝ))))))| := by
    intro z hz
    exact complex_discrepancy_real_observable
      (FiniteMass.uniformFinsetMass (alignmentBoxClass (lo z) (hi z) (a0 z) (t+diff*z)))
      (FiniteMass.uniformFinsetMass (Fintype.piFinset (fun j => Finset.Ico (lo z j) (hi z j))))
      (fun x => QuotientGroup.mk (P (Option.elim · (z : ℝ) (fun j => (x j : ℝ)))))
      (F z) Lip B (hLip z hz) (hbound z hz)
  let G : ℕ → (D.G ⧸ D.Γ) → ℝ := fun z => if hz : z < N then (hG z hz).choose else fun _ => 0
  have hGL : ∀ z, z < N → LipschitzWith Lip (G z) := by
    intro z hz
    simpa only [G, dif_pos hz] using (hG z hz).choose_spec.1
  have hGB : ∀ z, z < N → ∀ v, |G z v| ≤ B := by
    intro z hz
    simpa only [G, dif_pos hz] using (hG z hz).choose_spec.2.1
  have hdisc : ∀ z, z < N →
      η/2 ≤ |FiniteMass.expectation
        (FiniteMass.uniformFinsetMass (alignmentBoxClass (lo z) (hi z) (a0 z) (t+diff*z)))
        (fun x => G z (QuotientGroup.mk (P (Option.elim · (z : ℝ) (fun j => (x j : ℝ))))))-
        FiniteMass.expectation
          (FiniteMass.uniformFinsetMass (Fintype.piFinset (fun j => Finset.Ico (lo z j) (hi z j))))
          (fun x => G z (QuotientGroup.mk (P (Option.elim · (z : ℝ) (fun j => (x j : ℝ))))))| := by
    intro z hz
    have hd := (hG z hz).choose_spec.2.2
    simp only [G, dif_pos hz]
    exact (div_le_div_of_nonneg_right (hbad z hz) (by norm_num : (0 : ℝ) ≤ 2)).trans hd
  have hret := hw t diff P0 theta pOb bOb lo hi a0 G hmin hside hlo hhi hGL hGB hP0 htheta
    P hP hchar pLog hpLog hdegree hdiff hsmooth hsize hrough hpOb hbOb hOb hdisc
  simpa only [div_div, show (2 : ℝ)*2 = 4 by norm_num] using hret

end Hindman168
'''
Path('Hindman168/RoughNativeComplexObstructionBadFamily.lean').write_text(head+proof, encoding='utf-8')
