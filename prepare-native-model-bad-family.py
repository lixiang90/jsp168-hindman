from pathlib import Path

old = Path('Hindman168/RoughNativeModelBadIndex.lean').read_text(encoding='utf-8')
prefix = old[:old.index('theorem rough_native_model_bad_index')]
prefix = prefix.replace('namespace Hindman168', 'import Hindman168.RoughNativeSmallerBadFamily\nimport Hindman168.RoughNativeModelBadIndex\n\nnamespace Hindman168')
header = old[old.index('theorem rough_native_model_bad_index'):old.index('    ∃ N : ℕ')]
header = header.replace('theorem rough_native_model_bad_index', 'theorem rough_native_model_bad_family')
header += '''    ∃ Part : ℕ, ∃ L : NNReal, ∃ _ : 0 < Part, ∀ H : ℕ, 0 < H →
      ∃ N : ℕ, 0 < N ∧ ∀ (w q t diff : ℕ) (Z Scale c θ η : ℝ)
        (P0 : Polynomial ℝ) (theta : (κ →₀ ℕ) → Polynomial ℝ)
        (M0 : Polynomial ℚ) (M : (κ →₀ ℕ) → Polynomial ℚ),
        (∀ J ∈ support, RoughCoefficientModel w N q (∑ j, J j) Z A (theta J) (M J)) →
        0 < Z → 1 ≤ Z/K →
        (∀ z : ℕ, z < N → ∃ n : ℤ, M0.eval (z : ℚ) = (n : ℚ)) →
        (∀ z : ℕ, z < N →
          0 ≤ P0.eval (z : ℝ)-((M0.eval (z : ℚ) : ℚ) : ℝ) ∧
          P0.eval (z : ℝ)-((M0.eval (z : ℚ) : ℚ) : ℝ) < 1) →
        ∀ (lo hi a0 : ℕ → κ → ℤ) (F : ℕ → (D.G ⧸ D.Γ) → ℝ),
          (∀ z : ℕ, z < N → ∀ j, 2*(Part : ℤ) ≤ hi z j-lo z j) →
          (∀ z : ℕ, z < N → ∀ j, (2*Part*K : ℤ) ≤ hi z j-lo z j) →
          (∀ z : ℕ, z < N → ∀ j, (hi z j : ℝ)-lo z j ≤ C*Z) →
          (∀ z : ℕ, z < N → ∀ j, |(lo z j : ℝ)| ≤ C*Z) →
          (∀ z : ℕ, z < N → ∀ j, |(hi z j : ℝ)| ≤ C*Z) →
          (∀ z : ℕ, z < N → LipschitzWith Lip (F z)) →
          (∀ z : ℕ, z < N → ∀ v, |F z v| ≤ B) →
          M0.natDegree ≤ q → (∀ J ∈ support, (∑ j, J j) ≤ q) →
          P0.natDegree ≤ q → (∀ J ∈ support, (theta J).natDegree+J.sum (fun _ e => e) ≤ q) →
          ∀ (P : (Option κ → ℝ) → D.G)
            (hP : ∀ x, P x ∈ nativeLieSubalgebraSubgroup (E := D.E) S)
            (hchar : ∀ x, nativeLieLogarithmCharacter (I := D.I) (G := D.G) χ (P x) =
              eval x (roughSpatialJointPolynomial support P0 theta)),
          ∀ (pLog : RoughVectorMvPolynomial (Option κ) D.E)
            (_hpLog : ∀ x, roughVectorMvEval pLog x = nativeLieGlobalLogarithm (E := D.E) (I := D.I) (P x))
            (_hdegree : RoughVectorMvDegreeLE pLog q),
          0 < diff → N ≤ w →
          (∀ prime : ℕ, prime.Prime → prime ∣ diff → prime ≤ w) →
          (∀ z : ℕ, z < N → Scale ≤ (t+diff*z : ℕ) ∧ (t+diff*z : ℕ) < 2*Scale) →
          (∀ z : ℕ, z < N → (primorial w).Coprime (t+diff*z)) →
          (∀ z : ℕ, z < N → 0 < t+diff*z ∧ (t+diff*z).Coprime K) →
          0 < c → (∀ z : ℕ, z < N → 2*((t+diff*z : ℕ) : ℝ) ≤ c*Z) →
          (∀ z : ℕ, z < N → ∀ j, c*Z ≤ (hi z j : ℝ)-lo z j) →
          (∀ z : ℕ, z < N →
            θ+B*(((Part ^ Fintype.card κ*K ^ Fintype.card κ : ℕ) : ℝ)*
              Fintype.card κ*(5*((t+diff*z : ℕ) : ℝ)/(c*Z)))+2*(εfreeze+εapprox) < η) →
          (∀ z : ℕ, z < N →
            η ≤ |FiniteMass.expectation (FiniteMass.uniformFinsetMass (alignmentBoxClass (lo z) (hi z) (a0 z) (t+diff*z)))
              (fun x => F z (QuotientGroup.mk (P (Option.elim · (z : ℝ) (fun j => (x j : ℝ))))))-
            FiniteMass.expectation (FiniteMass.uniformFinsetMass
              (Fintype.piFinset (fun j => Finset.Ico (lo z j) (hi z j))))
              (fun x => F z (QuotientGroup.mk (P (Option.elim · (z : ℝ) (fun j => (x j : ℝ))))))|) →
          ∃ j : Fin K, Module.finrank ℝ (family j).E < Module.finrank ℝ D.E ∧
            RoughNativeBadFamily (κ := κ) (family j) H w Scale (Z/K)
              (roughKernelDegreeFactor step*q) (c/(4*Part)) (max (4*C/Part) (C+1)) L B θ := by
  intro family
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ j, MetricSpace ((family j).G ⧸ (family j).Γ) := fun j => (family j).metric
  letI : ∀ j, TopologicalSpace ((family j).G ⧸ (family j).Γ) := fun j =>
    (family j).metric.toUniformSpace.toTopologicalSpace
  obtain ⟨Part, L, hPart, hindex⟩ := rough_native_model_bad_index D S hS χ hχ hQ V hVr hVS hχV
    K hK hperiod support d hd A C B hA hC hB Lip hεf hεa
  refine ⟨Part, L, hPart, ?_⟩
  intro H hH
  obtain ⟨N, hN, hthin⟩ := rough_native_smaller_bad_family (κ := κ) D S hS χ hχ hQ V hVr hVS hχV K H hH
  refine ⟨N, hN, ?_⟩
  intro w q t diff Z Scale c θ η P0 theta M0 M hmodels hZ hscale h0 hconst lo hi a0 F
    hlen hpiece hside hlo hhi hLip hbound hM0 he hP0 htheta P hP hchar pLog hpLog hdegree
    hdiff hNw hsmooth hsize hrough hcop hc htZ hmin hgap hbad
  let m := map (Rat.castHom ℝ) (roughSpatialJointPolynomial support M0 M)
  let a := roughSpatialJointPolynomial support P0 theta-m
  have hm : m.totalDegree ≤ q := rough_models_joint_real_degree support theta M0 M hmodels hM0 he
  have hn : (-m).totalDegree ≤ q := by simpa only [totalDegree_neg] using hm
  have ha : a.totalDegree ≤ q := by
    dsimp only [a]
    rw [sub_eq_add_neg]
    exact (totalDegree_add _ _).trans
      (max_le (roughSpatialJointPolynomial_degree support P0 theta q hP0 htheta) hn)
  have hsplit : ∀ x, nativeLieLogarithmCharacter (I := D.I) (G := D.G) χ (P x) = eval x a+eval x m := by
    intro x
    rw [hchar x]
    dsimp only [a]
    rw [map_sub, sub_add_cancel]
  apply hthin a m P hP hsplit pLog hpLog q ha hm hdegree w t diff (Z/K) Scale
    (c/(4*Part)) (max (4*C/Part) (C+1)) L B θ hdiff hNw hsmooth hsize hrough
  intro z hz
  obtain ⟨u, j, _, _, hb⟩ := hindex w N q z Z P0 theta M0 M hmodels hz hZ (h0 z hz) (hconst z hz)
    (lo z) (hi z) (hlen z hz) (hside z hz) (hlo z hz) (hhi z hz) (F z) (hLip z hz) (hbound z hz)
    hM0 he hP0 htheta P hP hchar pLog hpLog hdegree (a0 z) (t+diff*z)
    (hcop z hz).1 (hcop z hz).2 c θ η hc (htZ z hz) (hmin z hz) (hpiece z hz) hscale (hgap z hz) (hbad z hz)
  exact ⟨u, j, hb⟩

end Hindman168
'''
signature, proof = header.split(' := by\n  intro family', 1)
signature = signature.replace('(hP :', '(_hP :').replace('(hchar :', '(_hchar :')
Path('Hindman168/RoughNativeModelBadFamily.lean').write_text(prefix+signature+' := by\n  intro family'+proof, encoding='utf-8')
