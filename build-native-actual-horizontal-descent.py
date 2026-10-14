from pathlib import Path

src=Path('Hindman168/NativeOriginalHorizontalKernelDescent.lean').read_text(encoding='utf-8')
start=src.index('theorem native_original_horizontal_kernel_descent')
stop=src.index(' := by',start)
header=src[start:stop].replace('native_original_horizontal_kernel_descent','native_original_actual_horizontal_kernel_descent')
header=header.replace('    let s := roughSpatialDegreeIndices κ q\n','')
begin=header.index('∀ (t diff : ℕ)')
end=header.index('          ∃ j : Fin K,',begin)
header=header[:begin]+'''∀ (P : (Option κ → ℝ) → D.G)
        (pLog : RoughVectorMvPolynomial (Option κ) D.E),
        RoughVectorMvDegreeLE pLog q →
        (∀ x, roughVectorMvEval pLog x = nativeLieGlobalLogarithm (E := D.E) (I := D.I) (P x)) →
        ∀ t diff : ℕ, 0 < diff →
        (∀ prime : ℕ, prime.Prime → prime ∣ diff → prime ≤ w) →
        (∀ z : ℕ, z < N → Scale w ≤ (t+diff*z : ℕ) ∧ (t+diff*z : ℕ) < 2*Scale w) →
        (∀ z : ℕ, z < N → (primorial w).Coprime (t+diff*z)) →
        (∀ z : ℕ, z < N → RoughNativeBadIndex D P z (t+diff*z) (Z w) c C Lip B η) →
        (∀ z : ℕ, z < N → ∃ pOb : ℕ, ∃ bOb : κ → ℕ,
          (pOb=1 ∨ pOb=t+diff*z) ∧ (∀ j, bOb j ≤ pOb) ∧
          ∀ I : κ → ℕ, 0 < (∑ j, I j) →
            ‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm I)
              (roughMvAffineSubstitution (fun j => (bOb j : ℝ)) (fun _ => (pOb : ℝ))
                (roughScalarSpatialProjection χ pLog (z : ℝ))) : ℝ) : UnitAddCircle)‖ ≤
              A0*((pOb : ℝ)/(Z w))^(∑ j, I j)) →
'''+header[end:]
result='''import Hindman168.NativeOriginalHorizontalKernelDescent
import Hindman168.RoughNativeRealBadIndexComplex

/-! ACTUAL real original bad samples and ALL affine original rows now
invoke true original horizontal kernel descent. Sample/observable/row-model
premises of the older descent are PRODUCED, not supplied by an oracle. -/
namespace Hindman168
open Filter MvPolynomial
open scoped Manifold ContDiff BigOperators Classical
universe u
attribute [local instance] lieGroup_smooth_min_three

'''+header+''' := by
  let S : LieSubalgebra ℝ (GroupLieAlgebra D.I D.G) := ⊤
  let hS := native_original_top_lie_rational D
  let hχ := native_original_horizontal_top_bracket D χ hHor
  let hΓ := hHor.2.2
  let hQ := rough_native_integral_character_rational_on_span (I := D.I) D.Γ χ hΓ
  obtain ⟨V,hVr,hVS,hχV,K,hK,hPeriod,Part,L,hPart,hDesc⟩ :=
    native_original_horizontal_kernel_descent (κ := κ) D χ hHor q A0 C B hA0 hC hB Lip
      c η hc hη Scale Z hScale hr
  refine ⟨V,hVr,hVS,hχV,K,hK,hPeriod,Part,L,hPart,?_⟩
  intro H hH
  obtain ⟨N,hN,hStage⟩ := hDesc H hH
  refine ⟨N,hN,?_⟩
  filter_upwards [hStage] with w hw
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro P pLog hDegree hLog t diff hDiff hSmooth hSize hRough hBad hRows
  have hSamples : ∀ z : ℕ, ∃ (lo hi a0 : κ → ℤ) (F : (D.G ⧸ D.Γ) → ℂ), z < N →
      LipschitzWith Lip F ∧ (∀ v, ‖F v‖ ≤ B) ∧
      (∀ j, c*(Z w) ≤ (hi j : ℝ)-lo j ∧ (hi j : ℝ)-lo j ≤ C*(Z w) ∧
        |(lo j : ℝ)| ≤ C*(Z w) ∧ |(hi j : ℝ)| ≤ C*(Z w)) ∧
      η ≤ ‖FiniteMass.complexExpectation (FiniteMass.uniformFinsetMass (alignmentBoxClass lo hi a0 (t+diff*z)))
        (fun x => F (QuotientGroup.mk (P (fun i => i.elim (z : ℝ) (fun j => (x j : ℝ))))))-
        FiniteMass.complexExpectation (FiniteMass.uniformFinsetMass
          (Fintype.piFinset (fun j => Finset.Ico (lo j) (hi j))))
        (fun x => F (QuotientGroup.mk (P (fun i => i.elim (z : ℝ) (fun j => (x j : ℝ))))))‖ := by
    intro z
    by_cases hz : z < N
    · obtain ⟨lo,hi,a0,F,hL,hB,hBox,_hStep,_hFull,hGap⟩ :=
        rough_native_real_bad_index_complex D P z (t+diff*z) (Z w) c C Lip B η (hBad z hz)
      exact ⟨lo,hi,a0,F,fun _ => ⟨hL,hB,hBox,hGap.le⟩⟩
    · exact ⟨fun _ => 0,fun _ => 0,fun _ => 0,fun _ => 0,fun h => (hz h).elim⟩
  choose lo hi a0 F hSample using hSamples
  have hPackets : ∀ z : ℕ, ∃ (pOb : ℕ) (bOb : κ → ℕ), z < N →
      (pOb=1 ∨ pOb=t+diff*z) ∧ (∀ j, bOb j ≤ pOb) ∧
      ∀ I : κ → ℕ, 0 < (∑ j, I j) →
        ‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm I)
          (roughMvAffineSubstitution (fun j => (bOb j : ℝ)) (fun _ => (pOb : ℝ))
            (roughScalarSpatialProjection χ pLog (z : ℝ))) : ℝ) : UnitAddCircle)‖ ≤
          A0*((pOb : ℝ)/(Z w))^(∑ j, I j) := by
    intro z
    by_cases hz : z < N
    · obtain ⟨pp,bb,hPacket⟩ := hRows z hz
      exact ⟨pp,bb,fun _ => hPacket⟩
    · exact ⟨1,fun _ => 0,fun h => (hz h).elim⟩
  choose pp bb hPacket using hPackets
  exact hw t diff (fun _ z => pp z) (fun _ z => bb z) lo hi a0 F
    (fun z hz j => ((hSample z hz).2.2.1 j).1)
    (fun z hz j => ((hSample z hz).2.2.1 j).2.1)
    (fun z hz j => ((hSample z hz).2.2.1 j).2.2.1)
    (fun z hz j => ((hSample z hz).2.2.1 j).2.2.2)
    (fun z hz => (hSample z hz).1) (fun z hz => (hSample z hz).2.1)
    P (fun x => (nativeLieSubalgebraSubgroup_mem_globalLogarithm_iff (E := D.E) S (P x)).mpr
      (Submodule.mem_top : nativeLieGlobalLogarithm (E := D.E) (I := D.I) (P x) ∈ (⊤ : Submodule ℝ D.E)))
    pLog hLog hDegree hDiff hSmooth hSize hRough
    (fun _ _ z hz => (hPacket z hz).1) (fun _ _ z hz => (hPacket z hz).2.1)
    (fun I hI z hz => (hPacket z hz).2.2 I ((rough_spatial_degree_indices_mem q I).mp hI).1)
    (fun z hz => (hSample z hz).2.2.2)

end Hindman168
'''
Path('Hindman168/NativeOriginalActualHorizontalKernelDescent.lean').write_text(result,encoding='utf-8')
