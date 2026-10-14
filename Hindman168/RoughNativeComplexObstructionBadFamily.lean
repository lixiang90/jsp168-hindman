import Hindman168.RoughNativeObstructionBadFamily
import Hindman168.ComplexRealObservable

import Hindman168.RoughNativePieceDescent
import Hindman168.RoughFiniteCoefficientAssembly

import Hindman168.RoughNativeBadIndex
import Hindman168.RoughNativeModelPieceDescent

import Hindman168.RoughNativeSmallerBadFamily
import Hindman168.RoughNativeModelBadIndex

import Hindman168.RoughNativeModelBadFamily
import Hindman168.RoughNativeDescentBudgets

import Hindman168.RoughNativeAsymptoticModelBadFamily
import Hindman168.RoughNativeJointCoefficientThinning

import Hindman168.RoughNativeIntegerizedBadFamily
import Hindman168.RoughActualAffineObstructionModels

namespace Hindman168
open Filter
open MvPolynomial
open scoped Manifold ContDiff Classical
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_complex_obstruction_bad_family {κ : Type*} [Fintype κ] {step : ℕ}
    (D : NativeNilmanifoldData.{u} step) (S : LieSubalgebra ℝ (GroupLieAlgebra D.I D.G))
    (hS : nativeLatticeRationalSubspace (E := D.E) (I := D.I) D.Γ (nativeLieSubalgebraModel S))
    (χ : D.E →ₗ[ℝ] ℝ)
    (hχ : ∀ x ∈ nativeLieSubalgebraModel S, ∀ y ∈ nativeLieSubalgebraModel S,
      χ (nativeLieAdjointDifferential (I := D.I) (G := D.G) x y) = 0)
    (hQ : ∀ x ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ,
      ∃ r : ℚ, χ x = (r : ℝ))
    (V : D.E) (hVr : V ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ)
    (hVS : V ∈ nativeLieSubalgebraModel S) (hχV : χ V = 1)
    (K : ℕ) (hK : 0 < K)
    (hperiod : nativeLieExponential (I := D.I) (G := D.G) ((K : ℝ) • V) ∈ D.Γ)
    (s : Finset (κ → ℕ)) (q : ℕ) (he : ∀ I ∈ s, 0 < (∑ j, I j) ∧ (∑ j, I j) ≤ q)
    (A0 C B : ℝ) (hA0 : 0 < A0) (hC : 1 ≤ C) (hB : 0 ≤ B) (Lip : NNReal)
    (c η : ℝ) (hc : 0 < c) (hη : 0 < η) (Scale Z : ℕ → ℝ)
    (hScale : Tendsto Scale atTop atTop)
    (hr : ∀ a : ℝ, 0 < a → Tendsto (fun w => Z w/(Scale w)^a) atTop atTop) :
    let support := roughFiniteMultiindices s
    let family := fun j : Fin K => roughNativeKernelNilmanifold D S hS χ hχ hQ V hVr (j.val : ℤ)
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ j, MetricSpace ((family j).G ⧸ (family j).Γ) := fun j => (family j).metric
    letI : ∀ j, TopologicalSpace ((family j).G ⧸ (family j).Γ) := fun j =>
      (family j).metric.toUniformSpace.toTopologicalSpace
    ∃ Part : ℕ, ∃ L : NNReal, ∃ _ : 0 < Part, ∀ H : ℕ, 0 < H →
      ∃ N : ℕ, 0 < N ∧ ∀ᶠ w in atTop, ∀ (t diff : ℕ)
        (P0 : Polynomial ℝ) (theta : (κ →₀ ℕ) → Polynomial ℝ)
        (pOb : (κ → ℕ) → ℕ → ℕ) (bOb : (κ → ℕ) → ℕ → κ → ℕ),
        ∀ (lo hi a0 : ℕ → κ → ℤ) (F : ℕ → (D.G ⧸ D.Γ) → ℂ),
          (∀ z : ℕ, z < N → ∀ j, c*(Z w) ≤ (hi z j : ℝ)-lo z j) →
          (∀ z : ℕ, z < N → ∀ j, (hi z j : ℝ)-lo z j ≤ C*(Z w)) →
          (∀ z : ℕ, z < N → ∀ j, |(lo z j : ℝ)| ≤ C*(Z w)) →
          (∀ z : ℕ, z < N → ∀ j, |(hi z j : ℝ)| ≤ C*(Z w)) →
          (∀ z : ℕ, z < N → LipschitzWith Lip (F z)) →
          (∀ z : ℕ, z < N → ∀ v, ‖F z v‖ ≤ B) →
          P0.natDegree ≤ q → (∀ J ∈ support, (theta J).natDegree+J.sum (fun _ e => e) ≤ q) →
          ∀ (P : (Option κ → ℝ) → D.G)
            (_hP : ∀ x, P x ∈ nativeLieSubalgebraSubgroup (E := D.E) S)
            (_hchar : ∀ x, nativeLieLogarithmCharacter (I := D.I) (G := D.G) χ (P x) =
              eval x (roughSpatialJointPolynomial support P0 theta)),
          ∀ (pLog : RoughVectorMvPolynomial (Option κ) D.E)
            (_hpLog : ∀ x, roughVectorMvEval pLog x = nativeLieGlobalLogarithm (E := D.E) (I := D.I) (P x))
            (_hdegree : RoughVectorMvDegreeLE pLog q),
          0 < diff →
          (∀ prime : ℕ, prime.Prime → prime ∣ diff → prime ≤ w) →
          (∀ z : ℕ, z < N → (Scale w) ≤ (t+diff*z : ℕ) ∧ (t+diff*z : ℕ) < 2*(Scale w)) →
          (∀ z : ℕ, z < N → (primorial w).Coprime (t+diff*z)) →
          (∀ I ∈ s, ∀ z : ℕ, z < N → pOb I z = 1 ∨ pOb I z = t+diff*z) →
          (∀ I ∈ s, ∀ z : ℕ, z < N → ∀ j, bOb I z j ≤ pOb I z) →
          (∀ I ∈ s, ∀ z : ℕ, z < N →
            ‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm I)
              (roughMvAffineSubstitution (fun j => (bOb I z j : ℝ)) (fun _ => (pOb I z : ℝ))
                (roughSpatialFixedPolynomial support (P0.eval (z : ℝ))
                  (fun J => (theta J).eval (z : ℝ)))) : ℝ) : UnitAddCircle)‖ ≤
              A0*((pOb I z : ℝ)/(Z w))^(∑ j, I j)) →
          (∀ z : ℕ, z < N →
            η ≤ ‖FiniteMass.complexExpectation (FiniteMass.uniformFinsetMass (alignmentBoxClass (lo z) (hi z) (a0 z) (t+diff*z)))
              (fun x => F z (QuotientGroup.mk (P (Option.elim · (z : ℝ) (fun j => (x j : ℝ))))))-
            FiniteMass.complexExpectation (FiniteMass.uniformFinsetMass
              (Fintype.piFinset (fun j => Finset.Ico (lo z j) (hi z j))))
              (fun x => F z (QuotientGroup.mk (P (Option.elim · (z : ℝ) (fun j => (x j : ℝ))))))‖) →
          ∃ j : Fin K, Module.finrank ℝ (family j).E < Module.finrank ℝ D.E ∧
            RoughNativeBadFamily (κ := κ) (family j) H w (Scale w) ((Z w)/K)
              (roughKernelDegreeFactor step*q) (c/(4*Part)) (max (4*C/Part) (C+1)) L B (η/4) := by
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
