import Hindman168.RoughNativePieceDescent
import Hindman168.RoughFiniteCoefficientAssembly

import Hindman168.RoughNativeBadIndex
import Hindman168.RoughNativeModelPieceDescent

import Hindman168.RoughNativeSmallerBadFamily
import Hindman168.RoughNativeModelBadIndex

import Hindman168.RoughNativeModelBadFamily
import Hindman168.RoughNativeDescentBudgets

namespace Hindman168
open Filter
open MvPolynomial
open scoped Manifold ContDiff Classical
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_asymptotic_model_bad_family {κ : Type*} [Fintype κ] {step : ℕ}
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
    (support : Finset (κ →₀ ℕ)) (d : ℕ) (hd : ∀ J ∈ support, (∑ j, J j) ≤ d)
    (A C B : ℝ) (hA : 0 ≤ A) (hC : 1 ≤ C) (hB : 0 ≤ B) (Lip : NNReal)
    (c η : ℝ) (hc : 0 < c) (hη : 0 < η) (Scale Z : ℕ → ℝ)
    (hg : PowerDominates atTop Z Scale) (hScale : ∀ᶠ w in atTop, 1 ≤ Scale w)
    (hZ : ∀ᶠ w in atTop, 0 ≤ Z w) :
    let family := fun j : Fin K => roughNativeKernelNilmanifold D S hS χ hχ hQ V hVr (j.val : ℤ)
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ j, MetricSpace ((family j).G ⧸ (family j).Γ) := fun j => (family j).metric
    letI : ∀ j, TopologicalSpace ((family j).G ⧸ (family j).Γ) := fun j =>
      (family j).metric.toUniformSpace.toTopologicalSpace
    ∃ Part : ℕ, ∃ L : NNReal, ∃ _ : 0 < Part, ∀ H : ℕ, 0 < H →
      ∃ N : ℕ, 0 < N ∧ ∀ᶠ w in atTop, ∀ (q t diff : ℕ)
        (P0 : Polynomial ℝ) (theta : (κ →₀ ℕ) → Polynomial ℝ)
        (M0 : Polynomial ℚ) (M : (κ →₀ ℕ) → Polynomial ℚ),
        (∀ J ∈ support, RoughCoefficientModel w N q (∑ j, J j) (Z w) A (theta J) (M J)) →
        (∀ z : ℕ, z < N → ∃ n : ℤ, M0.eval (z : ℚ) = (n : ℚ)) →
        (∀ z : ℕ, z < N →
          0 ≤ P0.eval (z : ℝ)-((M0.eval (z : ℚ) : ℚ) : ℝ) ∧
          P0.eval (z : ℝ)-((M0.eval (z : ℚ) : ℚ) : ℝ) < 1) →
        ∀ (lo hi a0 : ℕ → κ → ℤ) (F : ℕ → (D.G ⧸ D.Γ) → ℝ),
          (∀ z : ℕ, z < N → ∀ j, c*(Z w) ≤ (hi z j : ℝ)-lo z j) →
          (∀ z : ℕ, z < N → ∀ j, (hi z j : ℝ)-lo z j ≤ C*(Z w)) →
          (∀ z : ℕ, z < N → ∀ j, |(lo z j : ℝ)| ≤ C*(Z w)) →
          (∀ z : ℕ, z < N → ∀ j, |(hi z j : ℝ)| ≤ C*(Z w)) →
          (∀ z : ℕ, z < N → LipschitzWith Lip (F z)) →
          (∀ z : ℕ, z < N → ∀ v, |F z v| ≤ B) →
          M0.natDegree ≤ q → (∀ J ∈ support, (∑ j, J j) ≤ q) →
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
          (∀ z : ℕ, z < N →
            η ≤ |FiniteMass.expectation (FiniteMass.uniformFinsetMass (alignmentBoxClass (lo z) (hi z) (a0 z) (t+diff*z)))
              (fun x => F z (QuotientGroup.mk (P (Option.elim · (z : ℝ) (fun j => (x j : ℝ))))))-
            FiniteMass.expectation (FiniteMass.uniformFinsetMass
              (Fintype.piFinset (fun j => Finset.Ico (lo z j) (hi z j))))
              (fun x => F z (QuotientGroup.mk (P (Option.elim · (z : ℝ) (fun j => (x j : ℝ))))))|) →
          ∃ j : Fin K, Module.finrank ℝ (family j).E < Module.finrank ℝ D.E ∧
            RoughNativeBadFamily (κ := κ) (family j) H w (Scale w) ((Z w)/K)
              (roughKernelDegreeFactor step*q) (c/(4*Part)) (max (4*C/Part) (C+1)) L B (η/2) := by
  intro family
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ j, MetricSpace ((family j).G ⧸ (family j).Γ) := fun j => (family j).metric
  letI : ∀ j, TopologicalSpace ((family j).G ⧸ (family j).Γ) := fun j =>
    (family j).metric.toUniformSpace.toTopologicalSpace
  obtain ⟨Part, L, hPart, hglobal⟩ := rough_native_model_bad_family
    (εfreeze := η/32) (εapprox := η/32) D S hS χ hχ hQ V hVr hVS hχV
    K hK hperiod support d hd A C B hA hC hB Lip (by positivity) (by positivity)
  refine ⟨Part, L, hPart, ?_⟩
  intro H hH
  obtain ⟨N, hN, hstage⟩ := hglobal H hH
  refine ⟨N, hN, ?_⟩
  have hbud := rough_native_descent_budgets (κ := κ) hg hScale hZ Part K N hPart hK c B η hc hB hη
  filter_upwards [hbud] with w hw
  intro q t diff P0 theta M0 M hmodels h0 hconst lo hi a0 F hmin hside hlo hhi
    hLip hbound hM0 he hP0 htheta P hP hchar pLog hpLog hdegree hdiff hsmooth hsize hrough hbad
  have hb := fun z (hz : z < N) => hw.2.2.2 (t+diff*z) (hsize z hz).1 (hsize z hz).2 (hrough z hz)
  have hbox := fun z (hz : z < N) => (hb z hz).2.2.2.2 (lo z) (hi z) (hmin z hz)
  exact hstage w q t diff (Z w) (Scale w) c (η/2) η P0 theta M0 M hmodels hw.2.1 hw.2.2.1
    h0 hconst lo hi a0 F (fun z hz => (hbox z hz).1) (fun z hz => (hbox z hz).2)
    hside hlo hhi hLip hbound hM0 he hP0 htheta P hP hchar pLog hpLog hdegree
    hdiff hw.1 hsmooth hsize hrough (fun z hz => ⟨(hb z hz).1, (hb z hz).2.1⟩)
    hc (fun z hz => (hb z hz).2.2.1) hmin (fun z hz => (hb z hz).2.2.2.1) hbad

end Hindman168
