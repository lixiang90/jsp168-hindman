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

namespace Hindman168
open Filter
open MvPolynomial
open scoped Manifold ContDiff Classical
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_integerized_bad_family {κ : Type*} [Fintype κ] {step : ℕ}
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
    (q : ℕ) (c η : ℝ) (hc : 0 < c) (hη : 0 < η) (Scale Z : ℕ → ℝ)
    (hg : PowerDominates atTop Z Scale) (hScale : ∀ᶠ w in atTop, 1 ≤ Scale w)
    (hZ : ∀ᶠ w in atTop, 0 ≤ Z w) :
    let family := fun j : Fin K => roughNativeKernelNilmanifold D S hS χ hχ hQ V hVr (j.val : ℤ)
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ j, MetricSpace ((family j).G ⧸ (family j).Γ) := fun j => (family j).metric
    letI : ∀ j, TopologicalSpace ((family j).G ⧸ (family j).Γ) := fun j =>
      (family j).metric.toUniformSpace.toTopologicalSpace
    ∃ Part : ℕ, ∃ L : NNReal, ∃ _ : 0 < Part, ∀ H : ℕ, 0 < H →
      ∃ N : ℕ, 0 < N ∧ ∀ᶠ w in atTop, ∀ (t diff : ℕ)
        (P0 : Polynomial ℝ) (theta : (κ →₀ ℕ) → Polynomial ℝ)
        (M : (κ →₀ ℕ) → Polynomial ℚ),
        (∀ J ∈ support, RoughCoefficientModel w N q (∑ j, J j) (Z w) A (theta J) (M J)) →
        ∀ (lo hi a0 : ℕ → κ → ℤ) (F : ℕ → (D.G ⧸ D.Γ) → ℝ),
          (∀ z : ℕ, z < N → ∀ j, c*(Z w) ≤ (hi z j : ℝ)-lo z j) →
          (∀ z : ℕ, z < N → ∀ j, (hi z j : ℝ)-lo z j ≤ C*(Z w)) →
          (∀ z : ℕ, z < N → ∀ j, |(lo z j : ℝ)| ≤ C*(Z w)) →
          (∀ z : ℕ, z < N → ∀ j, |(hi z j : ℝ)| ≤ C*(Z w)) →
          (∀ z : ℕ, z < N → LipschitzWith Lip (F z)) →
          (∀ z : ℕ, z < N → ∀ v, |F z v| ≤ B) →
          (∀ J ∈ support, (∑ j, J j) ≤ q) →
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
  obtain ⟨Part, L, hPart, hglobal⟩ := rough_native_asymptotic_model_bad_family D S hS χ hχ hQ V hVr hVS hχV
    K hK hperiod support d hd A C B hA hC hB Lip c η hc hη Scale Z hg hScale hZ
  refine ⟨Part, L, hPart, ?_⟩
  intro H hH
  obtain ⟨Len, hLen, hstage⟩ := hglobal H hH
  obtain ⟨N, hN, hthin⟩ := rough_native_joint_coefficient_thinning D support q Len hLen
  refine ⟨N, hN, ?_⟩
  filter_upwards [hstage, eventually_ge_atTop N] with w hw hNw
  intro t diff P0 theta M hmodels lo hi a0 F hmin hside hlo hhi hLip hbound he hP0 htheta
    P hP hchar pLog hpLog hdegree hdiff hsmooth hsize hrough hbad
  obtain ⟨a, b, M0, Pnew, pNew, hb, hbN, hindex, hM0, hden, hval, hmodels', hP0', htheta',
    hformula, hmem, hchar', hdegree', hlog'⟩ :=
    hthin w (Z w) A P0 theta M (nativeLieSubalgebraSubgroup (E := D.E) S)
      (nativeLieLogarithmCharacter (I := D.I) (G := D.G) χ) P hNw hP0 htheta hmodels hP hchar pLog hpLog hdegree
  obtain ⟨hdiff', hsmooth', hsize', hrough'⟩ := rough_progression_reparametrize hdiff hb (hbN.trans hNw)
    hsmooth hsize hrough hindex
  refine hw q (t+diff*a) (diff*b)
    (P0.comp (Polynomial.C (a : ℝ)+Polynomial.C (b : ℝ)*Polynomial.X))
    (fun J => (theta J).comp (Polynomial.C (a : ℝ)+Polynomial.C (b : ℝ)*Polynomial.X)) M0
    (fun J => (M J).comp (Polynomial.C (a : ℚ)+Polynomial.C (b : ℚ)*Polynomial.X))
    hmodels' (fun z hz => (hval z hz).1) (fun z hz => (hval z hz).2)
    (fun z => lo (a+b*z)) (fun z => hi (a+b*z)) (fun z => a0 (a+b*z)) (fun z => F (a+b*z))
    (fun z hz => hmin _ (hindex z hz)) (fun z hz => hside _ (hindex z hz))
    (fun z hz => hlo _ (hindex z hz)) (fun z hz => hhi _ (hindex z hz))
    (fun z hz => hLip _ (hindex z hz)) (fun z hz => hbound _ (hindex z hz))
    hM0 he hP0' htheta' Pnew hmem hchar' pNew hlog' hdegree'
    hdiff' hsmooth' hsize' hrough' ?_
  intro z hz
  have h := hbad (a+b*z) (hindex z hz)
  have hs : (t : ℤ)+(diff : ℤ)*a+(diff : ℤ)*b*z = (t : ℤ)+(diff : ℤ)*((a : ℤ)+(b : ℤ)*z) := by ring
  simpa only [hformula, Option.elim_none, Option.elim_some, Nat.cast_add, Nat.cast_mul, hs] using h

end Hindman168
