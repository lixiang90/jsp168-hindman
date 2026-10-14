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

theorem rough_native_obstruction_bad_family {κ : Type*} [Fintype κ] {step : ℕ}
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
        ∀ (lo hi a0 : ℕ → κ → ℤ) (F : ℕ → (D.G ⧸ D.Γ) → ℝ),
          (∀ z : ℕ, z < N → ∀ j, c*(Z w) ≤ (hi z j : ℝ)-lo z j) →
          (∀ z : ℕ, z < N → ∀ j, (hi z j : ℝ)-lo z j ≤ C*(Z w)) →
          (∀ z : ℕ, z < N → ∀ j, |(lo z j : ℝ)| ≤ C*(Z w)) →
          (∀ z : ℕ, z < N → ∀ j, |(hi z j : ℝ)| ≤ C*(Z w)) →
          (∀ z : ℕ, z < N → LipschitzWith Lip (F z)) →
          (∀ z : ℕ, z < N → ∀ v, |F z v| ≤ B) →
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
            η ≤ |FiniteMass.expectation (FiniteMass.uniformFinsetMass (alignmentBoxClass (lo z) (hi z) (a0 z) (t+diff*z)))
              (fun x => F z (QuotientGroup.mk (P (Option.elim · (z : ℝ) (fun j => (x j : ℝ))))))-
            FiniteMass.expectation (FiniteMass.uniformFinsetMass
              (Fintype.piFinset (fun j => Finset.Ico (lo z j) (hi z j))))
              (fun x => F z (QuotientGroup.mk (P (Option.elim · (z : ℝ) (fun j => (x j : ℝ))))))|) →
          ∃ j : Fin K, Module.finrank ℝ (family j).E < Module.finrank ℝ D.E ∧
            RoughNativeBadFamily (κ := κ) (family j) H w (Scale w) ((Z w)/K)
              (roughKernelDegreeFactor step*q) (c/(4*Part)) (max (4*C/Part) (C+1)) L B (η/2) := by
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
