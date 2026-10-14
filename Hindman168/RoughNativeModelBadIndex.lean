import Hindman168.RoughNativePieceDescent
import Hindman168.RoughFiniteCoefficientAssembly

import Hindman168.RoughNativeBadIndex
import Hindman168.RoughNativeModelPieceDescent

namespace Hindman168
open MvPolynomial
open scoped Manifold ContDiff Classical
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_model_bad_index {κ : Type*} [Fintype κ] {step : ℕ}
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
    {εfreeze εapprox : ℝ} (hεf : 0 < εfreeze) (hεa : 0 < εapprox) :
    let family := fun j : Fin K => roughNativeKernelNilmanifold D S hS χ hχ hQ V hVr (j.val : ℤ)
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ j, MetricSpace ((family j).G ⧸ (family j).Γ) := fun j => (family j).metric
    letI : ∀ j, TopologicalSpace ((family j).G ⧸ (family j).Γ) := fun j =>
      (family j).metric.toUniformSpace.toTopologicalSpace
    ∃ N : ℕ, ∃ L : NNReal, ∃ _ : 0 < N, ∀ (w H q z : ℕ) (Z : ℝ)
      (P0 : Polynomial ℝ) (theta : (κ →₀ ℕ) → Polynomial ℝ)
      (M0 : Polynomial ℚ) (M : (κ →₀ ℕ) → Polynomial ℚ),
      (∀ J ∈ support, RoughCoefficientModel w H q (∑ j, J j) Z A (theta J) (M J)) →
      z < H → 0 < Z → (∃ n : ℤ, M0.eval (z : ℚ) = (n : ℚ)) →
      (0 ≤ P0.eval (z : ℝ)-((M0.eval (z : ℚ) : ℚ) : ℝ) ∧
        P0.eval (z : ℝ)-((M0.eval (z : ℚ) : ℚ) : ℝ) < 1) →
      ∀ (l r : κ → ℤ), (∀ j, 2*(N : ℤ) ≤ r j-l j) →
      (∀ j, (r j : ℝ)-l j ≤ C*Z) →
      (∀ j, |(l j : ℝ)| ≤ C*Z) → (∀ j, |(r j : ℝ)| ≤ C*Z) →
      ∀ F : (D.G ⧸ D.Γ) → ℝ, LipschitzWith Lip F → (∀ v, |F v| ≤ B) →
      M0.natDegree ≤ q → (∀ J ∈ support, (∑ j, J j) ≤ q) →
      P0.natDegree ≤ q → (∀ J ∈ support, (theta J).natDegree+J.sum (fun _ e => e) ≤ q) →
      let m := map (Rat.castHom ℝ) (roughSpatialJointPolynomial support M0 M)
      let a := roughSpatialJointPolynomial support P0 theta-m
      ∀ (P : (Option κ → ℝ) → D.G)
        (hP : ∀ x, P x ∈ nativeLieSubalgebraSubgroup (E := D.E) S)
        (hchar : ∀ x, nativeLieLogarithmCharacter (I := D.I) (G := D.G) χ (P x) = eval x (roughSpatialJointPolynomial support P0 theta)),
      ∀ (pLog : RoughVectorMvPolynomial (Option κ) D.E)
        (_hpLog : ∀ x, roughVectorMvEval pLog x =
          nativeLieGlobalLogarithm (E := D.E) (I := D.I) (P x))
        (_hdegree : RoughVectorMvDegreeLE pLog q),
      let hsplit : ∀ x, nativeLieLogarithmCharacter (I := D.I) (G := D.G) χ (P x) = eval x a+eval x m :=
        fun x => by rw [hchar x]; dsimp only [a]; rw [map_sub, sub_add_cancel]
      let Q := fun j : Fin K => roughNativeKernelMap D S hS χ hχ hQ V hVr
        (j.val : ℤ) hVS hχV a m P hP hsplit
        ∀ (a0 : κ → ℤ) (t : ℕ), 0 < t → t.Coprime K →
          ∀ (c θ η : ℝ), 0 < c → 2*(t : ℝ) ≤ c*Z →
          (∀ j, c*Z ≤ (r j : ℝ)-l j) →
          (∀ j, (2*N*K : ℤ) ≤ r j-l j) → 1 ≤ Z/K →
          θ+B*(((N ^ Fintype.card κ*K ^ Fintype.card κ : ℕ) : ℝ)*
            Fintype.card κ*(5*(t : ℝ)/(c*Z)))+2*(εfreeze+εapprox) < η →
          η ≤ |FiniteMass.expectation (FiniteMass.uniformFinsetMass (alignmentBoxClass l r a0 t))
              (fun x => F (QuotientGroup.mk (P (Option.elim · (z : ℝ) (fun j => (x j : ℝ))))))-
            FiniteMass.expectation (FiniteMass.uniformFinsetMass
              (Fintype.piFinset (fun j => Finset.Ico (l j) (r j))))
              (fun x => F (QuotientGroup.mk (P (Option.elim · (z : ℝ) (fun j => (x j : ℝ))))))| →
          ∃ (u : κ → Fin K) (j : Fin K),
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
