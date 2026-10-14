import Hindman168.NativeOriginalHorizontalKernelGeometry

/-! ACTUAL original horizontal character alone supplies all rational/geometry
inputs to proved kernel descent. No supplied pivot, lattice period, subgroup
or inverse. Finite canonical children and budgets precede all raw sources. -/
namespace Hindman168
open Filter MvPolynomial
open scoped Manifold ContDiff Classical
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_original_horizontal_kernel_descent {κ : Type*} [Fintype κ] {step : ℕ}
    (D : NativeNilmanifoldData.{u} step) (χ : D.E →ₗ[ℝ] ℝ)
    (hHor : RoughNativeHorizontalFunctional (I := D.I) D.Γ χ)
    (q : ℕ)
    (A0 C B : ℝ) (hA0 : 0 < A0) (hC : 1 ≤ C) (hB : 0 ≤ B) (Lip : NNReal)
    (c η : ℝ) (hc : 0 < c) (hη : 0 < η) (Scale Z : ℕ → ℝ)
    (hScale : Tendsto Scale atTop atTop)
    (hr : ∀ a : ℝ, 0 < a → Tendsto (fun w => Z w/(Scale w)^a) atTop atTop) :
    let S : LieSubalgebra ℝ (GroupLieAlgebra D.I D.G) := ⊤
    let hS := native_original_top_lie_rational D
    let hχ := native_original_horizontal_top_bracket D χ hHor
    let hΓ := hHor.2.2
    let hQ := rough_native_integral_character_rational_on_span (I := D.I) D.Γ χ hΓ
    ∃ V : D.E, ∃ hVr : V ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ,
      V ∈ nativeLieSubalgebraModel S ∧ χ V = 1 ∧
      ∃ K : ℕ, 0 < K ∧
        nativeLieExponential (I := D.I) (G := D.G) ((K : ℝ) • V) ∈ D.Γ ∧
    let s := roughSpatialDegreeIndices κ q
    let family := fun j : Fin K => roughNativeKernelNilmanifold D S hS χ hχ hQ V hVr (j.val : ℤ)
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ j, MetricSpace ((family j).G ⧸ (family j).Γ) := fun j => (family j).metric
    letI : ∀ j, TopologicalSpace ((family j).G ⧸ (family j).Γ) := fun j =>
      (family j).metric.toUniformSpace.toTopologicalSpace
    ∃ Part : ℕ, ∃ L : NNReal, ∃ _ : 0 < Part, ∀ H : ℕ, 0 < H →
      ∃ N : ℕ, 0 < N ∧ ∀ᶠ w in atTop, ∀ (t diff : ℕ)
        (pOb : (κ → ℕ) → ℕ → ℕ) (bOb : (κ → ℕ) → ℕ → κ → ℕ),
        ∀ (lo hi a0 : ℕ → κ → ℤ) (F : ℕ → (D.G ⧸ D.Γ) → ℂ),
          (∀ z : ℕ, z < N → ∀ j, c*(Z w) ≤ (hi z j : ℝ)-lo z j) →
          (∀ z : ℕ, z < N → ∀ j, (hi z j : ℝ)-lo z j ≤ C*(Z w)) →
          (∀ z : ℕ, z < N → ∀ j, |(lo z j : ℝ)| ≤ C*(Z w)) →
          (∀ z : ℕ, z < N → ∀ j, |(hi z j : ℝ)| ≤ C*(Z w)) →
          (∀ z : ℕ, z < N → LipschitzWith Lip (F z)) →
          (∀ z : ℕ, z < N → ∀ v, ‖F z v‖ ≤ B) →
          ∀ (P : (Option κ → ℝ) → D.G)
            (_hP : ∀ x, P x ∈ nativeLieSubalgebraSubgroup (E := D.E) S),
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
                (roughScalarSpatialProjection χ pLog (z : ℝ))) : ℝ) : UnitAddCircle)‖ ≤
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
  let S : LieSubalgebra ℝ (GroupLieAlgebra D.I D.G) := ⊤
  let hS := native_original_top_lie_rational D
  let hχ := native_original_horizontal_top_bracket D χ hHor
  obtain ⟨v,hv⟩ := DFunLike.ne_iff.mp hHor.1
  have hv0 : χ v ≠ 0 := by simpa only [LinearMap.zero_apply] using hv
  exact rough_native_normalized_obstruction_bad_family D S hS χ hχ hHor.2.2 v
    (show v ∈ nativeLieSubalgebraModel S from (Submodule.mem_top : v ∈ (⊤ : Submodule ℝ D.E))) hv0
    q A0 C B hA0 hC hB Lip c η hc hη Scale Z hScale hr

end Hindman168
