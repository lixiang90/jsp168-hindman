import Hindman168.NativeNilmanifoldFiniteDiscrepancy
import Hindman168.BoundedLipschitzNormalization

/-! A GENUINE compact continuous-observable family on actual native data
admits ONE fixed finite unit-Lipschitz discrepancy detector. Budgets precede
ALL sample sets/orbits. No inverse or source nonuniformity is assumed. -/
namespace Hindman168
open scoped Manifold ContDiff Classical
universe u

theorem native_compact_family_unit_detection {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (δ : ℝ) (hδ : 0 < δ) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (H : Set C(D.G ⧸ D.Γ,ℂ)), IsCompact H →
      ∃ θ : ℝ, 0 < θ ∧ ∃ P : Finset C(D.G ⧸ D.Γ,ℂ),
        (∀ J ∈ P, J ∈ unitLipschitzObservables (D.G ⧸ D.Γ)) ∧
        ∀ {α : Type*} (S : Finset α) (orbit : α → D.G ⧸ D.Γ),
          ∀ F ∈ H, δ ≤ ‖nativeNilmanifoldFiniteDiscrepancy D S orbit F‖ →
            ∃ J ∈ P, θ < ‖nativeNilmanifoldFiniteDiscrepancy D S orbit J‖ := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  intro H hH
  obtain ⟨B,L,hB,hL,P,hP,hApprox⟩ := compact_family_bounded_lipschitz_approximation
    (D.G ⧸ D.Γ) H hH (δ/8) (by positivity)
  let R := 1+B+L
  have hR : 0 < R := by dsimp only [R]; positivity
  have hBR : B ≤ R := by dsimp only [R]; linarith
  have hLR : L ≤ R := by dsimp only [R]; linarith
  let scale : C(D.G ⧸ D.Γ,ℂ) → C(D.G ⧸ D.Γ,ℂ) := fun F => (R : ℂ)⁻¹ • F
  refine ⟨(δ/2)/R,by positivity,P.image scale,?_,?_⟩
  · intro J hJ
    obtain ⟨F,hF,rfl⟩ := Finset.mem_image.mp hJ
    exact bounded_lipschitz_normalization _ F B L R hR hBR hLR (hP F hF).1 (hP F hF).2
  · intro α S orbit F hF hLarge
    obtain ⟨G,hG,hClose⟩ := hApprox F hF
    have hDetect := linear_discrepancy_approximant_detection _
      (nativeNilmanifoldFiniteDiscrepancy D S orbit) (native_nilmanifold_finite_discrepancy_norm D S orbit)
      F G (δ/8) δ hClose hLarge
    have hMean : δ/2 < ‖nativeNilmanifoldFiniteDiscrepancy D S orbit G‖ := by linarith
    refine ⟨scale G,Finset.mem_image.mpr ⟨G,hG,rfl⟩,?_⟩
    change (δ/2)/R < ‖nativeNilmanifoldFiniteDiscrepancy D S orbit ((R : ℂ)⁻¹ • G)‖
    rw [linear_discrepancy_normalization_norm _ _ G R hR,div_eq_mul_inv]
    simpa only [mul_comm] using mul_lt_mul_of_pos_left hMean (inv_pos.mpr hR)

end Hindman168
