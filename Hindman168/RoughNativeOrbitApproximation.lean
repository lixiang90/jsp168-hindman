import Hindman168.RoughNativeOrbitSourceMetric
import Hindman168.RoughScalarFamilyApproximation

namespace Hindman168
open Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_scalar_orbit_continuous {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (L : Subgroup D.G) (g : D.G) (V : D.E) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := roughNativeOrbitSourceMetric D L g
    letI : TopologicalSpace (L ⧸ (roughConjugateSubgroup D.Γ g).comap L.subtype) :=
      (roughNativeOrbitSourceMetric D L g).toUniformSpace.toTopologicalSpace
    Continuous (fun p : ℝ × (L ⧸ (roughConjugateSubgroup D.Γ g).comap L.subtype) =>
      roughConjugateOrbitMap D.Γ L g
        (nativeLieExponential (I := D.I) (G := D.G) (p.1 • V)) p.2) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := roughNativeOrbitSourceMetric D L g
  letI : TopologicalSpace (L ⧸ (roughConjugateSubgroup D.Γ g).comap L.subtype) :=
    (roughNativeOrbitSourceMetric D L g).toUniformSpace.toTopologicalSpace
  have hi : Isometry (roughConjugateOrbitMap D.Γ L g 1) := fun _ _ => rfl
  have hc := (rough_native_scalar_action_continuous D V).comp
    (continuous_fst.prodMk (hi.continuous.comp continuous_snd))
  convert hc using 1
  funext p
  change roughConjugateOrbitMap D.Γ L g
    (nativeLieExponential (I := D.I) (G := D.G) (p.1 • V)) p.2 =
      nativeLieExponential (I := D.I) (G := D.G) (p.1 • V) •
        roughConjugateOrbitMap D.Γ L g 1 p.2
  obtain ⟨h, hh⟩ := QuotientGroup.mk_surjective p.2
  rw [← hh]
  simp only [roughConjugateOrbitMap_mk, one_mul]
  exact congrArg (fun h : D.G => (QuotientGroup.mk h : D.G ⧸ D.Γ))
    (mul_assoc _ h.val g)

theorem rough_native_orbit_lipschitz_approximation {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (L : Subgroup D.G) (g : D.G)
    [CompactSpace (L ⧸ (roughConjugateSubgroup D.Γ g).comap L.subtype)]
    (V : D.E) (R B : ℝ) (hB : 0 ≤ B) (Lip : NNReal) {ε : ℝ} (hε : 0 < ε) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := roughNativeOrbitSourceMetric D L g
    letI : TopologicalSpace (L ⧸ (roughConjugateSubgroup D.Γ g).comap L.subtype) :=
      (roughNativeOrbitSourceMetric D L g).toUniformSpace.toTopologicalSpace
    ∃ K : NNReal, ∀ (t : ℝ), |t| ≤ R → ∀ F : (D.G ⧸ D.Γ) → ℝ,
      LipschitzWith Lip F → (∀ y, |F y| ≤ B) →
      ∃ f : (L ⧸ (roughConjugateSubgroup D.Γ g).comap L.subtype) → ℝ,
        LipschitzWith K f ∧
          (∀ x, |F (roughConjugateOrbitMap D.Γ L g
            (nativeLieExponential (I := D.I) (G := D.G) (t • V)) x) - f x| ≤ ε) ∧
          (∀ x, |f x| ≤ B) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := roughNativeOrbitSourceMetric D L g
  letI : TopologicalSpace (L ⧸ (roughConjugateSubgroup D.Γ g).comap L.subtype) :=
    (roughNativeOrbitSourceMetric D L g).toUniformSpace.toTopologicalSpace
  letI := rough_native_orbit_source_metric_compact D L g
  exact rough_scalar_family_lipschitz_approximation _
    (rough_native_scalar_orbit_continuous D L g V) R B hB Lip hε

end Hindman168
