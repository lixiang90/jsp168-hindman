import Hindman168.NativeResidueCubeProgressionHaar
import Hindman168.NativeCompactFamilyUnitDetection

/-! Uniform actual cube Haar laws for every fixed compact continuous test family. -/
namespace Hindman168
open Filter MeasureTheory
open scoped Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_residue_cube_compact_progression_haar {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (p : ℕ → RoughVectorMvPolynomial Unit D.E)
    (hp : ∀ m, RoughVectorMvWeightedDegree F.layer (p m) 0)
    (hIrr : NativeSubgroupSequentialIrrational D F L p)
    (t : ℕ) (ht : 0 < t)
    (c R η : ℝ) (hc : 0 < c) (hR : 0 ≤ R) (hη : 0 < η) :
    let A := nativeResidueCubeData D F ρ hρ d n e
    letI : MeasurableSpace A.E := borel A.E
    letI : MeasurableSpace A.G := borel A.G
    letI := A.metric
    letI : TopologicalSpace (A.G ⧸ A.Γ) := A.metric.toUniformSpace.toTopologicalSpace
    ∀ H : Set C(A.G ⧸ A.Γ, ℂ), IsCompact H →
    ∀ᶠ m in atTop, ∀ lo hi v : Fin (d+1) → ℤ,
      (∀ i, c*L m ≤ (hi i : ℝ)-lo i ∧ (hi i : ℝ)-lo i ≤ R*L m) →
      (∀ i, |(lo i : ℝ)| ≤ R*L m ∧ |(hi i : ℝ)| ≤ R*L m) →
      ∀ z : ℝ, ∀ f ∈ H,
        ‖finiteComplexSetMean (alignmentBoxClass lo hi v t)
          (fun x => f (nativeResidueCubeSpatialOrbit D F ρ hρ d n e (p m) (hp m)
            (fun i => i.elim z (fun j => (x j : ℝ))) : A.G ⧸ A.Γ)) -
              ∫ q, f q ∂nativeNilmanifoldQuotientProbability A‖ < η := by
  let A := nativeResidueCubeData D F ρ hρ d n e
  letI : MeasurableSpace A.E := borel A.E
  letI : MeasurableSpace A.G := borel A.G
  letI := A.metric
  letI : TopologicalSpace (A.G ⧸ A.Γ) := A.metric.toUniformSpace.toTopologicalSpace
  dsimp only
  intro H hH
  obtain ⟨θ,hθ,P,hP,hDetect⟩ := native_compact_family_unit_detection A η hη H hH
  have h := native_residue_cube_progression_box_haar D F ρ hρ d n e L hL p hp hIrr
    t ht c R 1 θ 1 hc hR zero_le_one hθ
  filter_upwards [h] with m hm
  intro lo hi v hlen hloc z f hf
  by_contra hbad
  obtain ⟨g,hg,hlarge⟩ := hDetect (alignmentBoxClass lo hi v t)
    (fun x => (nativeResidueCubeSpatialOrbit D F ρ hρ d n e (p m) (hp m)
      (fun i => i.elim z (fun j => (x j : ℝ))) : A.G ⧸ A.Γ)) f hf (le_of_not_gt hbad)
  exact (not_lt_of_ge (hm lo hi v hlen hloc z g (hP g hg).1 (hP g hg).2).le) hlarge

end Hindman168
