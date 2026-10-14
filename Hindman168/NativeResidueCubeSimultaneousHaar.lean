import Hindman168.NativeResidueCubeProgressionHaar

/-! One length threshold works for every dimension through ORIGINAL s+1 and
every rational residue in the SAME finite family. No source is refactorized. -/
namespace Hindman168
open Filter MeasureTheory
open scoped Manifold ContDiff Topology BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_residue_cubes_through_original_step_haar {s ℓ M : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : Fin M → D.G)
    (hρ : ∀ r, ρ r ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (p : ℕ → RoughVectorMvPolynomial Unit D.E)
    (hp : ∀ m, RoughVectorMvWeightedDegree F.layer (p m) 0)
    (hIrr : NativeSubgroupSequentialIrrational D F L p)
    (t : ℕ) (ht : 0 < t)
    (c R B η : ℝ) (T : NNReal) (hc : 0 < c) (hR : 0 ≤ R) (hB : 0 ≤ B) (hη : 0 < η) :
    ∀ᶠ m in atTop, ∀ q : Fin (s+2), ∀ r : Fin M,
      let A := nativeResidueCubeData D F (ρ r) (hρ r) q.val (2^q.val-1) (nativeCubeVertexEnumeration q.val)
      letI : MeasurableSpace A.E := borel A.E
      letI : MeasurableSpace A.G := borel A.G
      letI := A.metric
      letI : TopologicalSpace (A.G ⧸ A.Γ) := A.metric.toUniformSpace.toTopologicalSpace
      ∀ lo hi v : Fin (q.val+1) → ℤ,
        (∀ i, c*L m ≤ (hi i : ℝ)-lo i ∧ (hi i : ℝ)-lo i ≤ R*L m) →
        (∀ i, |(lo i : ℝ)| ≤ R*L m ∧ |(hi i : ℝ)| ≤ R*L m) →
        ∀ z : ℝ, ∀ f : C(A.G ⧸ A.Γ, ℂ), LipschitzWith T f → (∀ y, ‖f y‖ ≤ B) →
          ‖finiteComplexSetMean (alignmentBoxClass lo hi v t)
            (fun x => f (nativeResidueCubeSpatialOrbit D F (ρ r) (hρ r)
              q.val (2^q.val-1) (nativeCubeVertexEnumeration q.val) (p m) (hp m)
              (fun i => i.elim z (fun j => (x j : ℝ))) : A.G ⧸ A.Γ)) -
                ∫ y, f y ∂nativeNilmanifoldQuotientProbability A‖ < η := by
  apply Filter.eventually_all.mpr
  intro q
  apply Filter.eventually_all.mpr
  intro r
  exact native_residue_cube_progression_box_haar D F (ρ r) (hρ r)
    q.val (2^q.val-1) (nativeCubeVertexEnumeration q.val) L hL p hp hIrr
    t ht c R B η T hc hR hB hη

end Hindman168
