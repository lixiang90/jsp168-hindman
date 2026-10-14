import Hindman168.NativeRationalLayerRealWindowHaar
import Hindman168.NativeCompactFamilyUnitDetection

/-! The genuine subgroup window law for any fixed compact family of
continuous observables. Finite unit-Lipschitz detectors are constructed
before all origins, window lengths and sample-dependent test choices. -/
namespace Hindman168
open Filter MeasureTheory
open scoped Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_layer_compact_window_haar {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (rho : D.G) (hRat : rho ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (p : ℕ → RoughVectorMvPolynomial Unit D.E)
    (hp : ∀ n, RoughVectorMvWeightedDegree F.layer (p n) 0)
    (hIrr : NativeSubgroupSequentialIrrational D F L p)
    (d : ℚ) (hd : d ≠ 0) (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (δ : ℝ) (hδ : 0 < δ) :
    let A := nativeRationalLayerOrbitData D F 0 rho hRat
    letI : MeasurableSpace A.E := borel A.E
    letI : MeasurableSpace A.G := borel A.G
    letI := A.metric
    letI : TopologicalSpace (A.G ⧸ A.Γ) := A.metric.toUniformSpace.toTopologicalSpace
    ∀ H : Set C(A.G ⧸ A.Γ,ℂ), IsCompact H →
    ∀ᶠ n in atTop, ∀ b : ℝ, ∀ m : ℕ, τ*L n ≤ m → ∀ f ∈ H,
      ‖finiteComplexSetMean (scalarMvIntegerCube Unit m)
        (fun x => f (QuotientGroup.mk (s := A.Γ) (show A.G from
          nativeRationalSubgroupPolynomialOrbit D F (p n) (hp n)
            (fun i => b + (d : ℝ)*(x i : ℝ))))) -
            ∫ q, f q ∂nativeNilmanifoldQuotientProbability A‖ < δ := by
  let A := nativeRationalLayerOrbitData D F 0 rho hRat
  letI : MeasurableSpace A.E := borel A.E
  letI : MeasurableSpace A.G := borel A.G
  letI := A.metric
  letI : TopologicalSpace (A.G ⧸ A.Γ) := A.metric.toUniformSpace.toTopologicalSpace
  dsimp only
  intro H hH
  obtain ⟨θ,hθ,T,hT,hDetect⟩ := native_compact_family_unit_detection A δ hδ H hH
  have h := native_rational_layer_real_window_haar_unit D F rho hRat L hL p hp hIrr
    d hd τ hτ hτ1 θ hθ
  filter_upwards [h] with n hn
  intro b m hm f hf
  by_contra hbad
  obtain ⟨g,hg,hlarge⟩ := hDetect (scalarMvIntegerCube Unit m)
    (fun x => QuotientGroup.mk (s := A.Γ) (show A.G from
      nativeRationalSubgroupPolynomialOrbit D F (p n) (hp n)
        (fun i => b + (d : ℝ)*(x i : ℝ)))) f hf (le_of_not_gt hbad)
  exact (not_lt_of_ge (hn b m hm g (hT g hg)).le) hlarge

end Hindman168
