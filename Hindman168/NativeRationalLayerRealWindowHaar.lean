import Hindman168.NativeRationalLayerWindowHaar
import Hindman168.NativeSubgroupIrrationalScale

/-! The original REAL factorization scale supplies the actual uniform
point-window Haar law. Natural floor comparison is proved; neither scale
integrality nor an extra irrationality premise is required. -/
namespace Hindman168
open Filter MeasureTheory
open scoped Manifold ContDiff Topology BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_layer_real_window_haar_unit {s ℓ : ℕ}
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
    ∀ᶠ n in atTop, ∀ b : ℝ, ∀ m : ℕ, τ*L n ≤ m →
      ∀ f ∈ unitLipschitzObservables (A.G ⧸ A.Γ),
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
  have hN : Tendsto (fun n => ⌊L n⌋₊) atTop atTop := tendsto_nat_floor_atTop.comp hL
  have hNIrr := native_subgroup_irrational_nat_floor D F L hL p hIrr
  have h := native_rational_layer_window_haar_unit D F rho hRat _ hN p hp hNIrr d hd τ hτ hτ1 δ hδ
  filter_upwards [h,hL.eventually_ge_atTop 0] with n hn hpos
  intro b m hlen f hf
  apply hn b m _ f hf
  exact (mul_le_mul_of_nonneg_left (Nat.floor_le hpos) hτ.le).trans hlen

end Hindman168
