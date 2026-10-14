import Hindman168.NativeRationalLayerPolynomialInverse
import Hindman168.NativeSubgroupHorizontalEscape

/-! The q=0 Haar law on the unshifted full integer interval for an actual
irrational adapted sequence in the actual subgroup/conjugated lattice.
The convergence is uniform over the full unit Lipschitz test family.
Local boxes, progressions, smooth factors and cubes are separate obligations. -/
namespace Hindman168
open Filter MeasureTheory
open scoped Manifold ContDiff Topology BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_layer_point_haar_unit {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (rho : D.G) (hRat : rho ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (p : ℕ → RoughVectorMvPolynomial Unit D.E)
    (hp : ∀ n, RoughVectorMvWeightedDegree F.layer (p n) 0)
    (hIrr : NativeSubgroupSequentialIrrational D F (fun n => (N n : ℝ)) p)
    (δ : ℝ) (hδ : 0 < δ) :
    let A := nativeRationalLayerOrbitData D F 0 rho hRat
    letI : MeasurableSpace A.E := borel A.E
    letI : MeasurableSpace A.G := borel A.G
    letI := A.metric
    letI : TopologicalSpace (A.G ⧸ A.Γ) := A.metric.toUniformSpace.toTopologicalSpace
    ∀ᶠ n in atTop, ∀ f ∈ unitLipschitzObservables (A.G ⧸ A.Γ),
      ‖finiteComplexSetMean (scalarMvIntegerCube Unit (N n))
        (fun x => f (QuotientGroup.mk (s := A.Γ) (show A.G from
          nativeRationalSubgroupPolynomialOrbit D F (p n) (hp n) (fun i => (x i : ℝ))))) -
            ∫ q, f q ∂nativeNilmanifoldQuotientProbability A‖ < δ := by
  classical
  let A := nativeRationalLayerOrbitData D F 0 rho hRat
  letI : MeasurableSpace A.E := borel A.E
  letI : MeasurableSpace A.G := borel A.G
  letI := A.metric
  letI : TopologicalSpace (A.G ⧸ A.Γ) := A.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨M,_hM,hInv⟩ := native_rational_layer_polynomial_inverse (σ := Unit) D F rho hRat δ hδ
  let T := roughNativeHorizontalCharacterGrid (I := A.I) A.Γ (M : ℝ)
  let ext := nativeSubgroupHorizontalExtension D F rho hRat
  have hEscape : ∀ᶠ n in atTop, ∀ chi ∈ T, ∀ j ∈ Finset.Icc 1 ℓ,
      NativeSubgroupRationalLevelCharacter D F j (ext chi) →
      (M : ℝ) < (N n : ℝ)^j * ‖((MvPolynomial.coeff (Finsupp.single () j)
        (roughVectorMvProjection (ext chi) (p n)) : ℝ) : UnitAddCircle)‖ := by
    apply (Filter.eventually_all_finset T).mpr
    intro chi hchi
    apply (Filter.eventually_all_finset (Finset.Icc 1 ℓ)).mpr
    intro j hj
    by_cases hLevel : NativeSubgroupRationalLevelCharacter D F j (ext chi)
    · have hHor := ((rough_native_horizontal_grid_mem_iff A.Γ (M : ℝ) chi).mp hchi).2
      have hB := native_actual_subgroup_horizontal_extension_bracket D F rho hRat chi hHor
      have h := native_subgroup_horizontal_top_coefficient_escape D F (fun n => (N n : ℝ))
        p hp hIrr (ext chi) hB j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2 hLevel
      exact (h.eventually_gt_atTop (M : ℝ)).mono (fun _ hn _ => hn)
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hLevel h))
  filter_upwards [hEscape, hN.eventually_gt_atTop 0] with n hn hpos
  intro f hf
  by_contra hbad
  obtain ⟨chi,hchi,j,hj,hjTop,hLevel,_hTail,hMono,_hBin⟩ :=
    hInv (p n) (hp n) (N n) hpos f hf (le_of_not_gt hbad)
  have hsmall := hMono (fun _ : Unit => j) (by simpa using (show 0 < j by omega))
  have hindex : Finsupp.equivFunOnFinite.symm (fun _ : Unit => j) = Finsupp.single () j := by
    apply Finsupp.ext
    intro x
    cases x
    simp
  simp only [Finset.univ_unique, Finset.sum_singleton, hindex] at hsmall
  exact (not_lt_of_ge hsmall) (hn chi hchi j (Finset.mem_Icc.mpr ⟨hj,hjTop⟩) hLevel)

end Hindman168
