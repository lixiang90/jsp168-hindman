import Hindman168.NativeRationalLayerOrbit
import Hindman168.NativeNilmanifoldQuotientProbability

/-! The actual invariant probability on H/(H intersect rho Gamma rho^-1)
and its image on h H rho Gamma/Gamma. These constructors and probability,
compactness and concentration results do NOT assume an empirical Haar law. -/
namespace Hindman168
open Set MeasureTheory
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRationalLayerOrbitMap {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (i : ℕ) (rho : D.G) (hRat : rho ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (h : D.G) :
    (nativeRationalLayerOrbitData D F i rho hRat).G ⧸
      (nativeRationalLayerOrbitData D F i rho hRat).Γ → D.G ⧸ D.Γ :=
  roughConjugateOrbitMap D.Γ (nativeRationalSubgroupLayer D F i)
    (nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) rho)) h

theorem native_rational_layer_orbit_map_mk {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (i : ℕ) (rho : D.G) (hRat : rho ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (h : D.G) (x : nativeRationalSubgroupLayer D F i) :
    nativeRationalLayerOrbitMap D F i rho hRat h (QuotientGroup.mk x) =
      (h * (x : D.G) * rho : D.G ⧸ D.Γ) := by
  change (h * (x : D.G) * nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
    (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) rho) : D.G ⧸ D.Γ) = _
  rw [nativeLieExponential_globalLogarithm]

theorem native_rational_layer_orbit_map_continuous {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (i : ℕ) (rho : D.G) (hRat : rho ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (h : D.G) : Continuous (nativeRationalLayerOrbitMap D F i rho hRat h) :=
  roughConjugateOrbitMap_continuous D.Γ _ _ h

theorem native_rational_layer_orbit_map_injective {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (i : ℕ) (rho : D.G) (hRat : rho ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (h : D.G) : Function.Injective (nativeRationalLayerOrbitMap D F i rho hRat h) :=
  roughConjugateOrbitMap_injective D.Γ _ _ h

theorem native_rational_layer_orbit_range_compact {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (i : ℕ) (rho : D.G) (hRat : rho ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (h : D.G) : IsCompact (range (nativeRationalLayerOrbitMap D F i rho hRat h)) := by
  let A := nativeRationalLayerOrbitData D F i rho hRat
  letI : CompactSpace (A.G ⧸ A.Γ) := A.quotientCompact
  exact isCompact_range (native_rational_layer_orbit_map_continuous D F i rho hRat h)

noncomputable def nativeRationalLayerHaarImage {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (i : ℕ) (rho : D.G) (hRat : rho ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (h : D.G) :
    letI : MeasurableSpace D.G := borel D.G
    Measure (D.G ⧸ D.Γ) := by
  letI : MeasurableSpace D.G := borel D.G
  let A := nativeRationalLayerOrbitData D F i rho hRat
  letI : MeasurableSpace A.E := borel A.E
  letI : MeasurableSpace A.G := borel A.G
  exact Measure.map (nativeRationalLayerOrbitMap D F i rho hRat h)
    (nativeNilmanifoldQuotientProbability A)

theorem native_rational_layer_haar_image_isProbability {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (i : ℕ) (rho : D.G) (hRat : rho ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (h : D.G) :
    letI : MeasurableSpace D.G := borel D.G
    IsProbabilityMeasure (nativeRationalLayerHaarImage D F i rho hRat h) := by
  letI : MeasurableSpace D.G := borel D.G
  let A := nativeRationalLayerOrbitData D F i rho hRat
  letI : MeasurableSpace A.E := borel A.E
  letI : MeasurableSpace A.G := borel A.G
  letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_coset_borel D
  letI : BorelSpace (A.G ⧸ A.Γ) := native_nilmanifold_coset_borel A
  letI := native_nilmanifold_quotient_probability_isProbability A
  exact Measure.isProbabilityMeasure_map
    (native_rational_layer_orbit_map_continuous D F i rho hRat h).measurable.aemeasurable

theorem native_rational_layer_haar_image_concentrated {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (i : ℕ) (rho : D.G) (hRat : rho ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (h : D.G) :
    letI : MeasurableSpace D.G := borel D.G
    ∀ᵐ x ∂nativeRationalLayerHaarImage D F i rho hRat h,
      x ∈ range (nativeRationalLayerOrbitMap D F i rho hRat h) := by
  letI : MeasurableSpace D.G := borel D.G
  let A := nativeRationalLayerOrbitData D F i rho hRat
  letI : MeasurableSpace A.E := borel A.E
  letI : MeasurableSpace A.G := borel A.G
  letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_coset_borel D
  letI : BorelSpace (A.G ⧸ A.Γ) := native_nilmanifold_coset_borel A
  letI : IsClosed (D.Γ : Set D.G) := Subgroup.isClosed_of_discrete
  exact ae_map_mem_range _
    (native_rational_layer_orbit_range_compact D F i rho hRat h).isClosed.measurableSet _

theorem native_rational_layer_haar_image_subgroup_invariant {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (i : ℕ) (rho : D.G) (hRat : rho ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (h : D.G) (y : nativeRationalSubgroupLayer D F i) :
    letI : MeasurableSpace D.G := borel D.G
    nativeRationalLayerHaarImage D F i rho hRat (h * y.val) =
      nativeRationalLayerHaarImage D F i rho hRat h := by
  letI : MeasurableSpace D.G := borel D.G
  let A := nativeRationalLayerOrbitData D F i rho hRat
  letI : MeasurableSpace A.E := borel A.E
  letI : MeasurableSpace A.G := borel A.G
  letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_coset_borel D
  letI : BorelSpace (A.G ⧸ A.Γ) := native_nilmanifold_coset_borel A
  let yA : A.G := y
  let Ty : A.G ⧸ A.Γ → A.G ⧸ A.Γ := fun x => yA • x
  have hTy : Measurable Ty := (continuous_const_smul yA).measurable
  have hMap : nativeRationalLayerOrbitMap D F i rho hRat (h * y.val) =
      nativeRationalLayerOrbitMap D F i rho hRat h ∘ Ty := by
    funext x
    obtain ⟨z,rfl⟩ := QuotientGroup.mk_surjective x
    change ((h * y.val) * z.val *
      nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
        (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) rho) : D.G ⧸ D.Γ) =
      (h * (y.val * z.val) *
      nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
        (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) rho) : D.G ⧸ D.Γ)
    rw [mul_assoc h y.val z.val]
  change Measure.map _ (nativeNilmanifoldQuotientProbability A) =
    Measure.map _ (nativeNilmanifoldQuotientProbability A)
  rw [hMap,← Measure.map_map
    (native_rational_layer_orbit_map_continuous D F i rho hRat h).measurable hTy]
  rw [show Measure.map Ty (nativeNilmanifoldQuotientProbability A) =
    nativeNilmanifoldQuotientProbability A from native_nilmanifold_quotient_probability_translate A yA]

end Hindman168
