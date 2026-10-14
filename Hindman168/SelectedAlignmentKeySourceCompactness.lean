import Hindman168.SelectedAlignmentStableCatalogueSelection
import Hindman168.SelectedAlignmentSourceKeyRecipeFamily
import Hindman168.PositivePrincipalSumBounds
import Hindman168.AlignmentJointObservableCompactnessSource

/-! Actual positive-event selection and one full-source extraction yield
both measure and setwise face symmetries for every target marginal. The
setwise assertion concerns the actual projection of the same full joint
cube orbit; no independent target filtration or Haar law is introduced. -/
namespace Hindman168
open Module Filter MeasureTheory FiniteMass
open scoped Manifold ContDiff BigOperators Classical Topology NNReal
universe u
attribute [local instance] alignmentAddingPairFintype lieGroup_smooth_min_three

variable {ι : Type} [Fintype ι]
  {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν))) 
  (r : ι → ℕ) (b : ∀ ν, Basis (Fin (r ν)) ℝ (alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)).E)

include n v hv r b in
theorem selected_alignment_key_source_compactness
    {k : ℕ} {A : Finset ℚ} {P₀ : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P₀ F)
    (gap : Fin N) (hgap : gap ≤ i)
    {count : ℕ} (e : Fin (2*count) ↪o ℕ) (heN : ∀ j, e j < N)
    (pivot : Fin count)
    (q₀ : ℕ) (hq : 0 < q₀) (T : ι → Finset (Fin count))
    (hT : ∀ ν j, j ∈ T ν → j < pivot)
    (targets : ι → Finset (Fin N))
    (hTargets : ∀ ν j, j ∈ targets ν → j < gap)
    (C : ℕ) (V U : ι → Finset (AlignmentAddingPair count pivot → ℤ))
    (shift : ℕ → ((Fin N → ℕ) × (Fin N → ℕ) × (Fin N → ℕ) × ℕ × ℕ) →
      ι → AlignmentAddingPair N i → ℤ)
    (g a : ∀ _w : ℕ,
      ∀ _key : ((Fin N → ℕ) × (Fin N → ℕ) × (Fin N → ℕ) × ℕ × ℕ), ∀ ν, (D ν).G)
    (label : ℕ → SelectedAlignmentShortKey N → ∀ ν : ι, ℤ × ℤ)
    (obs : ∀ ν, ℕ → (ℤ × ℤ) → C((D ν).G ⧸ (D ν).Γ, ℝ))
    (B : ι → ℝ) (Lip : ι → ℝ≥0)
    (hB : ∀ ν w p x, |obs ν w p x| ≤ B ν)
    (hLip : ∀ ν w p x y, dist (obs ν w p x) (obs ν w p y) ≤
      (Lip ν : ℝ) * @dist ((D ν).G ⧸ (D ν).Γ) (D ν).metric.toDist x y)
    (W : ℕ → ℕ) (hW : Tendsto W atTop atTop)
    (S : ℕ → (Fin N → ℕ) → Prop) {β : ℝ} (hβ : 0 < β)
    (hS : ∀ᶠ j in atTop, β ≤ event (globalRawMass (F.cutoff (W j)) (primorial (W j)) N) (S j))
 :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI : MeasurableSpace J.G := borel J.G
    ∃ sample : ℕ → Fin N → ℕ,
      (∀ᶠ m in atTop, sample m ∈ (globalRawMass (F.cutoff (W m)) (primorial (W m)) N).support ∧ S m (sample m) ∧
        ∀ ν, selectedAlignmentFullExposureArrayStable F e heN pivot q₀ (W m) C (T ν) (V ν) (U ν) (sample m)) ∧
    let selectedShift := fun m ν => shift (W m) (alignmentShortExposureKey (alignmentGeometryWithGap F i gap) (W m) i (targets ν) (sample m)) ν
    let selectedG := fun m ν => g (W m) (alignmentShortExposureKey (alignmentGeometryWithGap F i gap) (W m) i (targets ν) (sample m)) ν
    let selectedA := fun m ν => a (W m) (alignmentShortExposureKey (alignmentGeometryWithGap F i gap) (W m) i (targets ν) (sample m)) ν
    ∃ f : ℕ → ℕ, StrictMono f ∧
      ∃ H : NativeRationalSubgroupFiltration J s,
      (∀ k, H.layer k ≤ (nativeOriginalSubgroupLieFiltration J).layer k) ∧
      ∃ M : ℕ, ∃ hM : 0 < M, ∃ sigma : Fin M → J.G,
      ∃ hRat : ∀ r, sigma r ∈ nativeSubgroupRationalHull (E := J.E) (I := J.I) J.Γ,
      ∃ h : ℝ → J.G, ∃ hh : ContMDiff 𝓘(ℝ) J.I ∞ h,
      ∃ limit : ∀ ν, C((D ν).G ⧸ (D ν).Γ, ℝ),
      (∀ ν, TendstoUniformly (fun m => obs ν (W (f m))
        (label (W (f m)) (alignmentShortExposureKey (alignmentGeometryWithGap F i gap)
          (W (f m)) i (targets ν) (sample (f m))) ν)) (limit ν) atTop) ∧
      NativeResidueLocalHaarLaw J H (fun m => (alignmentLocalLength (alignmentGeometryWithGap F i gap) (W (f m)) i : ℝ))
        (fun m => alignmentOriginalJointRealSource D n v hv (alignmentGeometryWithGap F i gap) q₀ (W (f m)) targets (sample (f m))
      (alignmentMicrocellFirst (alignedSqrtMicrocellWidth ((alignmentGeometryWithGap F i gap).gap (W (f m)) i.val) (F.modulus (W (f m))))
        (F.modulus (W (f m))) (sample (f m) i)) (selectedShift (f m)) (selectedG (f m)) (selectedA (f m))) M hM sigma hRat h ∧
      NativeCubeBoundedAlphaHaarLaw J H (fun m => (alignmentLocalLength (alignmentGeometryWithGap F i gap) (W (f m)) i : ℝ))
        (fun m => alignmentOriginalJointRealSource D n v hv (alignmentGeometryWithGap F i gap) q₀ (W (f m)) targets (sample (f m))
      (alignmentMicrocellFirst (alignedSqrtMicrocellWidth ((alignmentGeometryWithGap F i gap).gap (W (f m)) i.val) (F.modulus (W (f m))))
        (F.modulus (W (f m))) (sample (f m) i)) (selectedShift (f m)) (selectedG (f m)) (selectedA (f m))) M hM sigma hRat h ∧
      (∀ (beta : ℝ) (residue : ℤ),
        SelectedAlignmentCatalogueCosetSymmetry D n v hv targets gap.val H
          (sigma (signedPeriodResidue M hM residue)) (hRat _) (h beta)) ∧
      letI := J.metric
      letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
      letI : BorelSpace (J.G ⧸ J.Γ) := native_nilmanifold_metric_coset_borel J
      Tendsto (fun m => finiteEmpiricalProbability
        (Finset.Ico 0 ⌊(alignmentLocalLength (alignmentGeometryWithGap F i gap) (W (f m)) i : ℝ)⌋)
        (fun z => (alignmentOriginalJointRealSource D n v hv (alignmentGeometryWithGap F i gap)
          q₀ (W (f m)) targets (sample (f m))
          (alignmentMicrocellFirst
            (alignedSqrtMicrocellWidth (F.gap (W (f m)) gap.val) (F.modulus (W (f m))))
            (F.modulus (W (f m))) (sample (f m) i))
          (selectedShift (f m)) (selectedG (f m)) (selectedA (f m)) (z : ℝ) : J.G ⧸ J.Γ))
        (1 : J.G)) atTop
        (𝓝 (nativePointMixtureProbability J H M hM sigma hRat h hh.continuous)) := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI : MeasurableSpace J.G := borel J.G
  obtain ⟨sample,hs,f,hf,H,hle,M,hM,sigma,hRat,h,hh,hlocal,halpha,hsym⟩ :=
    selected_alignment_stable_catalogue_cosets D n v hv r b hF gap hgap e heN pivot
      q₀ hq T hT targets hTargets C V U shift g a W hW S hβ hS
  let key := fun m ν => alignmentShortExposureKey (alignmentGeometryWithGap F i gap)
    (W (f m)) i (targets ν) (sample (f m))
  let selectedObs := fun m ν => obs ν (W (f m)) (label (W (f m)) (key m ν) ν)
  letI : ∀ ν, CompactSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).quotientCompact
  obtain ⟨limit,further,hfurther,hconv⟩ := alignment_countable_lipschitz_observable_compactness
    (fun ν => (D ν).metric) (fun ν => nativeNilmanifold_metric_topology (D ν))
    selectedObs B Lip (fun m ν z => hB ν _ _ z)
    (fun m ν x y => hLip ν _ _ x y) id
  let L := fun m => (alignmentLocalLength (alignmentGeometryWithGap F i gap) (W (f m)) i : ℝ)
  let P := fun m => alignmentOriginalJointRealSource D n v hv (alignmentGeometryWithGap F i gap)
    q₀ (W (f m)) targets (sample (f m))
    (alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap (W (f m)) gap.val)
      (F.modulus (W (f m)))) (F.modulus (W (f m))) (sample (f m) i))
    (fun ν => shift (W (f m)) (key m ν) ν)
    (fun ν => g (W (f m)) (key m ν) ν) (fun ν => a (W (f m)) (key m ν) ν)
  have hp : NativeResidueLocalHaarLaw J H L P M hM sigma hRat h := by
    simpa only [alignmentGeometryWithGap_gap] using hlocal
  have ha : NativeCubeBoundedAlphaHaarLaw J H L P M hM sigma hRat h := by
    simpa only [alignmentGeometryWithGap_gap] using halpha
  have hL : Tendsto L atTop atTop := by
    simpa only [L, Function.comp_apply, alignmentGeometryWithGap_length] using
      alignment_local_length_cofinal hF gap (W ∘ f) (hW.comp hf.tendsto_atTop)
  have hp' := alignment_native_local_haar_subsequence J H L P M hM sigma hRat h hp further hfurther
  have ha' := alignment_native_alpha_haar_subsequence J H L P M hM sigma hRat h ha further hfurther
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : BorelSpace (J.G ⧸ J.Γ) := native_nilmanifold_metric_coset_borel J
  have hweak := native_original_point_weak_limit J H (L ∘ further)
    (hL.comp hfurther.tendsto_atTop) (P ∘ further) M hM sigma hRat h hh.continuous hp'
  refine ⟨sample,hs,f ∘ further,hf.comp hfurther,H,hle,M,hM,sigma,hRat,h,hh,
    limit,hconv,?_,?_,hsym,hweak⟩
  · simpa only [J, L, P, key, Function.comp_def, alignmentGeometryWithGap_gap] using hp'
  · simpa only [J, L, P, key, Function.comp_def, alignmentGeometryWithGap_gap] using ha'

end Hindman168
