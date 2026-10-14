import Hindman168.AlignmentOriginalJointRealSource
import Hindman168.NativeOriginalPointWeakLimit

/-! The local law retained by the same-source selection gives weak convergence
of the ACTUAL original joint integer point orbit, with the same H, period,
rational representatives and curve. No new extraction is performed. -/
namespace Hindman168
open Filter MeasureTheory
open scoped Manifold ContDiff Topology
universe u
attribute [local instance] alignmentAddingPairFintype lieGroup_smooth_min_three

variable {ι : Type} [Fintype ι] {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))

theorem alignment_original_joint_point_mixture_weak_limit
    (F : MasterParameterFamily) (q₀ : ℕ) (targets : ι → Finset (Fin N))
    (w : ℕ → ℕ) (y : ℕ → Fin N → ℕ) (p : ℕ → ℤ)
    (shift : ℕ → ι → AlignmentAddingPair N i → ℤ) (g a : ∀ _m : ℕ, ∀ ν, (D ν).G)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    {ℓ : ℕ} (H : NativeRationalSubgroupFiltration
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))) ℓ)
    (M : ℕ) (hM : 0 < M)
    (sigma : Fin M → (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G)
    (hRat : ∀ r, sigma r ∈ nativeSubgroupRationalHull
      (E := (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).E)
      (I := (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).I)
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).Γ)
    (h : ℝ → (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G)
    (hh : Continuous h)
    (hlaw : NativeResidueLocalHaarLaw
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))) H L
      (fun m => alignmentOriginalJointRealSource D n v hv F q₀ (w m) targets (y m)
        (p m) (shift m) (g m) (a m)) M hM sigma hRat h) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI : MeasurableSpace J.G := borel J.G
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI : BorelSpace (J.G ⧸ J.Γ) := native_nilmanifold_metric_coset_borel J
    Tendsto (fun m => finiteEmpiricalProbability (Finset.Ico 0 ⌊L m⌋)
      (fun z => (alignmentOriginalJointPointOrbit D n v hv F q₀ (w m) targets (y m)
        (p m) (shift m) (g m) (a m) z : J.G ⧸ J.Γ)) (1 : J.G)) atTop
      (𝓝 (nativePointMixtureProbability J H M hM sigma hRat h hh)) := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI : MeasurableSpace J.G := borel J.G
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : BorelSpace (J.G ⧸ J.Γ) := native_nilmanifold_metric_coset_borel J
  simpa only [alignment_original_joint_real_source_integer] using
    native_original_point_weak_limit J H L hL
      (fun m => alignmentOriginalJointRealSource D n v hv F q₀ (w m) targets (y m)
        (p m) (shift m) (g m) (a m)) M hM sigma hRat h hh hlaw

end Hindman168
