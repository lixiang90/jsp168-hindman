import Hindman168.SelectedAlignmentNativeGoodCubeConvergence

/-! Every fixed accuracy in the countable good-condition family yields actual
mean comparison tending to zero. Endpoint/residue arrays may vary with m. -/
namespace Hindman168
open Filter
open scoped Manifold ContDiff BigOperators Classical Topology
universe u
attribute [local instance] alignmentAddingPairFintype lieGroup_smooth_min_three

variable {ι : Type} [Fintype ι] {κ : Type} [Fintype κ]
  {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))

theorem selected_alignment_native_good_projected_cube_means_tendsto
    (F : MasterParameterFamily) (gap : Fin N) (q₀ : ℕ) (T : Finset (Fin N)) (d : ℕ)
    (w : ℕ → ℕ) (y : ℕ → Fin N → ℕ)
    (shift : ℕ → ι → AlignmentAddingPair N i → ℤ) (g a : ∀ _m : ℕ, ∀ ν, (D ν).G)
    (B : ℝ) (L : NNReal) (c C : ℝ)
    (hgood : ∀ k : ℕ, ∀ᶠ m in atTop,
      ¬ selectedAlignmentNativeCompleteCubeAllFacesFailure (κ := κ) D n v hv F gap q₀ (w m) T d
        (shift m) (g m) (a m) B L c C (1/(k+1 : ℝ)) (y m)) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    ∀ weight : ι → κ → ℤ, (∀ ν j, weight ν j=0 ∨ weight ν j=1) →
    ∀ e : AlignmentAddingPair N i, e.targetTail=T → e.sourcePivot < gap → ∀ (j : κ)
      (lower upper : ℕ → Option κ → ℝ) (ellResidue : ℕ → Option κ → ℤ)
      (obs : C(J.G ⧸ J.Γ,ℂ)),
      (∀ᶠ m in atTop, ∀ z, |lower m z| ≤ C*alignmentLocalLength F (w m) i ∧
        |upper m z| ≤ C*alignmentLocalLength F (w m) i ∧
        c*alignmentLocalLength F (w m) i ≤ upper m z-lower m z) →
      obs ∈ boundedComplexLipschitzObservables (J.G ⧸ J.Γ) B L →
    Tendsto (fun m =>
      let p := alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap (w m) i.val) (F.modulus (w m)))
        (F.modulus (w m)) (y m i)
      finiteComplexSetMean (alignmentBoxClass (fun z => ⌈lower m z⌉) (fun z => ⌈upper m z⌉) (ellResidue m) d)
        (fun ell => obs (alignmentJointNativeCosetSlotTranslation D n v hv
          (fun ν => Pi.single e (weight ν j)) (nativeFinitePiCubeProjection (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)) (fun ν => alignmentBinaryCubeVertex (weight ν)) (fun V => (alignmentOriginalJointPointOrbit D n v hv F q₀ (w m) (fun _ => T) (y m) p (shift m) (g m) (a m)
          (ell none+∑ j ∈ V, ell (some j)) : J.G ⧸ J.Γ))))) -
      finiteComplexSetMean (alignmentBoxClass (fun z => ⌈lower m z⌉) (fun z => ⌈upper m z⌉) (ellResidue m) d)
        (fun ell => obs (nativeFinitePiCubeProjection (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)) (fun ν => alignmentBinaryCubeVertex (weight ν)) (fun V => (alignmentOriginalJointPointOrbit D n v hv F q₀ (w m) (fun _ => T) (y m) p (shift m) (g m) (a m)
          (ell none+∑ j ∈ V, ell (some j)) : J.G ⧸ J.Γ))))) atTop (𝓝 0) := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  intro weight hw e he hbefore j lower upper ellResidue obs hbox hobs
  have ht := selected_alignment_native_good_cube_means_tendsto D n v hv F gap q₀ T d w y shift g a B L c C hgood
    weight hw e he hbefore j lower upper ellResidue obs hbox hobs
  convert ht using 1
  funext m
  dsimp only
  rw [alignment_original_native_cube_projected_mean D n v hv F q₀ (w m) T (y m) _ _ d
      (ellResidue m) (lower m) (upper m) (shift m) weight hw (g m) (a m),
    alignment_original_native_cube_projected_mean D n v hv F q₀ (w m) T (y m) _ _ d
      (ellResidue m) (lower m) (upper m) (shift m) weight hw (g m) (a m)]

end Hindman168
