import Hindman168.AlignmentSelectedAllTargetsFaceHaar
import Hindman168.AlignmentRestrictedCubeSetwise

/-! Actual positive-event selection and one full-source extraction yield
both measure and setwise face symmetries for every target marginal. The
setwise assertion concerns the actual projection of the same full joint
cube orbit; no independent target filtration or Haar law is introduced. -/
namespace Hindman168
open Module Filter MeasureTheory FiniteMass
open scoped Manifold ContDiff BigOperators Classical Topology
universe u
attribute [local instance] alignmentAddingPairFintype lieGroup_smooth_min_three

variable {ι : Type} [Fintype ι]
  {κ : ℕ → Type} [∀ τ, Fintype (κ τ)] 
  {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν))) (index : ∀ τ, κ τ → ι)
  (r : ι → ℕ) (b : ∀ ν, Basis (Fin (r ν)) ℝ (alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)).E)

include n v hv r b in
theorem alignment_selected_all_targets_face_symmetries
    {k : ℕ} {A : Finset ℚ} {P₀ : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P₀ F)
    (q₀ : ℕ) (hq : 0 < q₀) (targets : ι → Finset (Fin N))
    (T : ℕ → Finset (Fin N)) (hTarget : ∀ τ, targets ∘ index τ = fun _ => T τ)
    (hT : ∀ τ j, j ∈ T τ → j < i)
    (shift : ℕ → ((Fin N → ℕ) × (Fin N → ℕ) × (Fin N → ℕ) × ℕ × ℕ) →
      ι → AlignmentAddingPair N i → ℤ)
    (g a : ∀ _w : ℕ,
      ∀ _key : ((Fin N → ℕ) × (Fin N → ℕ) × (Fin N → ℕ) × ℕ × ℕ), ∀ ν, (D ν).G)
    (W : ℕ → ℕ) (hW : Tendsto W atTop atTop)
    (S : ℕ → (Fin N → ℕ) → Prop) {β : ℝ} (hβ : 0 < β)
    (hS : ∀ᶠ j in atTop, β ≤ event (globalRawMass (F.cutoff (W j)) (primorial (W j)) N) (S j))
 :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI : MeasurableSpace J.G := borel J.G
    ∃ sample : ℕ → Fin N → ℕ,
      (∀ᶠ m in atTop, sample m ∈ (globalRawMass (F.cutoff (W m)) (primorial (W m)) N).support ∧ S m (sample m)) ∧
    let selectedShift := fun m ν => shift (W m) (alignmentShortExposureKey F (W m) i (targets ν) (sample m)) ν
    let selectedG := fun m ν => g (W m) (alignmentShortExposureKey F (W m) i (targets ν) (sample m)) ν
    let selectedA := fun m ν => a (W m) (alignmentShortExposureKey F (W m) i (targets ν) (sample m)) ν
    ∃ f : ℕ → ℕ, StrictMono f ∧
      ∃ H : NativeRationalSubgroupFiltration J s,
      (∀ k, H.layer k ≤ (nativeOriginalSubgroupLieFiltration J).layer k) ∧
      ∃ M : ℕ, ∃ hM : 0 < M, ∃ sigma : Fin M → J.G,
      ∃ hRat : ∀ r, sigma r ∈ nativeSubgroupRationalHull (E := J.E) (I := J.I) J.Γ,
      ∃ h : ℝ → J.G, ContMDiff 𝓘(ℝ) J.I ∞ h ∧
      NativeResidueLocalHaarLaw J H (fun m => (alignmentLocalLength F (W (f m)) i : ℝ))
        (fun m => alignmentOriginalJointRealSource D n v hv F q₀ (W (f m)) targets (sample (f m))
      (alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap (W (f m)) i.val) (F.modulus (W (f m))))
        (F.modulus (W (f m))) (sample (f m) i)) (selectedShift (f m)) (selectedG (f m)) (selectedA (f m))) M hM sigma hRat h ∧
      NativeCubeBoundedAlphaHaarLaw J H (fun m => (alignmentLocalLength F (W (f m)) i : ℝ))
        (fun m => alignmentOriginalJointRealSource D n v hv F q₀ (W (f m)) targets (sample (f m))
      (alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap (W (f m)) i.val) (F.modulus (W (f m))))
        (F.modulus (W (f m))) (sample (f m) i)) (selectedShift (f m)) (selectedG (f m)) (selectedA (f m))) M hM sigma hRat h ∧
      ∀ (τ : ℕ) (q : Fin (s+2)) (beta : ℝ) (residue : ℤ)
        (weight : κ τ → Fin q.val → ℤ), (∀ ν j, weight ν j=0 ∨ weight ν j=1) →
        ∀ e : AlignmentAddingPair N i, e.targetTail=T τ → ∀ j : Fin q.val,
      AlignmentRestrictedCubeHaarInvariant D n v hv (index τ) H
        (sigma (signedPeriodResidue M hM residue)) (hRat _) q.val (h beta)
        (fun ν => alignmentBinaryCubeVertex (weight ν)) (fun ν => Pi.single e (weight ν j)) ∧
      (alignmentJointNativeCosetSlotTranslation (D ∘ index τ) (n ∘ index τ) (fun k => v (index τ k)) (fun k => hv (index τ k)) (fun ν => Pi.single e (weight ν j))) '' Set.range (nativeFinitePiRestrictedCubeProjection (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)) (index τ) (fun ν => alignmentBinaryCubeVertex (weight ν)) ∘ nativeResidueCubeOrbitMap J H (sigma (signedPeriodResidue M hM residue)) (hRat _) q.val (2^q.val-1) (nativeCubeVertexEnumeration q.val) (h beta)) =
        Set.range (nativeFinitePiRestrictedCubeProjection (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)) (index τ) (fun ν => alignmentBinaryCubeVertex (weight ν)) ∘ nativeResidueCubeOrbitMap J H (sigma (signedPeriodResidue M hM residue)) (hRat _) q.val (2^q.val-1) (nativeCubeVertexEnumeration q.val) (h beta)) := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI : MeasurableSpace J.G := borel J.G
  obtain ⟨sample,hs,f,hf,H,hle,M,hM,sigma,hRat,h,hh,hpoint,halpha,hinv⟩ :=
    alignment_selected_all_targets_face_haar D n v hv index r b hF q₀ hq targets T hTarget hT
      shift g a W hW S hβ hS
  refine ⟨sample,hs,f,hf,H,hle,M,hM,sigma,hRat,h,hh,hpoint,halpha,?_⟩
  intro τ q beta residue weight hw e he j
  have hm := hinv τ q beta residue weight hw e he j
  refine ⟨hm, ?_⟩
  exact alignment_restricted_cube_measure_symmetry_preserves_coset D n v hv (index τ)
    H (sigma (signedPeriodResidue M hM residue)) (hRat _) q.val (h beta)
    (fun ν => alignmentBinaryCubeVertex (weight ν)) (fun ν => Pi.single e (weight ν j)) hm

end Hindman168
