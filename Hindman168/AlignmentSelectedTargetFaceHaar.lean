import Hindman168.AlignmentCommonSourceFaceHaar
import Hindman168.AlignmentAllCubeConditionsSelection

/-! Actual positive-event selection, followed by ONE common-source local-law
extraction, yields projected face Haar invariance for a fixed target family.
Neither good-condition avoidance nor the local Haar law is an input oracle. -/
namespace Hindman168
open Module Filter MeasureTheory FiniteMass
open scoped Manifold ContDiff BigOperators Classical Topology
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
theorem alignment_selected_target_face_haar
    {k : ℕ} {A : Finset ℚ} {P₀ : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P₀ F)
    (q₀ : ℕ) (hq : 0 < q₀) (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i)
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
    let selectedShift := fun m => shift (W m) (alignmentShortExposureKey F (W m) i T (sample m))
    let selectedG := fun m => g (W m) (alignmentShortExposureKey F (W m) i T (sample m))
    let selectedA := fun m => a (W m) (alignmentShortExposureKey F (W m) i T (sample m))
    ∃ f : ℕ → ℕ, StrictMono f ∧
      ∃ H : NativeRationalSubgroupFiltration J s,
      (∀ k, H.layer k ≤ (nativeOriginalSubgroupLieFiltration J).layer k) ∧
      ∃ M : ℕ, ∃ hM : 0 < M, ∃ sigma : Fin M → J.G,
      ∃ hRat : ∀ r, sigma r ∈ nativeSubgroupRationalHull (E := J.E) (I := J.I) J.Γ,
      ∃ h : ℝ → J.G, ContMDiff 𝓘(ℝ) J.I ∞ h ∧
      NativeResidueLocalHaarLaw J H (fun m => (alignmentLocalLength F (W (f m)) i : ℝ))
        (fun m => alignmentOriginalJointRealSource D n v hv F q₀ (W (f m)) (fun _ => T) (sample (f m))
      (alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap (W (f m)) i.val) (F.modulus (W (f m))))
        (F.modulus (W (f m))) (sample (f m) i)) (selectedShift (f m)) (selectedG (f m)) (selectedA (f m))) M hM sigma hRat h ∧
      NativeCubeBoundedAlphaHaarLaw J H (fun m => (alignmentLocalLength F (W (f m)) i : ℝ))
        (fun m => alignmentOriginalJointRealSource D n v hv F q₀ (W (f m)) (fun _ => T) (sample (f m))
      (alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap (W (f m)) i.val) (F.modulus (W (f m))))
        (F.modulus (W (f m))) (sample (f m) i)) (selectedShift (f m)) (selectedG (f m)) (selectedA (f m))) M hM sigma hRat h ∧
      ∀ (q : Fin (s+2)) (beta : ℝ) (residue : ℤ)
        (weight : ι → Fin q.val → ℤ), (∀ ν j, weight ν j=0 ∨ weight ν j=1) →
        ∀ e : AlignmentAddingPair N i, e.targetTail=T → ∀ j : Fin q.val,
      Measure.map (alignmentJointNativeCosetSlotTranslation D n v hv (fun ν => Pi.single e (weight ν j))) (Measure.map (nativeFinitePiCubeProjection (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)) (fun ν => alignmentBinaryCubeVertex (weight ν))) (nativeResidueCubeHaarImage J H (sigma (signedPeriodResidue M hM residue)) (hRat _) q.val (2^q.val-1) (nativeCubeVertexEnumeration q.val) (h beta))) =
        Measure.map (nativeFinitePiCubeProjection (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)) (fun ν => alignmentBinaryCubeVertex (weight ν))) (nativeResidueCubeHaarImage J H (sigma (signedPeriodResidue M hM residue)) (hRat _) q.val (2^q.val-1) (nativeCubeVertexEnumeration q.val) (h beta)) := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI : MeasurableSpace J.G := borel J.G
  obtain ⟨sample,hs,hgood⟩ := alignment_native_all_cube_conditions_supported_selection
    D n v hv r b hF q₀ hq T hT shift g a W hW S hβ hS
  refine ⟨sample,hs,?_⟩
  apply alignment_common_source_face_haar D n v hv F q₀ T W sample
    (fun m => shift (W m) (alignmentShortExposureKey F (W m) i T (sample m)))
    (fun m => g (W m) (alignmentShortExposureKey F (W m) i T (sample m)))
    (fun m => a (W m) (alignmentShortExposureKey F (W m) i T (sample m)))
    (alignment_local_length_cofinal hF i W hW)
  intro d t ht C c B K k
  obtain ⟨t',rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  exact hgood ⟨d,t',C,c,B,K,k⟩

end Hindman168
