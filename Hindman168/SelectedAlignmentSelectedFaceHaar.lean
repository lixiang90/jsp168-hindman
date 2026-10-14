import Hindman168.SelectedAlignmentAllTargetsCommonSourceFaceHaar
import Hindman168.SelectedAlignmentResidualGeometry
import Hindman168.SelectedAlignmentCubeConditionsSelection

/-! Actual positive-event selection for all target families followed by
ONE common-source extraction supplies all projected marginal face Haar
invariances. All witnesses belong to the same full heterogeneous source.
Numerical-condition avoidance, original-source identification, empirical
comparison, and the local Haar law are discharged by their constructions. -/
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
theorem selected_alignment_selected_all_targets_face_haar
    {k : ℕ} {A : Finset ℚ} {P₀ : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P₀ F) (gap : Fin N) (hgap : gap ≤ i)
    (q₀ : ℕ) (hq : 0 < q₀) (targets : ι → Finset (Fin N))
    (T : ℕ → Finset (Fin N)) (hTarget : ∀ τ, targets ∘ index τ = fun _ => T τ)
    (hT : ∀ τ j, j ∈ T τ → j < gap)
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
    let selectedShift := fun m ν => shift (W m) (alignmentShortExposureKey (alignmentGeometryWithGap F i gap) (W m) i (targets ν) (sample m)) ν
    let selectedG := fun m ν => g (W m) (alignmentShortExposureKey (alignmentGeometryWithGap F i gap) (W m) i (targets ν) (sample m)) ν
    let selectedA := fun m ν => a (W m) (alignmentShortExposureKey (alignmentGeometryWithGap F i gap) (W m) i (targets ν) (sample m)) ν
    ∃ f : ℕ → ℕ, StrictMono f ∧
      ∃ H : NativeRationalSubgroupFiltration J s,
      (∀ k, H.layer k ≤ (nativeOriginalSubgroupLieFiltration J).layer k) ∧
      ∃ M : ℕ, ∃ hM : 0 < M, ∃ sigma : Fin M → J.G,
      ∃ hRat : ∀ r, sigma r ∈ nativeSubgroupRationalHull (E := J.E) (I := J.I) J.Γ,
      ∃ h : ℝ → J.G, ContMDiff 𝓘(ℝ) J.I ∞ h ∧
      NativeResidueLocalHaarLaw J H (fun m => (alignmentLocalLength (alignmentGeometryWithGap F i gap) (W (f m)) i : ℝ))
        (fun m => alignmentOriginalJointRealSource D n v hv (alignmentGeometryWithGap F i gap) q₀ (W (f m)) targets (sample (f m))
      (alignmentMicrocellFirst (alignedSqrtMicrocellWidth ((alignmentGeometryWithGap F i gap).gap (W (f m)) i.val) (F.modulus (W (f m))))
        (F.modulus (W (f m))) (sample (f m) i)) (selectedShift (f m)) (selectedG (f m)) (selectedA (f m))) M hM sigma hRat h ∧
      NativeCubeBoundedAlphaHaarLaw J H (fun m => (alignmentLocalLength (alignmentGeometryWithGap F i gap) (W (f m)) i : ℝ))
        (fun m => alignmentOriginalJointRealSource D n v hv (alignmentGeometryWithGap F i gap) q₀ (W (f m)) targets (sample (f m))
      (alignmentMicrocellFirst (alignedSqrtMicrocellWidth ((alignmentGeometryWithGap F i gap).gap (W (f m)) i.val) (F.modulus (W (f m))))
        (F.modulus (W (f m))) (sample (f m) i)) (selectedShift (f m)) (selectedG (f m)) (selectedA (f m))) M hM sigma hRat h ∧
      ∀ (τ : ℕ) (q : Fin (s+2)) (beta : ℝ) (residue : ℤ)
        (weight : κ τ → Fin q.val → ℤ), (∀ ν j, weight ν j=0 ∨ weight ν j=1) →
        ∀ e : AlignmentAddingPair N i, e.targetTail=T τ → e.sourcePivot < gap → ∀ j : Fin q.val,
      AlignmentRestrictedCubeHaarInvariant D n v hv (index τ) H
        (sigma (signedPeriodResidue M hM residue)) (hRat _) q.val (h beta)
        (fun ν => alignmentBinaryCubeVertex (weight ν)) (fun ν => Pi.single e (weight ν j)) := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI : MeasurableSpace J.G := borel J.G
  obtain ⟨sample,hs,hgood⟩ := selected_alignment_all_targets_all_cube_conditions_supported_selection
    (fun τ => D ∘ index τ) (fun τ => n ∘ index τ)
    (fun τ k => v (index τ k)) (fun τ k => hv (index τ k))
    (fun τ k => r (index τ k)) (fun τ k => b (index τ k))
    hF gap hgap q₀ hq T hT
    (fun τ w key k => shift w key (index τ k))
    (fun τ w key k => g w key (index τ k))
    (fun τ w key k => a w key (index τ k)) W hW S hβ hS
  refine ⟨sample,hs,?_⟩
  apply selected_alignment_all_targets_common_source_face_haar D n v hv index (alignmentGeometryWithGap F i gap) gap q₀ targets T hTarget W sample
    (fun m ν => shift (W m) (alignmentShortExposureKey (alignmentGeometryWithGap F i gap) (W m) i (targets ν) (sample m)) ν)
    (fun m ν => g (W m) (alignmentShortExposureKey (alignmentGeometryWithGap F i gap) (W m) i (targets ν) (sample m)) ν)
    (fun m ν => a (W m) (alignmentShortExposureKey (alignmentGeometryWithGap F i gap) (W m) i (targets ν) (sample m)) ν)
    (by simpa only [alignmentGeometryWithGap_length] using alignment_local_length_cofinal hF gap W hW)
  intro τ d t ht C c B K k
  obtain ⟨t',rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  have hTargetPoint (ν : κ τ) : targets (index τ ν) = T τ := congrFun (hTarget τ) ν
  simpa only [hTargetPoint] using hgood τ ⟨d,t',C,c,B,K,k⟩

end Hindman168
