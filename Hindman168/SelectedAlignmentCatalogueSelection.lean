import Hindman168.SelectedAlignmentCatalogueLetters
import Hindman168.SelectedAlignmentSelectedCosets

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
  {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν))) 
  (r : ι → ℕ) (b : ∀ ν, Basis (Fin (r ν)) ℝ (alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)).E)

include n v hv r b in
theorem selected_alignment_selected_catalogue_cosets
    {k : ℕ} {A : Finset ℚ} {P₀ : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P₀ F) (gap : Fin N) (hgap : gap ≤ i)
    (q₀ : ℕ) (hq : 0 < q₀) (targets : ι → Finset (Fin N))
    (hTargets : ∀ ν j, j ∈ targets ν → j < gap)
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
      ∀ (beta : ℝ) (residue : ℤ),
        SelectedAlignmentCatalogueCosetSymmetry D n v hv targets gap.val H
          (sigma (signedPeriodResidue M hM residue)) (hRat _) (h beta) := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI : MeasurableSpace J.G := borel J.G
  let index := fun τ => alignmentDuplicatedTargetIndex i targets (alignmentDuplicatedTargetCode i τ)
  let T := fun τ => if ∀ j ∈ (alignmentDuplicatedTargetCode i τ).1.val, j < gap
    then (alignmentDuplicatedTargetCode i τ).1.val else ∅
  have ht : ∀ τ, targets ∘ index τ = fun _ => T τ := by
    intro τ
    funext ν
    have hν := congrFun (alignment_duplicated_target_uniform i targets
      (alignmentDuplicatedTargetCode i τ)) ν
    have hb : ∀ j ∈ (alignmentDuplicatedTargetCode i τ).1.val, j < gap := by
      intro j hj
      have hν' : targets (index τ ν) = (alignmentDuplicatedTargetCode i τ).1.val := hν
      exact hTargets (index τ ν) j (by rw [hν']; exact hj)
    simp only [T, if_pos hb]
    exact hν
  have hbefore : ∀ τ j, j ∈ T τ → j < gap := by
    intro τ j hj
    dsimp only [T] at hj
    split_ifs at hj with h
    · exact h j hj
    · exact (Finset.notMem_empty j hj).elim
  obtain ⟨sample,hs,f,hf,H,hle,M,hM,sigma,hRat,h,hh,hpoint,halpha,hinv⟩ :=
    selected_alignment_selected_all_targets_face_symmetries D n v hv index r b hF gap hgap q₀ hq targets T ht hbefore
      shift g a W hW S hβ hS
  refine ⟨sample,hs,f,hf,H,hle,M,hM,sigma,hRat,h,hh,hpoint,halpha,?_⟩
  intro beta residue τ q weight hw e hebefore he j
  have hebefore' : e.sourcePivot < gap := hebefore
  have hb : ∀ k ∈ (alignmentDuplicatedTargetCode i τ).1.val, k < gap := by
    intro k hk
    exact (e.target_before_sourcePivot k (by simpa only [he] using hk)).trans hebefore'
  have heT : e.targetTail = T τ := by simpa only [T, if_pos hb] using he
  exact hinv τ q beta residue weight hw e heT hebefore' j

end Hindman168
