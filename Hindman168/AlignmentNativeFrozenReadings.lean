import Hindman168.AlignmentNativeArrayReadings
import Hindman168.AlignmentFrozenPieceReading
import Hindman168.AlignmentNativeArrayCosetTranslations

namespace Hindman168
open scoped Manifold ContDiff BigOperators TensorProduct

attribute [local instance] nativeFiniteProductTopologicalSpace nativeFiniteProductGroup
  nativeFiniteProductNormedAddCommGroup nativeFiniteProductNormedSpace
  nativeFiniteProductCompleteSpace nativeFiniteProductFiniteDimensional
  nativeFiniteProductT2Space nativeFiniteProductIsNilpotent nativeFiniteProductConnectedSpace
  nativeFiniteProductChartTopology nativeFiniteProductChartedSpace
  nativeFiniteProductLieGroup nativeFiniteProductBoundaryless lieGroup_smooth_min_three

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] alignmentAddingPairFintype

variable {n : ℕ} {i : Fin n}

noncomputable def alignmentTargetArrayCoefficients
    (Δ : AlignmentAddingPair n i → ℤ) (T : Finset (Fin n)) :
    AlignmentAddingPair n i → ℤ :=
  fun e => if e.targetTail = T then Δ e else 0

theorem alignmentTargetArrayCoefficients_sum
    (Δ : AlignmentAddingPair n i → ℤ) (T : Finset (Fin n))
    (z : AlignmentAddingPair n i → ℤ) :
    ∑ e, z e * alignmentTargetArrayCoefficients Δ T e =
      alignmentIntegerArrayProgression Δ T z := by
  unfold alignmentIntegerArrayProgression alignmentTargetArrayCoefficients
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> simp

variable (N : ℕ) (evals : Fin (N + 1) → AlignmentAddingPair n i → ℤ)
  (hinj : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) N evals))

theorem alignment_exposure_native_array_reading
    (Γ : Subgroup G)
    {d : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) {q₀ w : ℕ} (hq : 0 < q₀) (hw : q₀ + 1 ≤ w)
    (C : ℕ) (T : Finset (Fin n)) (hT : ∀ j ∈ T, j < i)
    (V U : Finset (AlignmentAddingPair n i → ℤ)) {x y : Fin n → ℕ}
    (hgood : alignmentExposureArrayStable F w i q₀ C T V U x)
    (hx : ∀ j, Nat.Coprime (x j) (primorial w)) (hy : ∀ j, Nat.Coprime (y j) (primorial w))
    (hcut : ∀ j, j < i → y j ≤ F.cutoff w j.val ^ 2)
    (hkey : alignmentShortExposureKey F w i T x = alignmentShortExposureKey F w i T y)
    (v : AlignmentAddingPair n i → ℤ) (hv : v ∈ V)
    (u : AlignmentAddingPair n i → ℤ) (hu : u ∈ U)
    (p0 ℓ : ℤ) (hp0 : Int.ModEq (F.modulus w : ℕ) p0 (y i))
    (hdist : |p0 + (F.modulus w : ℤ) * ℓ - y i| ≤
      (C * alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) : ℕ))
    (obs : ℕ → (ℤ × ℤ) → C(G ⧸ Γ, ℝ)) (g b : ℕ → (ℤ × ℤ) → G) :
    let ρ := fun e => alignmentPairResidue q₀ w (F.modulus w) e y
    let Δ := fun e => alignmentPairProgression q₀ w (F.modulus w) e y
    let label := (((alignmentNaturalBlockProduct x T * x i : ℕ) : ℤ) / (F.gap w i.val : ℤ),
      alignmentPivotArrayResidue x T (F.modulus w) (x i)
        (alignmentIntegerSlotShift (fun e => alignmentPairResidue q₀ w (F.modulus w) e x) v))
    piecewiseLinearNilsequence Γ F (fun _ => i) obs g b w
      (alignmentIntegerArrayArgument y (F.modulus w) ρ Δ T (p0 + (F.modulus w : ℤ) * ℓ) v u) =
      alignmentNativeArrayReading N evals hinj Γ (obs w label) u
        (alignmentNativeModelCosetOrbit N evals hinj Γ (g w label) (b w label)
          (((alignmentNaturalBlockProduct y T : ℤ) * (p0 + alignmentIntegerSlotShift ρ v)) / (F.modulus w : ℤ))
          (alignmentNaturalBlockProduct y T : ℤ)
          (alignmentTargetArrayCoefficients Δ T) ℓ) := by
  dsimp only
  rw [alignmentNativeArrayReading_modelOrbit, alignmentTargetArrayCoefficients_sum]
  exact alignment_exposure_frozen_piece_reading Γ hF hq hw i C T hT V U hgood
    hx hy hcut hkey v hv u hu p0 ℓ hp0 hdist obs g b

end Hindman168
