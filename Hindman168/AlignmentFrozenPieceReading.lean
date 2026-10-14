import Hindman168.AlignmentCanonicalArrayResidues
import Hindman168.NilSequenceTestingLimit

namespace Hindman168

theorem alignmentIntegerArrayArgument_progression_quotient {n : ℕ} {i : Fin n}
    (t : Fin n → ℕ) (M : ℕ) (hM : 0 < M) (ρ : AlignmentAddingPair n i → ℕ)
    (Δ : AlignmentAddingPair n i → ℤ) (T : Finset (Fin n))
    (p0 ℓ : ℤ) (v u : AlignmentAddingPair n i → ℤ) :
    alignmentIntegerArrayArgument t M ρ Δ T (p0 + (M : ℤ) * ℓ) v u / (M : ℤ) =
      ((alignmentNaturalBlockProduct t T : ℤ) * (p0 + alignmentIntegerSlotShift ρ v)) / (M : ℤ) +
        (alignmentNaturalBlockProduct t T : ℤ) * ℓ + alignmentIntegerArrayProgression Δ T u := by
  have hm : (M : ℤ) ≠ 0 := by exact_mod_cast hM.ne'
  have he : alignmentIntegerArrayArgument t M ρ Δ T (p0 + (M : ℤ) * ℓ) v u =
      (alignmentNaturalBlockProduct t T : ℤ) * (p0 + alignmentIntegerSlotShift ρ v) +
        (M : ℤ) * ((alignmentNaturalBlockProduct t T : ℤ) * ℓ + alignmentIntegerArrayProgression Δ T u) := by
    unfold alignmentIntegerArrayArgument
    ring
  rw [he, Int.add_mul_ediv_left _ _ hm]
  ring

theorem alignment_exposure_frozen_piece_reading
    {G : Type*} [Group G] (Γ : Subgroup G) [TopologicalSpace (G ⧸ Γ)]
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) {q₀ w : ℕ} (hq : 0 < q₀) (hw : q₀ + 1 ≤ w)
    (i : Fin n) (C : ℕ) (T : Finset (Fin n)) (hT : ∀ j ∈ T, j < i)
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
      obs w label ((g w label ^
        (((alignmentNaturalBlockProduct y T : ℤ) * (p0 + alignmentIntegerSlotShift ρ v)) / (F.modulus w : ℤ) +
          (alignmentNaturalBlockProduct y T : ℤ) * ℓ + alignmentIntegerArrayProgression Δ T u) * b w label : G ⧸ Γ)) := by
  have hp : Int.ModEq (F.modulus w : ℕ) (p0 + (F.modulus w : ℤ) * ℓ) (y i) := by
    change (p0 + (F.modulus w : ℤ) * ℓ) % (F.modulus w : ℤ) = (y i : ℤ) % (F.modulus w : ℤ)
    change p0 % (F.modulus w : ℤ) = (y i : ℤ) % (F.modulus w : ℤ) at hp0
    simpa only [Int.add_emod, Int.mul_emod, Int.emod_self, zero_mul, Int.zero_emod,
      add_zero, Int.emod_emod] using hp0
  have hpiece := alignment_exposure_canonical_piece hF hq hw i C T hT V U hgood hx hy hcut hkey
    v hv u hu (p0 + (F.modulus w : ℤ) * ℓ) hp hdist
  dsimp only
  unfold piecewiseLinearNilsequence
  rw [hpiece]
  unfold pieceLinearOrbit
  rw [alignmentIntegerArrayArgument_progression_quotient _ _ (F.modulus w).pos]

end Hindman168
