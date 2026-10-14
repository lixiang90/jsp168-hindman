import Hindman168.AlignmentNativeWindowSampling
import Hindman168.AlignmentDyadicExposureGeometry

/-! The actual other-factor values in the original residue windows give a
fixed normalized-scale range about the raw anchor. No coefficient or sampled
factor controls the range constant, and no gcd between factors is needed. -/
namespace Hindman168
open scoped BigOperators

theorem alignment_window_retained_products {n : ℕ} (x y : Fin n → ℕ)
    (T U : Finset (Fin n)) (hU : U ⊆ T) (modulus : ℕ)
    (hx : ∀ j ∈ U, 0 < x j)
    (hy : ∀ j ∈ U, y j ∈ binaryDyadicResidueWindow modulus (x j)) :
    0 < alignmentNaturalBlockProduct y U ∧
    alignmentNaturalBlockProduct y U ≤ 2^T.card*alignmentNaturalBlockProduct x U ∧
    alignmentNaturalBlockProduct x U ≤ 2^T.card*alignmentNaturalBlockProduct y U := by
  have hypos : ∀ j ∈ U, 0 < y j := by
    intro j hj
    have hh := hy j hj
    rw [binaryDyadicResidueWindow,mem_residueWindow] at hh
    have hp : (0 : ℝ) < (2 ^ Nat.log2 (x j) : ℕ) := by positivity
    have hr : (0 : ℝ) < y j := hp.trans_le hh.1
    exact_mod_cast hr
  have he : (∏ j ∈ U, 2 ^ Nat.log2 (y j) : ℕ)=(∏ j ∈ U, 2 ^ Nat.log2 (x j) : ℕ) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [((binaryDyadicResidueWindow_mem (hypos j hj)).mp (hy j hj)).1]
  have hxb := binaryDyadicProduct_bounds U x hx
  have hyb := binaryDyadicProduct_bounds U y hypos
  rw [he] at hyb
  have hpow : (2 : ℕ)^U.card ≤ 2^T.card :=
    Nat.pow_le_pow_right (by decide) (Finset.card_le_card hU)
  refine ⟨Finset.prod_pos hypos,?_,?_⟩
  · exact hyb.2.trans ((Nat.mul_le_mul_left _ hxb.1).trans
      (Nat.mul_le_mul_right _ hpow))
  · exact hxb.2.trans ((Nat.mul_le_mul_left _ hyb.1).trans
      (Nat.mul_le_mul_right _ hpow))

theorem alignment_window_retained_normalized_scale {n : ℕ} (x y : Fin n → ℕ)
    (T U : Finset (Fin n)) (hU : U ⊆ T) (modulus d : ℕ) (hd : 0 < d)
    (hx : ∀ j ∈ U, 0 < x j)
    (hy : ∀ j ∈ U, y j ∈ binaryDyadicResidueWindow modulus (x j))
    (Z : ℝ) (hZ : 0 ≤ Z) :
    let K : ℝ := 2^T.card
    Z/((d : ℝ)*alignmentNaturalBlockProduct x U*K) ≤
      Z/((d : ℝ)*alignmentNaturalBlockProduct y U) ∧
    Z/((d : ℝ)*alignmentNaturalBlockProduct y U) ≤
      K^2*(Z/((d : ℝ)*alignmentNaturalBlockProduct x U*K)) := by
  dsimp only
  have hh := alignment_window_retained_products x y T U hU modulus hx hy
  have hdx : (0 : ℝ) < (d : ℝ)*alignmentNaturalBlockProduct x U := by
    have hp : 0 < alignmentNaturalBlockProduct x U := Finset.prod_pos hx
    exact mul_pos (by exact_mod_cast hd) (by exact_mod_cast hp)
  have hdy : (0 : ℝ) < (d : ℝ)*alignmentNaturalBlockProduct y U :=
    mul_pos (by exact_mod_cast hd) (by exact_mod_cast hh.1)
  have hK : (0 : ℝ) < 2^T.card := by positivity
  have hhigh : (d : ℝ)*alignmentNaturalBlockProduct y U ≤
      (d : ℝ)*alignmentNaturalBlockProduct x U*2^T.card := by
    have hp : (alignmentNaturalBlockProduct y U : ℝ) ≤
        2^T.card*(alignmentNaturalBlockProduct x U : ℝ) := by exact_mod_cast hh.2.1
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hlow : (d : ℝ)*alignmentNaturalBlockProduct x U ≤
      (d : ℝ)*alignmentNaturalBlockProduct y U*2^T.card := by
    have hp : (alignmentNaturalBlockProduct x U : ℝ) ≤
        2^T.card*(alignmentNaturalBlockProduct y U : ℝ) := by exact_mod_cast hh.2.2
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  refine ⟨div_le_div_of_nonneg_left hZ hdy hhigh,?_⟩
  have hu : Z/((d : ℝ)*alignmentNaturalBlockProduct y U) ≤
      (2^T.card*Z)/((d : ℝ)*alignmentNaturalBlockProduct x U) := by
    apply (div_le_div_iff₀ hdy hdx).mpr
    nlinarith [mul_le_mul_of_nonneg_left hlow hZ]
  have he : (2^T.card*Z)/((d : ℝ)*alignmentNaturalBlockProduct x U) =
      ((2 : ℝ)^T.card)^2*(Z/((d : ℝ)*alignmentNaturalBlockProduct x U*2^T.card)) := by
    field_simp
  exact hu.trans_eq he

theorem alignment_cube_scale_exposure_eq {n : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (i : Fin n) (T : Finset (Fin n)) {x y : Fin n → ℕ}
    (hkey : alignmentShortExposureKey F w i T x=alignmentShortExposureKey F w i T y) :
    alignmentCubeScale F w i T x=alignmentCubeScale F w i T y := by
  unfold alignmentCubeScale alignmentShortBinVolume
  rw [alignmentShortExposureKey_lower_product F w i T hkey]

theorem alignment_raw_exposed_retained_normalized_scale {n k : ℕ}
    {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A P F) (w : ℕ) (i : Fin n)
    (T U : Finset (Fin n)) (hU : U ⊆ T) (d : ℕ) (hd : 0 < d)
    (x y : Fin n → ℕ)
    (hx : x ∈ (globalRawMass (F.cutoff w) (primorial w) n).support)
    (hy : y ∈ (globalRawMass (F.cutoff w) (primorial w) n).support)
    (hkey : alignmentShortExposureKey F w i T x=alignmentShortExposureKey F w i T y) :
    let K : ℝ := 2^T.card
    alignmentCubeScale F w i T x/((d : ℝ)*alignmentNaturalBlockProduct x U*K) ≤
      alignmentCubeScale F w i T y/((d : ℝ)*alignmentNaturalBlockProduct y U) ∧
    alignmentCubeScale F w i T y/((d : ℝ)*alignmentNaturalBlockProduct y U) ≤
      K^2*(alignmentCubeScale F w i T x/((d : ℝ)*alignmentNaturalBlockProduct x U*K)) := by
  dsimp only
  rw [←alignment_cube_scale_exposure_eq F w i T hkey]
  exact alignment_window_retained_normalized_scale x y T U hU
    ((F.modulus w : ℕ)*(primorial w)^w) d hd
    (fun j _ => alignmentGlobalRawMass_support_positive hF w x hx j)
    (fun j hj => alignment_shortExposure_tail_window F w i T hkey j (hU hj)
      (alignmentGlobalRawMass_support_positive hF w y hy j))
    (alignmentCubeScale F w i T x) (by unfold alignmentCubeScale; positivity)

end Hindman168
