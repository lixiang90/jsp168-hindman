import Hindman168.AlignmentExposedJointEvaluation

/-! Actual integer spatial exponents on ALL coarse integer grids. Genuine
residue correction integrality, not real log-polynomiality, identifies the
original base and own-pair increment exponents. -/
namespace Hindman168
open scoped BigOperators Classical

def alignmentIntegerSpatialVertex {κ : Type*} [Fintype κ]
    (spatial : Option κ → ℤ) (weight : κ → ℤ) : ℤ :=
  spatial none+∑ j, weight j*spatial (some j)

noncomputable def alignmentIntegerSpatialBase {κ : Type*} [Fintype κ] {N : ℕ}
    (F : MasterParameterFamily) (q₀ w : ℕ) (i : Fin N) (T : Finset (Fin N)) (y : Fin N → ℕ)
    (shift : AlignmentAddingPair N i → ℤ) (weight : κ → ℤ) (spatial : Option κ → ℤ) : ℤ :=
  let M : ℕ := F.modulus w
  let Y : ℤ := (alignmentShortBinStart F w i T y : ℤ)/(M : ℤ)
  let tau : ℤ := alignmentNaturalBlockProduct y T
  let s := alignmentIntegerSlotShift (fun e => alignmentPairResidue q₀ w M e y) shift
  alignmentIntegerSpatialVertex spatial weight+Y+
    (alignmentPivotArrayResidue y T M (y i) 0+tau*s-
      alignmentPivotArrayResidue y T M (y i) s)/(M : ℤ)

theorem alignment_joint_integer_spatial_base_eval {κ : Type*} [Fintype κ] {N : ℕ}
    (F : MasterParameterFamily) (q₀ w : ℕ) (i : Fin N) (T : Finset (Fin N)) (y : Fin N → ℕ)
    (shift : AlignmentAddingPair N i → ℤ) (weight : κ → ℤ) (spatial : Option κ → ℤ) :
    MvPolynomial.eval (Sum.elim (fun j => (spatial j : ℝ)) (fun j => (y j : ℝ)))
      (alignmentExposedJointBasePolynomial F q₀ w i T y shift weight)=
      (alignmentIntegerSpatialBase F q₀ w i T y shift weight spatial : ℝ) := by
  let M : ℤ := F.modulus w
  let tau : ℤ := alignmentNaturalBlockProduct y T
  let s := alignmentIntegerSlotShift (fun e => alignmentPairResidue q₀ w (F.modulus w) e y) shift
  have hM : M ≠ 0 := by
    dsimp [M]
    exact_mod_cast (F.modulus w).pos.ne'
  have hk := alignment_cube_residue_correction_exact M tau (y i) s hM
  have hh := alignmentCubeBasePolynomial_integral_eval M
    ((alignmentShortBinStart F w i T y : ℤ)/M)
    (alignmentPivotArrayResidue y T (F.modulus w) (y i) 0)
    (alignmentPivotArrayResidue y T (F.modulus w) (y i) s) s
    (alignmentIntegerSpatialVertex spatial weight) tau _ hM
    (by simpa only [alignmentPivotArrayResidue,add_zero] using hk)
  unfold alignmentExposedJointBasePolynomial
  rw [alignmentJointBasePolynomial_eval]
  have hvertex : (spatial none : ℝ)+∑ j, (weight j : ℝ)*(spatial (some j) : ℝ)=
      (alignmentIntegerSpatialVertex spatial weight : ℝ) := by
    simp only [alignmentIntegerSpatialVertex,Int.cast_add,Int.cast_sum,Int.cast_mul]
  have htail : (∏ j ∈ T, (y j : ℝ))=(alignmentNaturalBlockProduct y T : ℝ) := by
    simp only [alignmentNaturalBlockProduct,Nat.cast_prod]
  rw [hvertex,htail]
  exact hh

theorem alignment_exposed_integer_spatial_base_eval {κ : Type*} [Fintype κ]
    {N k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F)
    (q₀ w : ℕ) (i : Fin N) (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i)
    (x y : Fin N → ℕ) (hx : ∀ j, Nat.Coprime (x j) (primorial w))
    (hy : ∀ j, Nat.Coprime (y j) (primorial w))
    (hkey : alignmentShortExposureKey F w i T x=alignmentShortExposureKey F w i T y)
    (shift : AlignmentAddingPair N i → ℤ) (weight : κ → ℤ) (spatial : Option κ → ℤ) :
    MvPolynomial.eval (Sum.elim (fun j => (spatial j : ℝ)) (fun j => (y j : ℝ)))
      (alignmentExposedJointBasePolynomial F q₀ w i T x shift weight)=
      (alignmentIntegerSpatialBase F q₀ w i T y shift weight spatial : ℝ) := by
  rw [←alignmentExposedJointBasePolynomial_frozen hF q₀ w i T hT hx hy hkey shift weight]
  exact alignment_joint_integer_spatial_base_eval F q₀ w i T y shift weight spatial

end Hindman168
