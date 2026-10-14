import Hindman168.RoughNativeFixedKernel
import Mathlib.Data.Int.ModEq

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]

attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_exponential_integer_period (Γ : Subgroup G) (V : E)
    (K : ℕ) (hK : nativeLieExponential (I := I) (G := G) ((K : ℝ) • V) ∈ Γ)
    (j z : ℤ) :
    (QuotientGroup.mk (nativeLieExponential (I := I) (G := G)
      (((j + (K : ℤ) * z : ℤ) : ℝ) • V)) : G ⧸ Γ) =
        QuotientGroup.mk (nativeLieExponential (I := I) (G := G) ((j : ℝ) • V)) := by
  let exp : E → G := fun v => nativeLieExponential (I := I) (G := G) v
  have hp : exp ((((K : ℤ) * z : ℤ) : ℝ) • V) = exp ((K : ℝ) • V) ^ z := by
    calc
      _ = exp ((z : ℝ) • ((K : ℝ) • V)) := by
        congr 1
        simp only [Int.cast_mul, Int.cast_natCast, smul_smul]
        rw [mul_comm]
      _ = _ := nativeLieExponential_int_smul (I := I) (G := G) ((K : ℝ) • V) z
  have he : exp (((j + (K : ℤ) * z : ℤ) : ℝ) • V) =
      exp ((j : ℝ) • V) * exp ((K : ℝ) • V) ^ z := by
    calc
      _ = exp ((j : ℝ) • V) * exp ((((K : ℤ) * z : ℤ) : ℝ) • V) := by
        rw [Int.cast_add]
        exact nativeLieExponential_add_smul (I := I) (G := G) V
          (j : ℝ) (((K : ℤ) * z : ℤ) : ℝ)
      _ = _ := congrArg (fun g : G => exp ((j : ℝ) • V) * g) hp
  apply Eq.symm
  apply QuotientGroup.eq.mpr
  change (exp ((j : ℝ) • V))⁻¹ * exp (((j + (K : ℤ) * z : ℤ) : ℝ) • V) ∈ Γ
  rw [he, inv_mul_cancel_left]
  exact Γ.zpow_mem hK z

theorem rough_native_exponential_residue (Γ : Subgroup G) (V : E)
    (K : ℕ) (hK : nativeLieExponential (I := I) (G := G) ((K : ℝ) • V) ∈ Γ)
    (n : ℤ) :
    (QuotientGroup.mk (nativeLieExponential (I := I) (G := G) ((n : ℝ) • V)) : G ⧸ Γ) =
      QuotientGroup.mk (nativeLieExponential (I := I) (G := G) (((n % (K : ℤ) : ℤ) : ℝ) • V)) := by
  have h := rough_native_exponential_integer_period (I := I) Γ V K hK
    (n % (K : ℤ)) (n / (K : ℤ))
  simpa only [Int.emod_add_mul_ediv] using h

theorem rough_native_exponential_modEq (Γ : Subgroup G) (V : E)
    (K : ℕ) (hK : nativeLieExponential (I := I) (G := G) ((K : ℝ) • V) ∈ Γ)
    (n j : ℤ) (h : Int.ModEq (K : ℤ) n j) :
    (QuotientGroup.mk (nativeLieExponential (I := I) (G := G) ((n : ℝ) • V)) : G ⧸ Γ) =
      QuotientGroup.mk (nativeLieExponential (I := I) (G := G) ((j : ℝ) • V)) := by
  calc
    _ = QuotientGroup.mk (nativeLieExponential (I := I) (G := G)
        (((n % (K : ℤ) : ℤ) : ℝ) • V)) := rough_native_exponential_residue Γ V K hK n
    _ = QuotientGroup.mk (nativeLieExponential (I := I) (G := G)
        (((j % (K : ℤ) : ℤ) : ℝ) • V)) := congrArg
          (fun r : ℤ => (QuotientGroup.mk (nativeLieExponential (I := I) (G := G)
            ((r : ℝ) • V)) : G ⧸ Γ)) h
    _ = _ := (rough_native_exponential_residue Γ V K hK j).symm

theorem rough_native_exponential_finite_representative (Γ : Subgroup G) (V : E)
    (K : ℕ) (hpos : 0 < K)
    (hK : nativeLieExponential (I := I) (G := G) ((K : ℝ) • V) ∈ Γ) (n : ℤ) :
    ∃ j : ℤ, 0 ≤ j ∧ j < (K : ℤ) ∧
      (QuotientGroup.mk (nativeLieExponential (I := I) (G := G) ((n : ℝ) • V)) : G ⧸ Γ) =
        QuotientGroup.mk (nativeLieExponential (I := I) (G := G) ((j : ℝ) • V)) := by
  have hpos' : (0 : ℤ) < K := by exact_mod_cast hpos
  exact ⟨n % (K : ℤ), Int.emod_nonneg _ (ne_of_gt hpos'),
    Int.emod_lt_of_pos _ hpos', rough_native_exponential_residue Γ V K hK n⟩

end Hindman168
