import Hindman168.NativeSequentialIntrinsicFactorization
import Hindman168.NilpotentUniformPowerCore
import Hindman168.SignedFallingPeriod

/-! Absorb only the FIXED binomial factorial into a fixed rational
generator. The original right factor at EVERY signed integer is exactly
its actual integer power. A finite original generator list has a TRUE
finite normal-core quotient relative to the ORIGINAL nonnormal lattice. -/
namespace Hindman168
open Set Subgroup
open scoped Manifold ContDiff BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRightFactorVector {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (a : NativeSequentialBinomialFactor D) : D.E :=
  (a.order.factorial : ℚ)⁻¹ • a.vector

noncomputable def nativeRightFactorGenerator {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (a : NativeSequentialBinomialFactor D) : D.G :=
  nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (nativeRightFactorVector D a)

theorem signed_falling_product_real_cast (j : ℕ) (b : ℤ) :
    (signedFallingProduct j b : ℝ) = ∏ r ∈ Finset.range j, ((b : ℝ)-(r : ℝ)) := by
  simp only [signedFallingProduct, Int.cast_prod, Int.cast_sub, Int.cast_natCast]

theorem adapted_taylor_binomial_eval_int_falling (j : ℕ) (b : ℤ) :
    MvPolynomial.eval (fun _ => (b : ℝ)) (adaptedTaylorBinomial j) =
      (j.factorial : ℝ)⁻¹ * (signedFallingProduct j b : ℝ) := by
  simp only [adaptedTaylorBinomial, map_mul, MvPolynomial.eval_C, map_prod, map_sub,
    MvPolynomial.eval_X, signed_falling_product_real_cast]

theorem native_right_factor_signed_integer_power {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (a : NativeSequentialBinomialFactor D) (n : ℕ) (b : ℤ) :
    nativeSequentialFactorRight D a n (b : ℝ) =
      nativeRightFactorGenerator D a ^ (a.integerCoefficient n * signedFallingProduct a.order b) := by
  have hv : ((a.integerCoefficient n : ℝ) *
      MvPolynomial.eval (fun _ => (b : ℝ)) (adaptedTaylorBinomial a.order)) • a.vector =
      ((a.integerCoefficient n * signedFallingProduct a.order b : ℤ) : ℝ) • nativeRightFactorVector D a := by
    rw [adapted_taylor_binomial_eval_int_falling, nativeRightFactorVector,
      ← Rat.cast_smul_eq_qsmul ℝ, smul_smul, Rat.cast_inv, Rat.cast_natCast, Int.cast_mul]
    congr 1
    ring
  exact (congrArg (fun v : D.E => nativeLieExponential (E := D.E) (I := D.I) (G := D.G) v) hv).trans
    (nativeLieExponential_int_smul (E := D.E) (I := D.I) (G := D.G) (nativeRightFactorVector D a) _)

theorem native_right_factor_generator_rational {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (a : NativeSequentialBinomialFactor D)
    (ha : a.vector ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ) :
    nativeRightFactorGenerator D a ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ := by
  apply (nativeSubgroupRationalHull_mem_iff (E := D.E) (I := D.I) D.Γ _).mpr
  rw [nativeRightFactorGenerator, nativeLieGlobalLogarithm_exponential]
  exact (nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ).smul_mem _ ha

noncomputable def nativeRightGeneratorGroup {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (as : List (NativeSequentialBinomialFactor D)) : Subgroup D.G :=
  Subgroup.closure (range (fun i : Fin as.length => nativeRightFactorGenerator D (as.get i)))

abbrev NativeRightCoreQuotient {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (as : List (NativeSequentialBinomialFactor D)) :=
  nativeRightGeneratorGroup D as ⧸ (D.Γ.subgroupOf (nativeRightGeneratorGroup D as)).normalCore

theorem native_right_generator_group_fg {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (as : List (NativeSequentialBinomialFactor D)) :
    (nativeRightGeneratorGroup D as).FG :=
  (Subgroup.fg_iff _).mpr ⟨_,rfl,Set.finite_range _⟩

theorem native_right_generator_group_rational {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (as : List (NativeSequentialBinomialFactor D))
    (hRat : ∀ a ∈ as, a.vector ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ) :
    nativeRightGeneratorGroup D as ≤ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ := by
  apply (Subgroup.closure_le (K := nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)).mpr
  rintro g ⟨i,rfl⟩
  exact native_right_factor_generator_rational D _ (hRat _ (List.get_mem as i))

theorem native_right_core_quotient_finite {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (as : List (NativeSequentialBinomialFactor D))
    (hRat : ∀ a ∈ as, a.vector ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ) :
    Finite (NativeRightCoreQuotient D as) := by
  have hFG := native_right_generator_group_fg D as
  letI : Group.FG (nativeRightGeneratorGroup D as) := (Group.fg_iff_subgroup_fg _).mpr hFG
  obtain ⟨N,hN,hpow⟩ := nativeSubgroupRationalHull_uniform_power_of_fg (E := D.E) (I := D.I)
    D.Γ (nativeRightGeneratorGroup D as) hFG (native_right_generator_group_rational D as hRat)
  exact nilpotent_fg_uniform_power_core_finite (D.Γ.subgroupOf (nativeRightGeneratorGroup D as)) N hN
    (fun g => hpow g.val g.property)

end Hindman168
