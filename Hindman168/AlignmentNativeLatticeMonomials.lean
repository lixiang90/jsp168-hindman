import Hindman168.NativeRationalExponentialSpan
import Hindman168.AlignmentLieArrayRestrictedSpan
import Hindman168.AlignmentLieArrayEvaluation

namespace Hindman168
open Set Submodule
open scoped Manifold ContDiff

variable {σ : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

open scoped TensorProduct

theorem alignmentNativeLatticeMonomials_span (Γ : Subgroup G)
    [CompactSpace (G ⧸ Γ)] :
    Submodule.span ℝ {x : alignmentLiePolynomialArrays σ ℝ (GroupLieAlgebra I G) |
      x.val ∈ alignmentLieArrayRestrictedGenerators
        (fun v => nativeLieExponential (I := I) (G := G) v ∈ Γ)} = ⊤ := by
  apply alignmentLiePolynomialArrays_restricted_span
  intro j
  exact nativeLieLowerCentralModel_exponential_span (E := E) (I := I) Γ j

omit [Module ℚ E] [FiniteDimensional ℝ E] [Group.IsNilpotent G]
  [ConnectedSpace G] [SimplyConnectedSpace G] in
theorem alignmentNativeMonomial_exponential (d : σ →₀ ℕ)
    (v : GroupLieAlgebra I G) (z : σ → ℤ) :
    nativeLieExponential (I := I) (G := G)
      (alignmentLieArrayEvaluation (fun j => (z j : ℝ))
        (MvPolynomial.monomial d 1 ⊗ₜ[ℝ] v)) =
      nativeLieExponential (I := I) (G := G) v ^ (d.prod (fun j n => z j ^ n)) := by
  rw [alignmentLieArrayEvaluation_monomial]
  have he : d.prod (fun j n => (z j : ℝ) ^ n) =
      ((d.prod (fun j n => z j ^ n) : ℤ) : ℝ) := by
    simp only [Int.cast_finsuppProd, Int.cast_pow]
  rw [he]
  exact nativeLieExponential_int_smul (E := E) (I := I) (G := G) v _

omit [Module ℚ E] [FiniteDimensional ℝ E] [Group.IsNilpotent G]
  [ConnectedSpace G] [SimplyConnectedSpace G] in
theorem alignmentNativeLatticeMonomial_all_integer_values (Γ : Subgroup G)
    (x : alignmentLiePolynomialArrays σ ℝ (GroupLieAlgebra I G))
    (hx : x.val ∈ alignmentLieArrayRestrictedGenerators
      (fun v => nativeLieExponential (I := I) (G := G) v ∈ Γ)) :
    ∀ z : σ → ℤ, nativeLieExponential (I := I) (G := G)
      (alignmentLiePolynomialArraysEvaluation (fun j => (z j : ℝ)) x) ∈ Γ := by
  obtain ⟨d, v, _, hv, he⟩ := hx
  intro z
  change nativeLieExponential (I := I) (G := G)
    (alignmentLieArrayEvaluation (fun j => (z j : ℝ)) x.val) ∈ Γ
  rw [he, alignmentNativeMonomial_exponential]
  exact Γ.zpow_mem hv _

theorem alignmentNativeAllIntegerLatticeCoefficients_span (Γ : Subgroup G)
    [CompactSpace (G ⧸ Γ)] :
    Submodule.span ℝ {x : alignmentLiePolynomialArrays σ ℝ (GroupLieAlgebra I G) |
      ∀ z : σ → ℤ, nativeLieExponential (I := I) (G := G)
        (alignmentLiePolynomialArraysEvaluation (fun j => (z j : ℝ)) x) ∈ Γ} = ⊤ := by
  apply top_unique
  rw [← alignmentNativeLatticeMonomials_span (σ := σ) (E := E) (I := I) Γ]
  exact Submodule.span_mono (fun x hx => alignmentNativeLatticeMonomial_all_integer_values Γ x hx)

end Hindman168

