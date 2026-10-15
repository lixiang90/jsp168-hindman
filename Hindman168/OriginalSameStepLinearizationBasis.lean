import Hindman168.OriginalSameStepLinearizationCalculus
import OAI.Combinatorics.Progressions.Linear.BasisGradedCoordinateBasis
import OAI.Combinatorics.Progressions.Linear.BoundedAdaptedBasis
import Mathlib.Data.Finsupp.Multiset
/-!
# Finite-dimensional first shifted polynomial ideals

Derived from OpenAI math, fixed commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`, Apache-2.0.
The complete upstream source remains under dependencies/openai-finite-szemeredi.
Upstream paths below are relative to lean/OAI/Combinatorics/Progressions:
- `Polynomial/ShiftedPolynomialBasis.lean`, lines 365–408.
- `Polynomial/ShiftedPolynomialBasis.lean`, lines 615–644.
- `Polynomial/RankPolynomialFactorization.lean`, lines 210–212.
- `Polynomial/RankPolynomialFactorization.lean`, lines 246–286.

Modifications: The declarations are moved to BasisTools; their field notation is made explicit and the local binder hF is renamed hlayers. The original Lie filtration, adapted Lie subalgebra and shifted ideal are reused unchanged.
No assumptions or mathematical conclusions are added or removed.
-/
namespace Hindman168.OriginalSameStepLinearization.BasisTools
open OAI.Erdos3 OAI.Erdos3.VectorPolynomial Module
section Basis
variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
 (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
 (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
include hlayers
theorem mem_layer_iff_basis_coordinates (j : ℕ) (v : L) :
    v ∈ F.layer j ↔ ∀ i, ¬ j ≤ ω i → b.repr v i = 0 := by
  rw [hlayers, basis_mem_span_image_iff]
  rfl

theorem adaptedSubmodule_eq_span_tensorBasis (w : σ → ℕ) :
    F.adaptedSubmodule w = Submodule.span ℚ
      (coefficientTensorBasis b '' {z : (σ →₀ ℕ) × ι | Finsupp.weight w z.1 ≤ ω z.2}) := by
  ext p
  change (∀ α, coefficients p α ∈ F.layer (Finsupp.weight w α)) ↔ _
  rw [basis_mem_span_image_iff]
  simp_rw [mem_layer_iff_basis_coordinates F b ω hlayers]
  constructor
  · intro h z hz
    rcases z with ⟨α, i⟩
    rw [coefficientTensorBasis_repr]
    exact h α i hz
  · intro h α i hi
    have hh := h (α, i) hi
    simpa only [coefficientTensorBasis_repr] using hh

noncomputable def adaptedMonomialBasis (w : σ → ℕ) :
    Basis {z : (σ →₀ ℕ) × ι // Finsupp.weight w z.1 ≤ ω z.2} ℚ (F.adaptedLieSubalgebra w) :=
  supportedSubmoduleBasis (coefficientTensorBasis b) (F.adaptedSubmodule w)
    {z | Finsupp.weight w z.1 ≤ ω z.2} (adaptedSubmodule_eq_span_tensorBasis F b ω hlayers w)

@[simp] theorem adaptedMonomialBasis_coe (w : σ → ℕ)
    (z : {z : (σ →₀ ℕ) × ι // Finsupp.weight w z.1 ≤ ω z.2}) :
    (adaptedMonomialBasis F b ω hlayers w z : VectorPolynomial σ ℚ L) =
      monomial z.val.1 (b z.val.2) := by
  exact (supportedSubmoduleBasis_coe (coefficientTensorBasis b) (F.adaptedSubmodule w)
    {z | Finsupp.weight w z.1 ≤ ω z.2}
    (adaptedSubmodule_eq_span_tensorBasis F b ω hlayers w) z).trans
      (coefficientTensorBasis_apply b _ _)

theorem adaptedMonomialBasis_repr (w : σ → ℕ) (p : F.adaptedLieSubalgebra w)
    (z : {z : (σ →₀ ℕ) × ι // Finsupp.weight w z.1 ≤ ω z.2}) :
    (adaptedMonomialBasis F b ω hlayers w).repr p z =
      b.repr (coefficients (p : VectorPolynomial σ ℚ L) z.val.1) z.val.2 := by
  exact (supportedSubmoduleBasis_repr (coefficientTensorBasis b) (F.adaptedSubmodule w)
    {z | Finsupp.weight w z.1 ≤ ω z.2}
    (adaptedSubmodule_eq_span_tensorBasis F b ω hlayers w) p z).trans
      (coefficientTensorBasis_repr b _ _ _)

theorem shiftedPolynomialIdeal_eq_span_monomialBasis (w : σ → ℕ) (k : ℕ) :
    (F.shiftedPolynomialIdeal w k).toSubmodule = Submodule.span ℚ
      (adaptedMonomialBasis F b ω hlayers w ''
        {z | Finsupp.weight w z.val.1 + k ≤ ω z.val.2}) := by
  ext p
  change (∀ α, coefficients (p : VectorPolynomial σ ℚ L) α ∈
    F.layer (Finsupp.weight w α + k)) ↔ _
  rw [basis_mem_span_image_iff]
  simp_rw [mem_layer_iff_basis_coordinates F b ω hlayers]
  constructor
  · intro h z hz
    rw [adaptedMonomialBasis_repr F]
    exact h z.val.1 z.val.2 hz
  · intro h α i hi
    by_cases hdeg : Finsupp.weight w α ≤ ω i
    · have hz := h ⟨(α, i), hdeg⟩ hi
      simpa only [adaptedMonomialBasis_repr F] using hz
    · exact (mem_layer_iff_basis_coordinates F b ω hlayers _ _).mp (p.property α) i hdeg

abbrev ShiftedMonomialIndex (w : σ → ℕ) (ω : ι → ℕ) (k : ℕ) :=
  {z : {z : (σ →₀ ℕ) × ι // Finsupp.weight w z.1 ≤ ω z.2} |
    Finsupp.weight w z.val.1 + k ≤ ω z.val.2}

noncomputable def shiftedMonomialBasis (w : σ → ℕ) (k : ℕ) :
    Basis (ShiftedMonomialIndex w ω k) ℚ (F.shiftedPolynomialIdeal w k) :=
  supportedSubmoduleBasis (adaptedMonomialBasis F b ω hlayers w)
    (F.shiftedPolynomialIdeal w k).toSubmodule
    {z | Finsupp.weight w z.val.1 + k ≤ ω z.val.2}
    (shiftedPolynomialIdeal_eq_span_monomialBasis F b ω hlayers w k)

end Basis
abbrev AdaptedBasisIndex {σ ι : Type*} (w : σ → ℕ) (ω : ι → ℕ) :=
  {z : (σ →₀ ℕ) × ι // Finsupp.weight w z.1 ≤ ω z.2}

section Dimension

variable {σ ι : Type*} (w : σ → ℕ) (ω : ι → ℕ) (s : ℕ)
  (hw : ∀ i, 0 < w i) (hω : ∀ i, ω i ≤ s)

include hw hω

theorem adaptedBasisIndex_degree_le (z : AdaptedBasisIndex w ω) :
    z.val.1.sum (fun _ n => n) ≤ s := by
  apply le_trans ?_ (z.property.trans (hω z.val.2))
  simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul]
  exact Finset.sum_le_sum (fun i _ => Nat.le_mul_of_pos_right _ (hw i))

noncomputable def adaptedBasisCode (z : AdaptedBasisIndex w ω) :
    (Σ n : Fin (s + 1), Fin n.val → σ) × ι :=
  (⟨⟨z.val.1.toMultiset.toList.length, by
      rw [Multiset.length_toList, Finsupp.card_toMultiset]
      exact Nat.lt_succ_of_le (adaptedBasisIndex_degree_le w ω s hw hω z)⟩,
    z.val.1.toMultiset.toList.get⟩, z.val.2)

theorem adaptedBasisCode_injective : Function.Injective (adaptedBasisCode w ω s hw hω) := by
  classical
  intro z u h
  have hi := congrArg (fun t : (Σ n : Fin (s + 1), Fin n.val → σ) × ι => t.2) h
  change z.val.2 = u.val.2 at hi
  have hl := congrArg (fun t : (Σ n : Fin (s + 1), Fin n.val → σ) × ι => List.ofFn t.1.2) h
  change List.ofFn z.val.1.toMultiset.toList.get = List.ofFn u.val.1.toMultiset.toList.get at hl
  rw [List.ofFn_get, List.ofFn_get] at hl
  have hm := congrArg (fun t : List σ => (t : Multiset σ)) hl
  rw [Multiset.coe_toList, Multiset.coe_toList] at hm
  apply Subtype.ext
  apply Prod.ext _ hi
  ext i
  have hh := congrArg (fun t : Multiset σ => t.count i) hm
  simpa only [Finsupp.count_toMultiset] using hh

variable [Fintype σ] [Fintype ι]

theorem adaptedBasisIndex_finite : Finite (AdaptedBasisIndex w ω) :=
  Finite.of_injective (adaptedBasisCode w ω s hw hω) (adaptedBasisCode_injective w ω s hw hω)


end Dimension
end Hindman168.OriginalSameStepLinearization.BasisTools
