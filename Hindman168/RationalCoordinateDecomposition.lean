import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Tactic

/-! Rational components of finite real coordinate vectors. A Hamel basis
of the real scalar field over the rationals supplies projections. Every
finite coordinate vector uses only finitely many projections, and membership
in the real span of rational vectors is preserved by each projection. -/

noncomputable section
namespace Hindman168
open Set Submodule Module

variable {ι κ : Type*}

 def rationalCoordinateCast (ι : Type*) : (ι → ℚ) →ₗ[ℚ] (ι → ℝ) where
  toFun x j := (x j : ℝ)
  map_add' x y := by ext j; exact Rat.cast_add _ _
  map_smul' r x := by
    ext j
    change ((r * x j : ℚ) : ℝ) = (r : ℝ) * (x j : ℝ)
    exact Rat.cast_mul _ _

 def realRationalComponent (b : Basis κ ℚ ℝ) (k : κ) :
    (ι → ℝ) →ₗ[ℚ] (ι → ℚ) where
  toFun x j := b.repr (x j) k
  map_add' x y := by
    ext j
    change b.repr (x j + y j) k = b.repr (x j) k + b.repr (y j) k
    rw [map_add, Finsupp.add_apply]
  map_smul' r x := by
    ext j
    change b.repr (r • x j) k = r * b.repr (x j) k
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]

 def realSpanRationalCoordinates (U : Submodule ℚ (ι → ℚ)) : Submodule ℝ (ι → ℝ) :=
  span ℝ (rationalCoordinateCast ι '' (U : Set (ι → ℚ)))

 theorem realRationalComponent_smul_cast (b : Basis κ ℚ ℝ) (k : κ)
    (r : ℝ) (x : ι → ℚ) :
    realRationalComponent b k (r • rationalCoordinateCast ι x) = (b.repr r k) • x := by
  ext j
  change b.repr (r * (x j : ℝ)) k = b.repr r k * x j
  have he : r * (x j : ℝ) = (x j : ℚ) • r := by
    change r * (x j : ℝ) = (x j : ℝ) * r
    exact mul_comm _ _
  rw [he, map_smul, Finsupp.smul_apply]
  exact mul_comm _ _

 theorem realRationalComponent_mem (b : Basis κ ℚ ℝ) (k : κ)
    (U : Submodule ℚ (ι → ℚ)) {x : ι → ℝ} (hx : x ∈ realSpanRationalCoordinates U) :
    realRationalComponent b k x ∈ U := by
  let c : U → (ι → ℝ) := fun u => rationalCoordinateCast ι u.val
  have hr : range c = rationalCoordinateCast ι '' (U : Set (ι → ℚ)) := by
    ext y
    constructor
    · rintro ⟨u, rfl⟩; exact ⟨u.val, u.property, rfl⟩
    · rintro ⟨u, hu, rfl⟩; exact ⟨⟨u, hu⟩, rfl⟩
  have hs : (Finsupp.linearCombination ℝ c).range = realSpanRationalCoordinates U := by
    rw [Finsupp.range_linearCombination, hr]
    rfl
  have hm : x ∈ (Finsupp.linearCombination ℝ c).range := by rw [hs]; exact hx
  obtain ⟨l, hl⟩ := hm
  rw [← hl, Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  apply U.sum_mem
  intro u _
  change realRationalComponent b k (l u • rationalCoordinateCast ι u.val) ∈ U
  rw [realRationalComponent_smul_cast]
  exact U.smul_mem _ u.property

 def realRationalComponentSupport [Fintype ι] (b : Basis κ ℚ ℝ) (x : ι → ℝ) : Finset κ := by
  classical
  exact Finset.univ.biUnion (fun j => (b.repr (x j)).support)

 theorem realRationalComponent_reconstruct [Fintype ι] (b : Basis κ ℚ ℝ) (x : ι → ℝ) :
    (∑ k ∈ realRationalComponentSupport b x,
      b k • rationalCoordinateCast ι (realRationalComponent b k x)) = x := by
  classical
  ext j
  simp only [Finset.sum_apply, Pi.smul_apply]
  change (∑ k ∈ realRationalComponentSupport b x,
    b k * ((b.repr (x j) k : ℚ) : ℝ)) = x j
  have hsub : (b.repr (x j)).support ⊆ realRationalComponentSupport b x := by
    intro k hk
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hk⟩
  calc
    (∑ k ∈ realRationalComponentSupport b x, b k * ((b.repr (x j) k : ℚ) : ℝ)) =
        ∑ k ∈ realRationalComponentSupport b x, (b.repr (x j) k) • b k := by
      apply Finset.sum_congr rfl
      intro k _
      change b k * ((b.repr (x j) k : ℚ) : ℝ) = ((b.repr (x j) k : ℚ) : ℝ) * b k
      exact mul_comm _ _
    _ = ∑ k ∈ (b.repr (x j)).support, (b.repr (x j) k) • b k := by
      symm
      apply Finset.sum_subset hsub
      intro k _ hk
      rw [Finsupp.notMem_support_iff.mp hk, zero_smul]
    _ = x j := by
      simpa only [Finsupp.linearCombination_apply, Finsupp.sum] using b.linearCombination_repr (x j)

end Hindman168
