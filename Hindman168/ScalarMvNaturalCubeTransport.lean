import Hindman168.ScalarMvPolynomialInverse

namespace Hindman168
open scoped Classical

theorem scalar_mv_nat_cast_injective (κ : Type*) :
    Function.Injective (fun v : κ → ℕ => fun i => (v i : ℤ)) := by
  intro v w h
  funext i
  exact Int.ofNat_inj.mp (congrFun h i)

theorem scalar_mv_integer_cube_nat_cast_image (κ : Type*) [Fintype κ] (N : ℕ) :
    scalarMvIntegerCube κ N =
      (Fintype.piFinset (fun _ : κ => Finset.range N)).image (fun v : κ → ℕ => fun i => (v i : ℤ)) := by
  ext x
  simp only [scalarMvIntegerCube, Fintype.mem_piFinset, Finset.mem_Ico, Finset.mem_image,
    Finset.mem_range]
  constructor
  · intro hx
    let v : κ → ℕ := fun i => (x i).toNat
    have hv : ∀ i, (v i : ℤ) = x i := fun i => Int.toNat_of_nonneg (hx i).1
    refine ⟨v, ?_, funext hv⟩
    intro i
    have hi : (v i : ℤ) < (N : ℤ) := (hv i).trans_lt (hx i).2
    exact_mod_cast hi
  · rintro ⟨v, hv, rfl⟩ i
    change 0 ≤ (v i : ℤ) ∧ (v i : ℤ) < (N : ℤ)
    exact ⟨Int.natCast_nonneg _, by exact_mod_cast hv i⟩

theorem scalar_mv_integer_cube_natural_mean (κ : Type*) [Fintype κ] (N : ℕ)
    (f : (κ → ℤ) → ℂ) :
    finiteComplexSetMean (scalarMvIntegerCube κ N) f =
      finiteComplexSetMean (Fintype.piFinset (fun _ : κ => Finset.range N))
        (fun v : κ → ℕ => f (fun i => (v i : ℤ))) := by
  rw [scalar_mv_integer_cube_nat_cast_image,
    finiteComplexSetMean_image _ _ (scalar_mv_nat_cast_injective κ)]

end Hindman168
