import Hindman168.ScalarUnitCubeMean

/-! Exact NATURAL range / INTEGER interval / Unit cube means, including
empty ranges. This is literal sample transport, with no endpoint loss. -/
namespace Hindman168
open scoped Classical

theorem integer_interval_nat_range_image (N : ℕ) :
    Finset.Ico 0 (N : ℤ)=(Finset.range N).image (fun n : ℕ => (n : ℤ)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hx0,hxN⟩ := Finset.mem_Ico.mp hx
    refine Finset.mem_image.mpr ⟨x.toNat,Finset.mem_range.mpr ?_,Int.toNat_of_nonneg hx0⟩
    have hNat : (x.toNat : ℤ) < (N : ℤ) := by
      simpa only [Int.toNat_of_nonneg hx0] using hxN
    exact_mod_cast hNat
  · intro hx
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_Ico.mpr ⟨Int.natCast_nonneg n,by exact_mod_cast Finset.mem_range.mp hn⟩

theorem finite_complex_integer_interval_nat_mean (N : ℕ) (f : ℤ → ℂ) :
    finiteComplexSetMean (Finset.Ico 0 (N : ℤ)) f =
      finiteComplexSetMean (Finset.range N) (fun n => f (n : ℤ)) := by
  rw [integer_interval_nat_range_image]
  exact finiteComplexSetMean_image _ _ (fun _ _ h => by exact_mod_cast h) f

theorem scalar_unit_integer_cube_nat_mean (N : ℕ) (f : (Unit → ℤ) → ℂ) :
    finiteComplexSetMean (scalarMvIntegerCube Unit N) f =
      finiteComplexSetMean (Finset.range N) (fun n => f (fun _ => (n : ℤ))) := by
  rw [scalar_unit_integer_cube_mean,finite_complex_integer_interval_nat_mean]

end Hindman168
