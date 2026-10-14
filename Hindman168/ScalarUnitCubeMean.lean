import Hindman168.ScalarMvIntegerCube
import Hindman168.FiniteComplexSetMean

/-! Exact univariate interval/Unit-cube sampling, including empty intervals. -/
namespace Hindman168
open scoped Classical BigOperators

theorem scalar_unit_integer_cube_image (N : ℕ) :
    scalarMvIntegerCube Unit N = (Finset.Ico 0 (N : ℤ)).image (fun n => fun _ : Unit => n) := by
  ext x
  simp only [scalarMvIntegerCube,Fintype.mem_piFinset,Finset.mem_image]
  constructor
  · intro hx
    exact ⟨x (),hx (),by funext j; cases j; rfl⟩
  · rintro ⟨n,hn,rfl⟩ j
    exact hn

theorem scalar_unit_integer_cube_mean (N : ℕ) (f : (Unit → ℤ) → ℂ) :
    finiteComplexSetMean (scalarMvIntegerCube Unit N) f =
      finiteComplexSetMean (Finset.Ico 0 (N : ℤ)) (fun n => f (fun _ => n)) := by
  rw [scalar_unit_integer_cube_image]
  exact finiteComplexSetMean_image _ _ (fun _ _ h => congrFun h ()) f

end Hindman168
