import Hindman168.IntegerCubeCornerCoordinates
import Hindman168.FiniteHaarDirections
import Hindman168.SubgroupCubeAverage
import Mathlib.Data.ZMod.Basic

namespace Hindman168
open scoped BigOperators Classical

noncomputable def integerPeriodicCubeProduct (q d : ℕ) (f : ZMod q → ℝ)
    (p : ℤ × (Fin d → ℤ)) : ℝ :=
  ∏ ω : Finset (Fin d), f (integerCubeVertex p ω)

def integerCubeResidueShift (q d : ℕ) (r : ZMod q × (Fin d → ZMod q)) :
    ℤ × (Fin d → ℤ) := ((r.1.val : ℤ), fun j => (r.2 j).val)

theorem integerPeriodicCubeProduct_abs_le_one (q d : ℕ) (f : ZMod q → ℝ)
    (hf : ∀ x, |f x| ≤ 1) (p : ℤ × (Fin d → ℤ)) :
    |integerPeriodicCubeProduct q d f p| ≤ 1 := by
  rw [integerPeriodicCubeProduct, Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun _ _ => hf _)

theorem finiteCubeParameterMean_eq_top_cube {G : Type*} [AddCommGroup G] [Fintype G]
    (d : ℕ) (f : G → ℝ) :
    finiteHaarMean (fun p : G × (Fin d → G) =>
      ∏ ω : Finset (Fin d), f (p.1 + ∑ j ∈ ω, p.2 j)) =
        subgroupCubeAverage (⊤ : AddSubgroup G) d f := by
  rw [finiteHaarMean_prod]
  unfold subgroupCubeAverage
  congr 1
  funext x
  let e : (Fin d → (⊤ : AddSubgroup G)) ≃ (Fin d → G) :=
    Equiv.piCongrRight (fun _ => (AddSubgroup.topEquiv : (⊤ : AddSubgroup G) ≃+ G).toEquiv)
  exact (finiteHaarMean_equiv e
    (fun v => ∏ ω : Finset (Fin d), f (x + ∑ j ∈ ω, v j))).symm

/-- Averaging canonical residue translates of every integer cube
parameter produces exactly the cyclic cube mean at each parameter point. -/
theorem integerPeriodicCubeProduct_mean_residue_shift (q d : ℕ) [NeZero q]
    (f : ZMod q → ℝ) (p : ℤ × (Fin d → ℤ)) :
    finiteHaarMean (fun r : ZMod q × (Fin d → ZMod q) =>
      integerPeriodicCubeProduct q d f (p + integerCubeResidueShift q d r)) =
        subgroupCubeAverage (⊤ : AddSubgroup (ZMod q)) d f := by
  let F := fun z : ZMod q × (Fin d → ZMod q) =>
    ∏ ω : Finset (Fin d), f (z.1 + ∑ j ∈ ω, z.2 j)
  let s : ZMod q × (Fin d → ZMod q) := ((p.1 : ZMod q), fun j => (p.2 j : ZMod q))
  have he (r : ZMod q × (Fin d → ZMod q)) :
      integerPeriodicCubeProduct q d f (p + integerCubeResidueShift q d r) = F (s + r) := by
    apply Finset.prod_congr rfl
    intro ω _
    congr 1
    simp only [integerCubeVertex, integerCubeResidueShift, Prod.fst_add, Prod.snd_add,
      Pi.add_apply, s, Int.cast_add, Int.cast_sum, Int.cast_natCast,
      ZMod.natCast_zmod_val, Finset.sum_add_distrib]
  simp_rw [he]
  exact (finiteHaarMean_add_left F s).trans (finiteCubeParameterMean_eq_top_cube d f)

end Hindman168
