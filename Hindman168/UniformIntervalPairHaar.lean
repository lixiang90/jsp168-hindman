import Hindman168.UniformIntervals
import Hindman168.CoordinateLists
import Hindman168.FiniteProductExpectations
import Hindman168.FiniteHaarDirections
import Hindman168.FiniteWeightedCauchySchwarz

/-! Exact identification of paired uniform integer interval samples with
two independent finite counting averages, including zero interval length. -/

namespace Hindman168
open FiniteMass
open scoped BigOperators Classical

theorem uniformFinite_expectation_haar {α : Type*} [Fintype α] (f : α → ℝ) :
    expectation (uniformFinsetMass (Finset.univ : Finset α)) f = finiteHaarMean f := by
  rw [expectation_eq_sum _ _ (Finset.subset_univ _)]
  simp only [uniformFinsetMass, flatMass_apply, Finset.mem_univ, if_true,
    Finset.card_univ, ← Finset.mul_sum, finiteHaarMean, div_eq_mul_inv]
  exact mul_comm _ _

theorem uniformFinite_pi_law {ι α : Type*} [Fintype ι] [Fintype α] :
    piMass (fun _ : ι => uniformFinsetMass (Finset.univ : Finset α)) =
      uniformFinsetMass (Finset.univ : Finset (ι → α)) := by
  ext x
  simp [piMass_apply, uniformFinsetMass, flatMass_apply, Fintype.card_pi,
    Finset.prod_inv_distrib]

theorem uniformFinite_tensor_law {α β : Type*} [Fintype α] [Fintype β] :
    tensor (uniformFinsetMass (Finset.univ : Finset α))
      (uniformFinsetMass (Finset.univ : Finset β)) =
      uniformFinsetMass (Finset.univ : Finset (α × β)) := by
  ext x
  simp [tensor_apply, uniformFinsetMass, flatMass_apply, Fintype.card_prod, mul_comm]

theorem uniformFin_cast_interval_law (T : ℕ) :
    (uniformFinsetMass (Finset.univ : Finset (Fin T))).mapDomain
      (fun j => (j.val : ℤ)) = uniformIntervalMass 0 T := by
  classical
  letI : DecidableEq ℤ := Classical.decEq ℤ
  have hinj : Function.Injective (fun j : Fin T => (j.val : ℤ)) := by
    intro i j h
    exact Fin.ext (Int.ofNat_injective h)
  have himage : (Finset.univ : Finset (Fin T)).image (fun j => (j.val : ℤ)) =
      integerWindow 0 T := by
    ext z
    simp only [Finset.mem_image, Finset.mem_univ, true_and, integerWindow,
      zero_add, Finset.mem_Ico]
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨Int.natCast_nonneg _, by exact_mod_cast j.isLt⟩
    · intro hz
      have he : (z.toNat : ℤ) = z := (Int.eq_natCast_toNat.mpr hz.1).symm
      have ht : z.toNat < T := by
        have h := hz.2
        rw [← he] at h
        exact_mod_cast h
      exact ⟨⟨z.toNat, ht⟩, he⟩
  rw [uniformFinsetMass_push _ _ hinj]
  exact congrArg uniformFinsetMass himage

theorem uniformInterval_pair_expectation_haar (d T : ℕ)
    (f : (Fin d → ℤ × ℤ) → ℝ) :
    expectation (piMass (fun _ : Fin d => tensor
      (uniformIntervalMass 0 T) (uniformIntervalMass 0 T))) f =
      finiteHaarMean (fun u : Fin d → Fin T => finiteHaarMean
        (fun v : Fin d → Fin T => f (fun j => ((u j).val, (v j).val)))) := by
  classical
  let μ := uniformFinsetMass (Finset.univ : Finset (Fin T))
  let castPair : Fin T × Fin T → ℤ × ℤ := fun p => (p.1.val, p.2.val)
  have hpair : (tensor μ μ).mapDomain castPair =
      tensor (uniformIntervalMass 0 T) (uniformIntervalMass 0 T) := by
    exact (tensor_map μ μ (fun j : Fin T => (j.val : ℤ))
      (fun j : Fin T => (j.val : ℤ))).trans (by
        simp only [μ, uniformFin_cast_interval_law])
  have hmap := piMass_map (fun _ : Fin d => tensor μ μ) (fun _ => castPair)
  simp only [hpair] at hmap
  rw [← hmap, expectation_push]
  simp only [μ, uniformFinite_tensor_law, uniformFinite_pi_law, uniformFinite_expectation_haar]
  let E : (Fin d → Fin T × Fin T) ≃ ((Fin d → Fin T) × (Fin d → Fin T)) :=
    { toFun := fun p => (fun j => (p j).1, fun j => (p j).2)
      invFun := fun p j => (p.1 j, p.2 j)
      left_inv := fun p => by funext j; exact Prod.eta (p j)
      right_inv := fun p => rfl }
  have he := finiteHaarMean_equiv E
    (fun p => f (fun j => ((p.1 j).val, (p.2 j).val)))
  convert he.trans (finiteHaarMean_prod _) using 1
  congr 1
  exact Subsingleton.elim _ _

end Hindman168
