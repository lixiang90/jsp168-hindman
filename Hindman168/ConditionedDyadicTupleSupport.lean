import Hindman168.MasterActualCellBessel

namespace Hindman168
open FiniteMass
open scoped Classical

/-- Every supported good tuple stays in the original common dyadic
prime pool and satisfies the original polynomial good event. -/
theorem conditioned_dyadic_tuple_support {n : ℕ} (P : DyadicPrimePool)
    (T : Finset (MvPolynomial (Fin n) ℤ)) (x : Fin n → ℕ)
    (hx : x ∈ (conditionMass (dyadicPoolTupleMass (fun _ : Fin n => P))
      (primeSampleGood T)).support) :
    (∀ i, x i ∈ primePool P.lower P.upper) ∧ primeSampleGood T x := by
  refine ⟨primeIndependentMass_support_pool (conditionMass_support _ _ hx), ?_⟩
  by_contra hn
  apply Finsupp.mem_support_iff.mp hx
  rw [conditionMass_apply, if_neg hn]

end Hindman168
