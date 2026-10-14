import Hindman168.CoordinateLists
import Hindman168.TailProducts

/-!
# Coordinate products have the verified harmonic tail law

No extra independence premise is introduced. Product laws are obtained
as pushforwards of the finite coordinate mass, then identified with the
recursive tail law used in the quantitative sampling estimates.
-/

namespace Hindman168

open scoped BigOperators Classical

theorem tensorList_raw_product (W : ℕ) (Xs : List ℕ) :
    (FiniteMass.tensorList (Xs.map (fun X => rawMass X W))).mapDomain List.prod =
      tailMass W Xs := by
  induction Xs with
  | nil => simp [FiniteMass.tensorList, tailMass]
  | cons X Xs ih =>
    simp only [List.map_cons, FiniteMass.tensorList, tailMass]
    rw [← Finsupp.mapDomain_comp]
    have h := congrArg (fun μ : FiniteMass.Mass (ℕ × ℕ) =>
      μ.mapDomain (fun p => p.1 * p.2))
      (FiniteMass.tensor_map (rawMass X W)
        (FiniteMass.tensorList (Xs.map (fun X => rawMass X W))) id List.prod)
    rw [← Finsupp.mapDomain_comp, Finsupp.mapDomain_id, ih] at h
    exact h.trans ((FiniteMass.tensor_mul_comm _ _).trans
      (FiniteMass.tensor_statistic _ _ (fun s n : ℕ => s * n)))

theorem piMass_raw_product {n : ℕ} (W : ℕ) (X : Fin n → ℕ) :
    (FiniteMass.piMass (fun i => rawMass (X i) W)).mapDomain (fun x => ∏ i, x i) =
      tailMass W (List.ofFn X) := by
  have h := congrArg (fun μ : FiniteMass.Mass (List ℕ) => μ.mapDomain List.prod)
    (FiniteMass.piMass_ofFn (fun i => rawMass (X i) W))
  rw [← Finsupp.mapDomain_comp] at h
  have hm : List.ofFn (fun i => rawMass (X i) W) =
      (List.ofFn X).map (fun n => rawMass n W) :=
    List.ofFn_comp' X (fun n => rawMass n W)
  rw [hm, tensorList_raw_product] at h
  exact (Finsupp.mapDomain_congr (fun x _ => (List.prod_ofFn (f := x)).symm)).trans h

/-- Any specified enumeration of a finite index family gives the same
product law. The equality itself has no normalization hypothesis. -/
theorem piMass_raw_product_equiv {ι : Type*} [Fintype ι] {n : ℕ}
    (e : Fin n ≃ ι) (W : ℕ) (X : ι → ℕ) :
    (FiniteMass.piMass (fun i => rawMass (X i) W)).mapDomain (fun x => ∏ i, x i) =
      tailMass W (List.ofFn (fun i => X (e i))) := by
  have h := congrArg (fun μ : FiniteMass.Mass (Fin n → ℕ) =>
    μ.mapDomain (fun x => ∏ i, x i))
    (FiniteMass.piMass_reindex (fun i => rawMass (X i) W) e)
  rw [← Finsupp.mapDomain_comp, piMass_raw_product] at h
  exact (Finsupp.mapDomain_congr (fun x _ =>
    Fintype.prod_equiv e.symm (fun i => x i) (fun k => x (e k))
      (fun i => by rw [e.apply_symm_apply]))).trans h

end Hindman168
