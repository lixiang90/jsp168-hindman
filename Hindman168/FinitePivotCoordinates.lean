import Hindman168.FiniteConditionalJoint

/-!
# Extract exactly one independent direction coordinate

The explicit split preserves the actual coefficient product. All other
coordinates stay in the outside law. A pair of copies can subsequently
be marginalized only when its discarded component has total mass one.
-/

namespace Hindman168.FiniteMass

open scoped BigOperators Classical

noncomputable def insertPivotCoordinate {ι α : Type*} (k : ι)
    (rest : {i : ι // i ≠ k} → α) (value : α) (i : ι) : α :=
  if hi : i = k then value else rest ⟨i, hi⟩

noncomputable def pivotCoordinateEquiv {ι α : Type*} (k : ι) :
    (ι → α) ≃ (({i : ι // i ≠ k} → α) × α) where
  toFun x := (fun i => x i.val, x k)
  invFun p := insertPivotCoordinate k p.1 p.2
  left_inv x := by
    funext i
    by_cases hi : i = k <;> simp [insertPivotCoordinate, hi]
  right_inv p := by
    apply Prod.ext
    · funext i
      simp only [insertPivotCoordinate, dif_neg i.property]
    · simp [insertPivotCoordinate]

theorem insertPivotCoordinate_self {ι α : Type*} (k : ι)
    (rest : {i : ι // i ≠ k} → α) (value : α) :
    insertPivotCoordinate k rest value k = value := by
  simp [insertPivotCoordinate]

theorem insertPivotCoordinate_rest {ι α : Type*} (k : ι)
    (rest : {i : ι // i ≠ k} → α) (value : α) :
    (fun i : {i : ι // i ≠ k} => insertPivotCoordinate k rest value i.val) = rest := by
  funext i
  simp only [insertPivotCoordinate, dif_neg i.property]

theorem piMass_pivotCoordinate {ι α : Type*} [Fintype ι]
    (μ : ι → Mass α) (k : ι) :
    (piMass μ).mapDomain (pivotCoordinateEquiv k) =
      tensor (piMass (fun i : {i : ι // i ≠ k} => μ i.val)) (μ k) := by
  ext p
  rw [Finsupp.mapDomain_equiv_apply, piMass_apply, tensor_apply, piMass_apply]
  change (∏ i, μ i (insertPivotCoordinate k p.1 p.2 i)) =
    (∏ i : {i : ι // i ≠ k}, μ i.val (p.1 i)) * μ k p.2
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ k, insertPivotCoordinate_self]
  have hr : (∏ i : {i : ι // i ≠ k}, μ i.val (insertPivotCoordinate k p.1 p.2 i.val)) =
      ∏ i : {i : ι // i ≠ k}, μ i.val (p.1 i) := by
    apply Fintype.prod_congr
    intro i
    rw [congrFun (insertPivotCoordinate_rest k p.1 p.2) i]
  rw [hr, mul_comm]

theorem expectation_piMass_pivot {ι α : Type*} [Fintype ι]
    (μ : ι → Mass α) (k : ι) (f : (ι → α) → ℝ) :
    expectation (piMass μ) f =
      expectation (piMass (fun i : {i : ι // i ≠ k} => μ i.val))
        (fun rest => expectation (μ k) (fun value => f (insertPivotCoordinate k rest value))) := by
  let e : (ι → α) ≃ (({i : ι // i ≠ k} → α) × α) := pivotCoordinateEquiv k
  have he := congrArg (fun ρ => expectation ρ (fun p => f (e.symm p)))
    (piMass_pivotCoordinate μ k)
  rw [expectation_push, expectation_tensor] at he
  have hs : (fun x => f (e.symm ((pivotCoordinateEquiv k) x))) = f := by
    funext x
    exact congrArg f (e.symm_apply_apply x)
  rw [hs] at he
  exact he

theorem expectation_tensor_first {α : Type*} (μ : Mass α) (ht : total μ = 1)
    (f : α → ℝ) :
    expectation (tensor μ μ) (fun p => f p.1) = expectation μ f := by
  rw [expectation_tensor]
  simp only [expectation_const, ht, one_mul]

end Hindman168.FiniteMass
