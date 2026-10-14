import Hindman168.FinitePivotCoordinates
import Hindman168.FiniteReplicaJointLaw
import Mathlib.Algebra.BigOperators.Option

namespace Hindman168.FiniteMass
open scoped BigOperators Classical

noncomputable def tailPivotCoordinateEquiv {κ α : Type*} :
    (Option κ → α) ≃ ((κ → α) × α) where
  toFun x := (fun k => x (some k), x none)
  invFun x k := match k with
    | none => x.2
    | some j => x.1 j
  left_inv x := by funext k; cases k <;> rfl
  right_inv x := rfl

theorem piMass_tailPivot {κ α : Type*} [Fintype κ] (μ : Option κ → Mass α) :
    (piMass μ).mapDomain tailPivotCoordinateEquiv =
      conditionalJoint (piMass (fun k => μ (some k))) (fun _ => μ none) := by
  ext x
  rw [Finsupp.mapDomain_equiv_apply, piMass_apply, conditionalJoint_apply, piMass_apply]
  simp only [Fintype.prod_option]
  exact mul_comm _ _

theorem piMass_select_tailPivot {ι κ α : Type*} [Fintype ι] [Fintype κ]
    (μ : ι → Mass α) (j : Option κ → ι) (hj : Function.Injective j)
    (ht : ∀ i, total (μ i) = 1) :
    (piMass μ).mapDomain (fun x => (fun k => x (j (some k)), x (j none))) =
      conditionalJoint (piMass (fun k => μ (j (some k)))) (fun _ => μ (j none)) := by
  have h := congrArg (fun ν : Mass (Option κ → α) => ν.mapDomain tailPivotCoordinateEquiv)
    (piMass_restrict μ j hj ht)
  rw [← Finsupp.mapDomain_comp, piMass_tailPivot] at h
  exact h

end Hindman168.FiniteMass
