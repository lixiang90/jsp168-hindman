import Hindman168.PredictionOriginalMixedLaw
import Hindman168.FiniteConditionalJoint

/-! Exact transport between the original one-replica column law and one
harmonic root together with independent direction pairs. This does not
assume positive interval lengths or normalized comparison masses. -/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

noncomputable def singleCubeSampleColumns {d : ℕ} (y : ℤ) (v : Fin d → ℤ × ℤ) :
    ReplicaCubeColumn 1 d → ℤ
  | none => y
  | some (_, j, bit) => if bit then (v j).2 else (v j).1

noncomputable def singleCubeSamplingEquiv (d : ℕ) :
    (ReplicaCubeColumn 1 d → ℤ) ≃ (ℤ × (Fin d → ℤ × ℤ)) where
  toFun z := (z none, fun j => (z (some (0, j, false)), z (some (0, j, true))))
  invFun p := singleCubeSampleColumns p.1 p.2
  left_inv z := by
    funext col
    cases col with
    | none => rfl
    | some col =>
      rcases col with ⟨q, j, bit⟩
      have hq : q = 0 := Subsingleton.elim _ _
      subst q
      cases bit <;> rfl
  right_inv p := by
    apply Prod.ext
    · rfl
    · funext j; rfl

theorem singleCubeSamplingEquiv_law (d X W T : ℕ) :
    (piMass (predictionOriginalColumnMass X W (fun _ : Fin 1 × Fin d × Bool => 0) (fun _ => T))).mapDomain
      (singleCubeSamplingEquiv d) =
    tensor (integerMass X W) (piMass (fun _ : Fin d =>
      tensor (uniformIntervalMass 0 T) (uniformIntervalMass 0 T))) := by
  ext p
  rw [Finsupp.mapDomain_equiv_apply, piMass_apply, tensor_apply, piMass_apply]
  simp only [Fintype.prod_option, Fintype.prod_prod_type, singleCubeSamplingEquiv,
    predictionOriginalColumnMass]
  simp only [Fin.prod_univ_succ]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  congr 1
  apply Fintype.prod_congr
  intro j
  simp only [Fintype.prod_bool, tensor_apply]
  exact mul_comm _ _

theorem singleCube_original_expectation (d X W T : ℕ)
    (f : (ReplicaCubeColumn 1 d → ℤ) → ℝ) :
    expectation (piMass (predictionOriginalColumnMass X W (fun _ : Fin 1 × Fin d × Bool => 0) (fun _ => T))) f =
      expectation (integerMass X W) (fun y => expectation (piMass (fun _ : Fin d =>
        tensor (uniformIntervalMass 0 T) (uniformIntervalMass 0 T)))
        (fun v => f (singleCubeSampleColumns y v))) := by
  have he := congrArg (fun ρ => expectation ρ (fun p => f (singleCubeSampleColumns p.1 p.2)))
    (singleCubeSamplingEquiv_law d X W T)
  rw [expectation_push, expectation_tensor] at he
  have hs : (fun z => f (singleCubeSampleColumns ((singleCubeSamplingEquiv d) z).1
      ((singleCubeSamplingEquiv d) z).2)) = f := by
    funext z
    exact congrArg f ((singleCubeSamplingEquiv d).symm_apply_apply z)
  rwa [hs] at he

end Hindman168
