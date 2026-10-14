import Hindman168.SingleCubeVertexTransport
import Hindman168.OriginalDualTemplates

/-! Exact factorization of a repeated Boolean cube as its root function
paired with the original nonempty-vertex dual test. No law normalization,
positive shift length or boundedness premise is required. -/

namespace Hindman168
open scoped BigOperators Classical
open FiniteMass

noncomputable def originalRepeatedDualInput (a d : ℕ) (g : ℤ → ℝ) : OriginalSingleDualInput a d where
  epsilon := fun _ => 1
  vertexTest := fun _ _ => g

noncomputable def cubeDirectionPairEquiv (d : ℕ) :
    (Fin d × Bool → ℤ) ≃ (Fin d → ℤ × ℤ) where
  toFun u := fun j => (u (j, false), u (j, true))
  invFun v := fun jb => if jb.2 then (v jb.1).2 else (v jb.1).1
  left_inv u := by funext jb; rcases jb with ⟨j, bit⟩; cases bit <;> rfl
  right_inv v := by funext j; rfl

theorem cubeDirectionPairEquiv_law (d T : ℕ) :
    (piMass (fun _ : Fin d × Bool => uniformIntervalMass 0 T)).mapDomain
      (cubeDirectionPairEquiv d) =
    piMass (fun _ : Fin d => tensor (uniformIntervalMass 0 T) (uniformIntervalMass 0 T)) := by
  ext v
  rw [Finsupp.mapDomain_equiv_apply, piMass_apply, piMass_apply, Fintype.prod_prod_type]
  apply Fintype.prod_congr
  intro j
  simp only [Fintype.prod_bool, cubeDirectionPairEquiv, tensor_apply]
  exact mul_comm _ _

theorem cubeDirectionPair_expectation (d T : ℕ) (f : (Fin d → ℤ × ℤ) → ℝ) :
    expectation (piMass (fun _ : Fin d × Bool => uniformIntervalMass 0 T))
      (fun u => f (cubeDirectionPairEquiv d u)) =
    expectation (piMass (fun _ : Fin d => tensor (uniformIntervalMass 0 T) (uniformIntervalMass 0 T))) f := by
  rw [← cubeDirectionPairEquiv_law, expectation_push]

theorem singleCube_bool_product_root_vertices {d : ℕ}
    (M : ℤ) (g : ℤ → ℝ) (y : ℤ) (v : Fin d → ℤ × ℤ) :
    (∏ η : Fin d → Bool, g (y + M * ∑ j, if η j then (v j).2 - (v j).1 else 0)) =
    g y * ∏ S : CubeVertex d, g (y + M * ∑ j ∈ S.val, ((v j).2 - (v j).1)) := by
  rw [← singleCube_bool_product, Fintype.prod_option, Fintype.prod_prod_type]
  simp only [Fin.prod_univ_succ, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  simp [replicaCubeEval_root, replicaCubeEval_vertex, singleCubeSampleColumns]


theorem predictionSingleDualTest_repeated_pair {α : Type*} (d : ℕ) (μ : Mass α)
    (T : α → ℕ) (M : α → ℤ) (g : ℤ → ℝ) (y : ℤ) :
    predictionSingleDualTest d μ (fun _ _ => 0) T M (fun _ => 1) (fun _ _ => g) y =
      expectation μ (fun x => expectation (piMass (fun _ : Fin d =>
        tensor (uniformIntervalMass 0 (T x)) (uniformIntervalMass 0 (T x))))
        (fun v => ∏ S : CubeVertex d, g (y + M x * ∑ j ∈ S.val, ((v j).2 - (v j).1)))) := by
  unfold predictionSingleDualTest
  simp only [one_mul]
  apply congrArg (expectation μ)
  funext x
  exact cubeDirectionPair_expectation d (T x) (fun v =>
    ∏ S : CubeVertex d, g (y + M x * ∑ j ∈ S.val, ((v j).2 - (v j).1)))

theorem prediction_repeated_dual_cube {α : Type*} (d : ℕ) (μ : Mass α) (ρ : Mass ℤ)
    (T : α → ℕ) (M : α → ℤ) (g : ℤ → ℝ) :
    expectation μ (fun x => expectation (piMass (fun _ : Fin d =>
      tensor (uniformIntervalMass 0 (T x)) (uniformIntervalMass 0 (T x))))
      (fun v => expectation ρ (fun y => ∏ η : Fin d → Bool,
        g (y + M x * ∑ j, if η j then (v j).2 - (v j).1 else 0)))) =
    expectation ρ (fun y => g y *
      predictionSingleDualTest d μ (fun _ _ => 0) T M (fun _ => 1) (fun _ _ => g) y) := by
  symm
  simp_rw [predictionSingleDualTest_repeated_pair, ← expectation_const_mul]
  rw [expectation_comm ρ μ]
  apply congrArg (expectation μ)
  funext x
  rw [expectation_comm]
  apply congrArg (expectation (piMass (fun _ : Fin d =>
    tensor (uniformIntervalMass 0 (T x)) (uniformIntervalMass 0 (T x)))))
  funext v
  apply congrArg (expectation ρ)
  funext y
  exact (singleCube_bool_product_root_vertices (M x) g y v).symm

theorem originalRepeatedDualInput_admissible {a d m : ℕ}
    (F : MasterParameterFamily) (C : ℕ → Chain m) (label : ℕ → Fin m) (w : ℕ)
    (g : ℤ → ℝ) (hg : ∀ y, |g y| ≤ 1 + masterPredictionBlockMask F C label w y) :
    (originalRepeatedDualInput a d g).Admissible F C label w := by
  exact ⟨fun _ => by norm_num [originalRepeatedDualInput], fun _ _ y => hg y⟩

theorem model_error_abs_bound {ρ model ν : ℝ}
    (hρ : 0 ≤ ρ ∧ ρ ≤ ν) (hmodel : 0 ≤ model ∧ model ≤ 1) :
    |ρ - model| ≤ 1 + ν := by
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

end Hindman168
