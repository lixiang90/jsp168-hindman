import Hindman168.UniformIntervalPairHaar
import Hindman168.IntegerPredictionShortCubeStatistic
import Hindman168.SingleCubeVertexTransport

namespace Hindman168
open FiniteMass
open scoped BigOperators Classical

theorem booleanCube_product_finset (d : ℕ) (P y : ℤ) (f : ℤ → ℝ)
    (v : Fin d → ℤ × ℤ) :
    (∏ η : Fin d → Bool, f (y + P * ∑ j, if η j then (v j).2 - (v j).1 else 0)) =
      ∏ S : Finset (Fin d), f (y + P * ∑ j ∈ S, ((v j).2 - (v j).1)) := by
  symm
  apply Fintype.prod_equiv (cubeSubsetBoolEquiv d)
  intro S
  change f (y + P * ∑ j ∈ S, ((v j).2 - (v j).1)) =
    f (y + P * ∑ j, if decide (j ∈ S) then (v j).2 - (v j).1 else 0)
  simp only [decide_eq_true_eq]
  rw [← Finset.sum_filter]
  simp

theorem integerPredictionShortCubeStatistic_pair_law {n : ℕ}
    (w M R X d J : ℕ) (pol : MvPolynomial (Fin n) ℤ) (f : ℤ → ℝ) (x : Fin n → ℕ) :
    integerPredictionShortCubeStatistic w M R X d J pol f x =
      expectation (piMass (fun _ : Fin d => tensor
        (uniformIntervalMass 0 (R / (predictionCubeModulus w M pol x).natAbs / J))
        (uniformIntervalMass 0 (R / (predictionCubeModulus w M pol x).natAbs / J))))
        (fun v => expectation (integerMass X (primorial w)) (fun y =>
          ∏ η : Fin d → Bool, f (y + ((predictionCubeModulus w M pol x).natAbs : ℤ) *
            ∑ j, if η j then (v j).2 - (v j).1 else 0))) := by
  rw [expectation_comm]
  simp_rw [booleanCube_product_finset, uniformInterval_pair_expectation_haar]
  unfold integerPredictionShortCubeStatistic
  exact (expectation_eq_sum _ _ (integerMass_support_in_window X (primorial w))).symm

end Hindman168
