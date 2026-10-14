import Hindman168.AdditiveRowTerminalProducts

/-! Initial stages use exactly the original single direction samples. -/

namespace Hindman168.FiniteMass

open scoped BigOperators Classical

theorem piPairs_first_marginal {ι β : Type*} [Fintype ι] (ν : ι → Mass β)
    (ht : ∀ i, total (ν i) = 1) :
    (piMass (fun i => tensor (ν i) (ν i))).mapDomain (fun v i => (v i).1) = piMass ν := by
  rw [piMass_map]
  congr 1
  funext i
  rw [tensor_fst, ht i, one_smul]

theorem expectation_piPairs_first {ι β : Type*} [Fintype ι] (ν : ι → Mass β)
    (ht : ∀ i, total (ν i) = 1) (f : (ι → β) → ℝ) :
    expectation (piMass (fun i => tensor (ν i) (ν i))) (fun v => f (fun i => (v i).1)) =
      expectation (piMass ν) f := by
  rw [← expectation_push, piPairs_first_marginal ν ht]

end Hindman168.FiniteMass

namespace Hindman168.AdditiveRowData

open scoped BigOperators Classical
open FiniteMass

variable {b c : ℕ}

theorem orderedAverage_initial_single {α : Type*} (ρ : Mass α) (ν : α → Fin b → Mass ℤ)
    (ht : ∀ a i, total (ν a i) = 1) (D : α → AdditiveRowData b c) (z : α → Fin c → ℤ)
    (F Ω : α → ReplicaCubeRow b 1 → ℤ → ℝ) :
    orderedAverage ρ ν D z F Ω 0 =
      expectation ρ (fun a => expectation (piMass (ν a))
        (fun u => ∏ i : ReplicaCubeRow b 1,
          F a i ((D a).form i (fun j => z a j + ∑ k, u k * (D a).direction k j)))) := by
  unfold orderedAverage
  simp only [predictionDirectionPrefix_zero, eliminationIntegrand_empty]
  apply expectation_congr_support
  intro a _
  exact expectation_piPairs_first (ν a) (ht a)
    (fun u => ∏ i : ReplicaCubeRow b 1,
      F a i ((D a).form i (fun j => z a j + ∑ k, u k * (D a).direction k j)))

end Hindman168.AdditiveRowData
