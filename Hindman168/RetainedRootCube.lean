import Hindman168.CubeVertexFixingDirections

namespace Hindman168
open scoped BigOperators
variable {G : Type*} [AddCommGroup G] (Q : AddSubgroup G)

theorem retainedRootCubeProduct {d k : ℕ}
    (D : Fin k → Q →+ (G × (Fin d → Q)))
    (hD : ∀ j a, (D j a).1 = (a : G))
    (h : G → ℝ) (z : G × (Fin d → Q)) (v : Fin k → Q) :
    (∏ ω : Finset (Fin k), h ((z + ∑ j ∈ ω, D j (v j)).1)) =
      subgroupCubeProduct Q k h z.1 v := by
  unfold subgroupCubeProduct
  apply Finset.prod_congr rfl
  intro ω _
  congr 1
  change z.1 + (AddMonoidHom.fst G (Fin d → Q)) (∑ j ∈ ω, D j (v j)) = _
  rw [map_sum]
  change z.1 + ∑ j ∈ ω, (D j (v j)).1 = _
  simp only [hD]

theorem retainedRootCubeAverage [Fintype G] [Fintype Q] {d k : ℕ}
    (D : Fin k → Q →+ (G × (Fin d → Q)))
    (hD : ∀ j a, (D j a).1 = (a : G)) (h : G → ℝ) :
    finiteHaarMean (fun z : G × (Fin d → Q) => finiteHaarMean
      (fun v : Fin k → Q => ∏ ω : Finset (Fin k), h ((z + ∑ j ∈ ω, D j (v j)).1))) =
      subgroupCubeAverage Q k h := by
  simp only [retainedRootCubeProduct Q D hD]
  rw [finiteHaarMean_prod]
  simp only [finiteHaarMean_const, subgroupCubeAverage]

theorem rootResponseDirection_injective {d : ℕ} (D : Q →+ (G × (Fin d → Q)))
    (hD : ∀ a, (D a).1 = (a : G)) : Function.Injective D := by
  intro a b hab
  apply Subtype.ext
  simpa only [hD] using congrArg Prod.fst hab

theorem rootResponseDirection_haar [Fintype Q] {d : ℕ}
    (D : Q →+ (G × (Fin d → Q))) [Fintype D.range]
    (hD : ∀ a, (D a).1 = (a : G)) (f : D.range → ℝ) :
    finiteHaarMean (fun a : Q => f ⟨D a, ⟨a, rfl⟩⟩) = finiteHaarMean f := by
  let e : Q ≃ D.range := Equiv.ofInjective D (rootResponseDirection_injective Q D hD)
  exact finiteHaarMean_equiv e f

theorem retainedRootImageCubeAverage [Fintype G] [Fintype Q] {d k : ℕ}
    (D : Fin k → Q →+ (G × (Fin d → Q))) [∀ j, Fintype (D j).range]
    (hD : ∀ j a, (D j a).1 = (a : G)) (h : G → ℝ) :
    finiteHaarMean (fun z : G × (Fin d → Q) => finiteHaarMean
      (fun v : (j : Fin k) → (D j).range =>
        ∏ ω : Finset (Fin k), h ((z + ∑ j ∈ ω, (v j : G × (Fin d → Q))).1))) =
      subgroupCubeAverage Q k h := by
  let e : (Fin k → Q) ≃ ((j : Fin k) → (D j).range) := Equiv.piCongrRight
    (fun j => Equiv.ofInjective (D j) (rootResponseDirection_injective Q (D j) (hD j)))
  calc
    _ = finiteHaarMean (fun z : G × (Fin d → Q) => finiteHaarMean
        (fun v : Fin k → Q => ∏ ω : Finset (Fin k), h ((z + ∑ j ∈ ω, D j (v j)).1))) := by
      apply congrArg finiteHaarMean
      funext z
      exact (finiteHaarMean_equiv e _).symm
    _ = _ := retainedRootCubeAverage Q D hD h

theorem weightedRetainedRootImageCubeAverage [Fintype G] [Fintype Q]
    {ι : Type*} [Fintype ι] (p : ι → ℝ) {d k : ℕ}
    (D : Fin k → Q →+ (G × (Fin d → Q))) [∀ j, Fintype (D j).range]
    (hD : ∀ j a, (D j a).1 = (a : G)) (h : ι → G → ℝ) :
    (∑ c, p c * finiteHaarMean (fun z : G × (Fin d → Q) => finiteHaarMean
      (fun v : (j : Fin k) → (D j).range =>
        ∏ ω : Finset (Fin k), h c ((z + ∑ j ∈ ω, (v j : G × (Fin d → Q))).1)))) =
      weightedSubgroupCubeAverage p Q k h := by
  simp only [retainedRootImageCubeAverage Q D hD, weightedSubgroupCubeAverage]

end Hindman168
