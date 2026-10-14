import Hindman168.VariableReplicaCubes

/-!
# Padding variable cubes by tests one and integrating unused coordinates

Injected rows retain their actual test. Every extra ambient row carries one,
so it makes no contribution to the product. Unused shift coordinates are
integrated out with their proved mass one; no new independence is presumed.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

noncomputable def embeddedValue {α β γ : Type*} (e : α → β)
    (f : α → γ) (fallback : γ) (y : β) : γ :=
  if h : ∃ x, e x = y then f (Classical.choose h) else fallback

theorem embeddedValue_apply {α β γ : Type*} (e : α → β) (he : Function.Injective e)
    (f : α → γ) (fallback : γ) (x : α) : embeddedValue e f fallback (e x) = f x := by
  unfold embeddedValue
  rw [dif_pos ⟨x, rfl⟩]
  congr 1
  exact he (Classical.choose_spec (show ∃ y, e y = e x from ⟨x, rfl⟩))

theorem embeddedValue_outside {α β γ : Type*} (e : α → β)
    (f : α → γ) (fallback : γ) (y : β) (hy : y ∉ Set.range e) :
    embeddedValue e f fallback y = fallback := by
  exact dif_neg hy

theorem variable_cube_padded_product {b d : ℕ} {dim : Fin b → ℕ}
    (hd : ∀ q, dim q ≤ d) (M : Fin b → ℤ)
    (G : VariableReplicaCubeRow dim → ℤ → ℝ) (z : ReplicaCubeColumn b d → ℤ) :
    (∏ row, embeddedValue (variableCubeRowEmbedding hd) G (fun _ => 1) row
      (replicaCubeEval M row z)) =
      ∏ row, G row (variableReplicaCubeEval M row
        (fun col => z (variableCubeColumnEmbedding hd col))) := by
  apply (Fintype.prod_of_injective (variableCubeRowEmbedding hd)
    (variableCubeRowEmbedding_injective hd) _ _ ?_ ?_).symm
  · intro row hr
    rw [embeddedValue_outside _ _ _ _ hr]
  · intro row
    rw [embeddedValue_apply _ (variableCubeRowEmbedding_injective hd), variableReplicaCubeEval_embedding]

noncomputable def variablePredictionOriginalColumnMass {b : ℕ} {dim : Fin b → ℕ}
    (X W : ℕ) (A : VariableReplicaCubeColumn dim → ℤ) (T : Fin b → ℕ) :
    VariableReplicaCubeColumn dim → Mass ℤ
  | none => integerMass X W
  | some ⟨q, j, bit⟩ => uniformIntervalMass (A (some ⟨q, j, bit⟩)) (T q)

noncomputable def variableCubePaddedLocations {b d : ℕ} {dim : Fin b → ℕ}
    (hd : ∀ q, dim q ≤ d) (A : VariableReplicaCubeColumn dim → ℤ)
    (c : Fin b × Fin d × Bool) : ℤ :=
  embeddedValue (variableCubeColumnEmbedding hd) A 0 (some c)

theorem variable_cube_original_column_mass {b d : ℕ} {dim : Fin b → ℕ}
    (hd : ∀ q, dim q ≤ d) (X W : ℕ) (A : VariableReplicaCubeColumn dim → ℤ)
    (T : Fin b → ℕ) (col : VariableReplicaCubeColumn dim) :
    predictionOriginalColumnMass X W (variableCubePaddedLocations hd A) T
      (variableCubeColumnEmbedding hd col) = variablePredictionOriginalColumnMass X W A T col := by
  cases col with
  | none => rfl
  | some c =>
    rcases c with ⟨q, j, bit⟩
    change uniformIntervalMass
      (embeddedValue (variableCubeColumnEmbedding hd) A 0 (variableCubeColumnEmbedding hd (some ⟨q, j, bit⟩)))
      (T q) = uniformIntervalMass (A (some ⟨q, j, bit⟩)) (T q)
    rw [embeddedValue_apply _ (variableCubeColumnEmbedding_injective hd)]

theorem variable_cube_original_mass_projection {b d : ℕ} {dim : Fin b → ℕ}
    (hd : ∀ q, dim q ≤ d) (X W : ℕ) (A : VariableReplicaCubeColumn dim → ℤ)
    (T : Fin b → ℕ) (hZ : 0 < harmonicNormalizer X W) (hT : ∀ q, 0 < T q) :
    (piMass (predictionOriginalColumnMass X W (variableCubePaddedLocations hd A) T)).mapDomain
      (fun z col => z (variableCubeColumnEmbedding hd col)) =
      piMass (variablePredictionOriginalColumnMass X W A T) := by
  rw [piMass_restrict _ (variableCubeColumnEmbedding hd) (variableCubeColumnEmbedding_injective hd)
    (predictionOriginalColumnMass_total X W _ T hZ hT)]
  congr 1
  funext col
  exact variable_cube_original_column_mass hd X W A T col

theorem variable_cube_padded_expectation {b d : ℕ} {dim : Fin b → ℕ}
    (hd : ∀ q, dim q ≤ d) (X W : ℕ) (A : VariableReplicaCubeColumn dim → ℤ)
    (T : Fin b → ℕ) (hZ : 0 < harmonicNormalizer X W) (hT : ∀ q, 0 < T q)
    (M : Fin b → ℤ) (G : VariableReplicaCubeRow dim → ℤ → ℝ) :
    expectation (piMass (predictionOriginalColumnMass X W (variableCubePaddedLocations hd A) T))
      (fun z => ∏ row, embeddedValue (variableCubeRowEmbedding hd) G (fun _ => 1) row
        (replicaCubeEval M row z)) =
      expectation (piMass (variablePredictionOriginalColumnMass X W A T))
        (fun z => ∏ row, G row (variableReplicaCubeEval M row z)) := by
  simp_rw [variable_cube_padded_product hd M G]
  rw [← variable_cube_original_mass_projection hd X W A T hZ hT, expectation_push]

end Hindman168
