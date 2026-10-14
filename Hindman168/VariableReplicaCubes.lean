import Hindman168.MasterPredictionOriginalCubeLimit

/-!
# Replica cubes with different dimensions and their common ambient embedding

Each original replica retains exactly its own nonempty vertex subsets and
shift coordinates. Injective embeddings into one larger cube preserve every
integer row evaluation; extra ambient rows will later carry the test one.
-/

namespace Hindman168

open scoped BigOperators Classical

abbrev VariableReplicaCubeRow {b : ℕ} (dim : Fin b → ℕ) :=
  Option (Σ q : Fin b, CubeVertex (dim q))

abbrev VariableReplicaCubeColumn {b : ℕ} (dim : Fin b → ℕ) :=
  Option (Σ q : Fin b, Fin (dim q) × Bool)

def variableCubeAmbientDimension {b : ℕ} (dim : Fin b → ℕ) : ℕ := ∑ q, dim q

theorem variableCubeAmbientDimension_bound {b : ℕ} (dim : Fin b → ℕ) (q : Fin b) :
    dim q ≤ variableCubeAmbientDimension dim :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)

def variableCubeFinEmbedding {b d : ℕ} {dim : Fin b → ℕ}
    (hd : ∀ q, dim q ≤ d) (q : Fin b) : Fin (dim q) ↪ Fin d :=
  ⟨Fin.castLE (hd q), Fin.castLE_injective (hd q)⟩

def variableCubeVertexEmbedding {b d : ℕ} {dim : Fin b → ℕ}
    (hd : ∀ q, dim q ≤ d) (q : Fin b) (S : CubeVertex (dim q)) : CubeVertex d :=
  ⟨S.val.map (variableCubeFinEmbedding hd q), S.property.map⟩

theorem variableCubeVertexEmbedding_injective {b d : ℕ} {dim : Fin b → ℕ}
    (hd : ∀ q, dim q ≤ d) (q : Fin b) : Function.Injective (variableCubeVertexEmbedding hd q) := by
  intro S T h
  apply Subtype.ext
  exact Finset.map_injective _ (congrArg Subtype.val h)

def variableCubeRowEmbedding {b d : ℕ} {dim : Fin b → ℕ}
    (hd : ∀ q, dim q ≤ d) : VariableReplicaCubeRow dim → ReplicaCubeRow b d
  | none => none
  | some ⟨q, S⟩ => some (q, variableCubeVertexEmbedding hd q S)

def variableCubeColumnEmbedding {b d : ℕ} {dim : Fin b → ℕ}
    (hd : ∀ q, dim q ≤ d) : VariableReplicaCubeColumn dim → ReplicaCubeColumn b d
  | none => none
  | some ⟨q, j, bit⟩ => some (q, Fin.castLE (hd q) j, bit)

theorem variableCubeRowEmbedding_injective {b d : ℕ} {dim : Fin b → ℕ}
    (hd : ∀ q, dim q ≤ d) : Function.Injective (variableCubeRowEmbedding hd) := by
  intro a c h
  cases a with
  | none => cases c with
    | none => rfl
    | some c => simp [variableCubeRowEmbedding] at h
  | some a => cases c with
    | none => simp [variableCubeRowEmbedding] at h
    | some c =>
      rcases a with ⟨q, S⟩
      rcases c with ⟨q', T⟩
      have hp := Option.some.inj h
      have hq := congrArg Prod.fst hp
      dsimp [variableCubeRowEmbedding] at hq
      subst q'
      have hs := variableCubeVertexEmbedding_injective hd q (congrArg Prod.snd hp)
      subst T
      rfl

theorem variableCubeColumnEmbedding_injective {b d : ℕ} {dim : Fin b → ℕ}
    (hd : ∀ q, dim q ≤ d) : Function.Injective (variableCubeColumnEmbedding hd) := by
  intro a c h
  cases a with
  | none => cases c with
    | none => rfl
    | some c => simp [variableCubeColumnEmbedding] at h
  | some a => cases c with
    | none => simp [variableCubeColumnEmbedding] at h
    | some c =>
      rcases a with ⟨q, j, bit⟩
      rcases c with ⟨q', k, bit'⟩
      have hp := Option.some.inj h
      have hq := congrArg Prod.fst hp
      dsimp [variableCubeColumnEmbedding] at hq
      subst q'
      have hj : j = k := Fin.castLE_injective (hd q) (congrArg (fun c => c.2.1) hp)
      have hb : bit = bit' := congrArg (fun c => c.2.2) hp
      subst k
      subst bit'
      rfl

noncomputable def variableReplicaCubeEval {R : Type*} [CommRing R] {b : ℕ}
    {dim : Fin b → ℕ} (M : Fin b → R) :
    VariableReplicaCubeRow dim → (VariableReplicaCubeColumn dim → R) → R
  | none, z => z none
  | some ⟨q, S⟩, z => z none + M q * ∑ j ∈ S.val,
      (z (some ⟨q, j, true⟩) - z (some ⟨q, j, false⟩))

theorem variableReplicaCubeEval_embedding {R : Type*} [CommRing R]
    {b d : ℕ} {dim : Fin b → ℕ} (hd : ∀ q, dim q ≤ d)
    (M : Fin b → R) (row : VariableReplicaCubeRow dim) (z : ReplicaCubeColumn b d → R) :
    replicaCubeEval M (variableCubeRowEmbedding hd row) z =
      variableReplicaCubeEval M row (fun col => z (variableCubeColumnEmbedding hd col)) := by
  cases row with
  | none => exact replicaCubeEval_root M z
  | some row =>
    rcases row with ⟨q, S⟩
    simp only [variableCubeRowEmbedding, replicaCubeEval_vertex, variableCubeVertexEmbedding,
      variableReplicaCubeEval, Finset.sum_map, variableCubeFinEmbedding, Function.Embedding.coeFn_mk,
      variableCubeColumnEmbedding]

end Hindman168
