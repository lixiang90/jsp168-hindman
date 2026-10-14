import Hindman168.NativeProductLieTopology

/-! Nonempty finite products of the original spaces, built by actual
binary products. All recursively constructed structures are local. -/

namespace Hindman168

def nativeFiniteProduct (X : Type*) : ℕ → Type _
  | 0 => X
  | n + 1 => nativeFiniteProduct X n × X

@[reducible]
def nativeFiniteProductTopologicalSpace {X : Type*} [TopologicalSpace X] :
    (n : ℕ) → TopologicalSpace (nativeFiniteProduct X n)
  | 0 => inferInstanceAs (TopologicalSpace X)
  | n + 1 => by
    letI := nativeFiniteProductTopologicalSpace (X := X) n
    exact inferInstanceAs (TopologicalSpace (nativeFiniteProduct X n × X))

attribute [local instance] nativeFiniteProductTopologicalSpace

@[reducible]
def nativeFiniteProductGroup {G : Type*} [Group G] :
    (n : ℕ) → Group (nativeFiniteProduct G n)
  | 0 => inferInstanceAs (Group G)
  | n + 1 => by
    letI := nativeFiniteProductGroup (G := G) n
    exact inferInstanceAs (Group (nativeFiniteProduct G n × G))

attribute [local instance] nativeFiniteProductGroup

@[reducible]
def nativeFiniteProductNormedAddCommGroup {E : Type*} [NormedAddCommGroup E] :
    (n : ℕ) → NormedAddCommGroup (nativeFiniteProduct E n)
  | 0 => inferInstanceAs (NormedAddCommGroup E)
  | n + 1 => by
    letI := nativeFiniteProductNormedAddCommGroup (E := E) n
    exact inferInstanceAs (NormedAddCommGroup (nativeFiniteProduct E n × E))

attribute [local instance] nativeFiniteProductNormedAddCommGroup

@[reducible]
def nativeFiniteProductNormedSpace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (n : ℕ) → NormedSpace ℝ (nativeFiniteProduct E n)
  | 0 => inferInstanceAs (NormedSpace ℝ E)
  | n + 1 => by
    letI := nativeFiniteProductNormedSpace (E := E) n
    exact inferInstanceAs (NormedSpace ℝ (nativeFiniteProduct E n × E))

attribute [local instance] nativeFiniteProductNormedSpace

theorem nativeFiniteProductCompleteSpace {E : Type*} [NormedAddCommGroup E]
    [CompleteSpace E] : (n : ℕ) → CompleteSpace (nativeFiniteProduct E n)
  | 0 => inferInstanceAs (CompleteSpace E)
  | n + 1 => by
    letI := nativeFiniteProductCompleteSpace (E := E) n
    exact inferInstanceAs (CompleteSpace (nativeFiniteProduct E n × E))

theorem nativeFiniteProductFiniteDimensional {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    (n : ℕ) → FiniteDimensional ℝ (nativeFiniteProduct E n)
  | 0 => inferInstanceAs (FiniteDimensional ℝ E)
  | n + 1 => by
    letI := nativeFiniteProductFiniteDimensional (E := E) n
    exact inferInstanceAs (FiniteDimensional ℝ (nativeFiniteProduct E n × E))

theorem nativeFiniteProductT2Space {X : Type*} [TopologicalSpace X] [T2Space X] :
    (n : ℕ) → T2Space (nativeFiniteProduct X n)
  | 0 => inferInstanceAs (T2Space X)
  | n + 1 => by
    letI := nativeFiniteProductT2Space (X := X) n
    exact inferInstanceAs (T2Space (nativeFiniteProduct X n × X))

theorem nativeFiniteProductIsNilpotent {G : Type*} [Group G] [Group.IsNilpotent G] :
    (n : ℕ) → Group.IsNilpotent (nativeFiniteProduct G n)
  | 0 => inferInstanceAs (Group.IsNilpotent G)
  | n + 1 => by
    letI := nativeFiniteProductIsNilpotent (G := G) n
    exact inferInstanceAs (Group.IsNilpotent (nativeFiniteProduct G n × G))

theorem nativeFiniteProductConnectedSpace {X : Type*} [TopologicalSpace X]
    [ConnectedSpace X] : (n : ℕ) → ConnectedSpace (nativeFiniteProduct X n)
  | 0 => inferInstanceAs (ConnectedSpace X)
  | n + 1 => by
    letI := nativeFiniteProductConnectedSpace (X := X) n
    exact inferInstanceAs (ConnectedSpace (nativeFiniteProduct X n × X))

end Hindman168
