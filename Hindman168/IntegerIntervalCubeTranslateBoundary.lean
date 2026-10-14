import Hindman168.IntegerIntervalCubeCardBounds

namespace Hindman168
open scoped BigOperators Classical

/-- For a nonnegative parameter translation, cubes leaving the interval
domain must have some original vertex in an upper strip of width D. -/
theorem integerIntervalCube_translate_out_card_le (d L D : ℕ)
    (r : ℤ × (Fin d → ℤ))
    (hr : ∀ ω : Finset (Fin d), 0 ≤ integerCubeVertex r ω ∧ integerCubeVertex r ω ≤ D) :
    ((integerIntervalCubeDomain d L).filter (fun p =>
      p + r ∉ integerIntervalCubeDomain d L)).card ≤ 2 ^ d * D * L ^ d := by
  let A := integerIntervalCubeDomain d L
  let B := fun ω : Finset (Fin d) => A.filter (fun p =>
    (L : ℤ) - D ≤ integerCubeVertex p ω ∧ integerCubeVertex p ω < L)
  have hsubset : A.filter (fun p => p + r ∉ A) ⊆ Finset.univ.biUnion B := by
    intro p hp
    obtain ⟨hp, hbad⟩ := Finset.mem_filter.mp hp
    have hall := (mem_integerIntervalCubeDomain p).mp hp
    have hex : ∃ ω : Finset (Fin d), (L : ℤ) ≤ integerCubeVertex (p + r) ω := by
      by_contra hn
      push Not at hn
      apply hbad
      apply (mem_integerIntervalCubeDomain _).mpr
      intro ω
      refine ⟨?_, hn ω⟩
      rw [integerCubeVertex_add]
      exact add_nonneg (hall ω).1 (hr ω).1
    obtain ⟨ω, hω⟩ := hex
    rw [integerCubeVertex_add] at hω
    exact Finset.mem_biUnion.mpr ⟨ω, Finset.mem_univ _, Finset.mem_filter.mpr
      ⟨hp, by constructor; linarith [(hr ω).2]; exact (hall ω).2⟩⟩
  have hstrip (ω : Finset (Fin d)) : (B ω).card ≤ D * L ^ d := by
    have h := integerIntervalCubeDomain_vertex_strip_card_le d L ω ((L : ℤ) - D) L
    have he : (L : ℤ) - ((L : ℤ) - D) = D := by ring
    rw [he, Int.toNat_natCast] at h
    exact h
  calc
    _ ≤ (Finset.univ.biUnion B).card := Finset.card_le_card hsubset
    _ ≤ ∑ ω : Finset (Fin d), (B ω).card := Finset.card_biUnion_le
    _ ≤ ∑ _ω : Finset (Fin d), D * L ^ d := Finset.sum_le_sum (fun ω _ => hstrip ω)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_finset,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_id, mul_assoc]

/-- Cubes whose backward translate leaves the domain have a vertex
in a lower strip of width D. This gives the other boundary side. -/
theorem integerIntervalCube_translate_back_out_card_le (d L D : ℕ)
    (r : ℤ × (Fin d → ℤ))
    (hr : ∀ ω : Finset (Fin d), 0 ≤ integerCubeVertex r ω ∧ integerCubeVertex r ω ≤ D) :
    ((integerIntervalCubeDomain d L).filter (fun p =>
      p - r ∉ integerIntervalCubeDomain d L)).card ≤ 2 ^ d * D * L ^ d := by
  let A := integerIntervalCubeDomain d L
  let B := fun ω : Finset (Fin d) => A.filter (fun p =>
    0 ≤ integerCubeVertex p ω ∧ integerCubeVertex p ω < D)
  have hsub (p : ℤ × (Fin d → ℤ)) (ω : Finset (Fin d)) :
      integerCubeVertex (p - r) ω = integerCubeVertex p ω - integerCubeVertex r ω := by
    have he := integerCubeVertex_add (p - r) r ω
    rw [sub_add_cancel] at he
    linarith
  have hsubset : A.filter (fun p => p - r ∉ A) ⊆ Finset.univ.biUnion B := by
    intro p hp
    obtain ⟨hp, hbad⟩ := Finset.mem_filter.mp hp
    have hall := (mem_integerIntervalCubeDomain p).mp hp
    have hex : ∃ ω : Finset (Fin d), integerCubeVertex (p - r) ω < 0 := by
      by_contra hn
      push Not at hn
      apply hbad
      apply (mem_integerIntervalCubeDomain _).mpr
      intro ω
      refine ⟨hn ω, ?_⟩
      rw [hsub]
      linarith [(hall ω).2, (hr ω).1]
    obtain ⟨ω, hω⟩ := hex
    rw [hsub] at hω
    exact Finset.mem_biUnion.mpr ⟨ω, Finset.mem_univ _, Finset.mem_filter.mpr
      ⟨hp, by constructor; exact (hall ω).1; linarith [(hr ω).2]⟩⟩
  have hstrip (ω : Finset (Fin d)) : (B ω).card ≤ D * L ^ d := by
    have h := integerIntervalCubeDomain_vertex_strip_card_le d L ω 0 D
    simpa only [sub_zero, Int.toNat_natCast] using h
  calc
    _ ≤ (Finset.univ.biUnion B).card := Finset.card_le_card hsubset
    _ ≤ ∑ ω : Finset (Fin d), (B ω).card := Finset.card_biUnion_le
    _ ≤ ∑ _ω : Finset (Fin d), D * L ^ d := Finset.sum_le_sum (fun ω _ => hstrip ω)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_finset,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_id, mul_assoc]

end Hindman168
