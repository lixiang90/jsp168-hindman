import Hindman168.NativeFiniteRecipeBounds

/-! Selected blocks can have different coarse gaps. Their common native
space and observable bounds preserve each block's own interval partition. -/

namespace Hindman168
open NNReal
open scoped BigOperators
universe u v

theorem nativeVaryingGap_finset_common {s N : ℕ} (F : MasterParameterFamily)
    {ι : Type v} (S : Finset ι) (gap : ι → ℕ → Fin N) (f : ι → ℕ → ℤ → ℝ)
    (hf : ∀ i ∈ S, NativePieceRepresented.{u} s F (gap i) (f i)) :
    ∃ D : NativeNilmanifoldData.{u} s, ∀ i ∈ S, nativePieceOn D F (gap i) (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨trivialNativeNilmanifold s, by simp⟩
  | @insert a S ha ih =>
    obtain ⟨A, hA⟩ := hf a (Finset.mem_insert_self _ _)
    obtain ⟨B, hB⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    refine ⟨nativeNilmanifoldProduct A B, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact nativePieceOn_product_left A B F (gap i) _ hA
    · exact nativePieceOn_product_right A B F (gap i) _ (hB i hi)

theorem nativeVaryingGap_common_uniform {s N : ℕ} (F : MasterParameterFamily)
    {ι : Type v} [Fintype ι] (gap : ι → ℕ → Fin N) (f : ι → ℕ → ℤ → ℝ)
    (hf : ∀ i, NativePieceRepresented.{u} s F (gap i) (f i)) :
    ∃ D : NativeNilmanifoldData.{u} s,
      letI := D.metric
      letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
      ∃ B : ℝ, ∃ Lip : ℝ≥0, 0 ≤ B ∧
        ∀ i, ∃ (obs : ℕ → (ℤ × ℤ) → C(D.G ⧸ D.Γ, ℝ))
          (g x : ℕ → (ℤ × ℤ) → D.G),
          (∀ w p z, |obs w p z| ≤ B) ∧ (∀ w p, LipschitzWith Lip (obs w p)) ∧
          f i = piecewiseLinearNilsequence D.Γ F (gap i) obs g x := by
  classical
  obtain ⟨D, hD⟩ := nativeVaryingGap_finset_common F Finset.univ gap f (fun i _ => hf i)
  refine ⟨D, ?_⟩
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  have hreps : ∀ i, IsBoundedPieceNilsequence D.Γ F (gap i) (f i) :=
    fun i => hD i (Finset.mem_univ i)
  choose obs g x B Lip hB hb hl he using hreps
  refine ⟨∑ i, B i, ∑ i, Lip i, Finset.sum_nonneg (fun i _ => hB i), ?_⟩
  intro i
  refine ⟨obs i, g i, x i, ?_, ?_, he i⟩
  · exact fun w p z => (hb i w p z).trans
      (Finset.single_le_sum (fun j _ => hB j) (Finset.mem_univ i))
  · exact fun w p => (hl i w p).weaken
      (Finset.single_le_sum (fun j _ => (show 0 ≤ Lip j from zero_le)) (Finset.mem_univ i))

end Hindman168

