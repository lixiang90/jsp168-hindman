import Hindman168.NativeFiniteRecipeClosure
import Hindman168.NativeNilmanifoldTrivial

/-! Once finitely many represented families share one native nilmanifold,
one finite observable bound and one Lipschitz constant work simultaneously
for every label, stage, piece and point. -/

namespace Hindman168
open NNReal
open scoped BigOperators
universe u v

theorem nativePieceOn_finite_uniform_bounds {s N : ℕ} (D : NativeNilmanifoldData.{u} s)
    (F : MasterParameterFamily) (gap : ℕ → Fin N) {ι : Type v} [Fintype ι]
    (f : ι → ℕ → ℤ → ℝ) (hf : ∀ i, nativePieceOn D F gap (f i)) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ B : ℝ, ∃ Lip : ℝ≥0, 0 ≤ B ∧
      ∀ i, ∃ (obs : ℕ → (ℤ × ℤ) → C(D.G ⧸ D.Γ, ℝ))
        (g x : ℕ → (ℤ × ℤ) → D.G),
        (∀ w p z, |obs w p z| ≤ B) ∧ (∀ w p, LipschitzWith Lip (obs w p)) ∧
        f i = piecewiseLinearNilsequence D.Γ F gap obs g x := by
  classical
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  have hreps : ∀ i, IsBoundedPieceNilsequence D.Γ F gap (f i) := hf
  choose obs g x B Lip hB hb hl he using hreps
  refine ⟨∑ i, B i, ∑ i, Lip i, Finset.sum_nonneg (fun i _ => hB i), ?_⟩
  intro i
  refine ⟨obs i, g i, x i, ?_, ?_, he i⟩
  · intro w p z
    exact (hb i w p z).trans (Finset.single_le_sum (fun j _ => hB j) (Finset.mem_univ i))
  · intro w p
    exact (hl i w p).weaken (Finset.single_le_sum (fun j _ => (show 0 ≤ Lip j from zero_le)) (Finset.mem_univ i))

theorem nativePieceRepresented_finite_common {s N : ℕ} (seed : NativeNilmanifoldData.{u} s)
    (F : MasterParameterFamily) (gap : ℕ → Fin N) {ι : Type v} [Fintype ι]
    (f : ι → ℕ → ℤ → ℝ) (hf : ∀ i, NativePieceRepresented.{u} s F gap (f i)) :
    ∃ D : NativeNilmanifoldData.{u} s, ∀ i, nativePieceOn D F gap (f i) := by
  obtain ⟨D, hD⟩ := nativePieceRepresented_finset_common seed F gap Finset.univ f (fun i _ => hf i)
  exact ⟨D, fun i => hD i (Finset.mem_univ i)⟩

theorem nativePieceRepresented_sum {s N : ℕ} (F : MasterParameterFamily)
    (gap : ℕ → Fin N) {ι : Type v} (S : Finset ι) (c : ι → ℝ) (f : ι → ℕ → ℤ → ℝ)
    (hf : ∀ i ∈ S, NativePieceRepresented.{u} s F gap (f i)) :
    NativePieceRepresented.{u} s F gap (∑ i ∈ S, c i • f i) :=
  nativePieceRepresented_finset_sum (trivialNativeNilmanifold s) F gap S c f hf

theorem nativePieceRepresented_common_uniform {s N : ℕ}
    (F : MasterParameterFamily) (gap : ℕ → Fin N) {ι : Type v} [Fintype ι]
    (f : ι → ℕ → ℤ → ℝ) (hf : ∀ i, NativePieceRepresented.{u} s F gap (f i)) :
    ∃ D : NativeNilmanifoldData.{u} s,
      letI := D.metric
      letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
      ∃ B : ℝ, ∃ Lip : ℝ≥0, 0 ≤ B ∧
        ∀ i, ∃ (obs : ℕ → (ℤ × ℤ) → C(D.G ⧸ D.Γ, ℝ))
          (g x : ℕ → (ℤ × ℤ) → D.G),
          (∀ w p z, |obs w p z| ≤ B) ∧ (∀ w p, LipschitzWith Lip (obs w p)) ∧
          f i = piecewiseLinearNilsequence D.Γ F gap obs g x := by
  obtain ⟨D, hD⟩ := nativePieceRepresented_finite_common (trivialNativeNilmanifold s) F gap f hf
  exact ⟨D, nativePieceOn_finite_uniform_bounds D F gap f hD⟩

end Hindman168
