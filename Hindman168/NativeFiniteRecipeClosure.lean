import Hindman168.NativePieceRecipes

/-! Native recipes form a genuine vector subspace of raw stage families.
Every finite family has one common native product manifold, not just a
separate abstract representation for each algebraic operation. -/

namespace Hindman168
open scoped BigOperators
universe u v

noncomputable def nativePieceFunctionSpace (s : ℕ) (seed : NativeNilmanifoldData.{u} s)
    {N : ℕ} (F : MasterParameterFamily) (gap : ℕ → Fin N) : Submodule ℝ (ℕ → ℤ → ℝ) where
  carrier := NativePieceRepresented.{u} s F gap
  zero_mem' := ⟨seed, nativePieceOn_const seed F gap 0⟩
  add_mem' := by
    rintro f g ⟨A, hf⟩ ⟨B, hg⟩
    exact ⟨nativeNilmanifoldProduct A B, nativePieceOn_add A B F gap f g hf hg⟩
  smul_mem' := by
    rintro r f ⟨D, hf⟩
    exact ⟨D, nativePieceOn_smul D F gap f hf r⟩

theorem nativePieceRepresented_finset_sum {s N : ℕ} (seed : NativeNilmanifoldData.{u} s)
    (F : MasterParameterFamily) (gap : ℕ → Fin N) {ι : Type v} (S : Finset ι)
    (c : ι → ℝ) (f : ι → ℕ → ℤ → ℝ)
    (hf : ∀ i ∈ S, NativePieceRepresented.{u} s F gap (f i)) :
    NativePieceRepresented.{u} s F gap (∑ i ∈ S, c i • f i) := by
  exact (nativePieceFunctionSpace s seed F gap).sum_mem
    (fun i hi => (nativePieceFunctionSpace s seed F gap).smul_mem (c i) (hf i hi))

theorem nativePieceOn_product_left {s N : ℕ} (A B : NativeNilmanifoldData.{u} s)
    (F : MasterParameterFamily) (gap : ℕ → Fin N) (f : ℕ → ℤ → ℝ)
    (hf : nativePieceOn A F gap f) : nativePieceOn (nativeNilmanifoldProduct A B) F gap f := by
  simpa only [add_zero] using nativePieceOn_add A B F gap f (fun _ _ => 0) hf
    (nativePieceOn_const B F gap 0)

theorem nativePieceOn_product_right {s N : ℕ} (A B : NativeNilmanifoldData.{u} s)
    (F : MasterParameterFamily) (gap : ℕ → Fin N) (f : ℕ → ℤ → ℝ)
    (hf : nativePieceOn B F gap f) : nativePieceOn (nativeNilmanifoldProduct A B) F gap f := by
  simpa only [zero_add] using nativePieceOn_add A B F gap (fun _ _ => 0) f
    (nativePieceOn_const A F gap 0) hf

theorem nativePieceRepresented_finset_common {s N : ℕ} (seed : NativeNilmanifoldData.{u} s)
    (F : MasterParameterFamily) (gap : ℕ → Fin N) {ι : Type v} (S : Finset ι)
    (f : ι → ℕ → ℤ → ℝ) (hf : ∀ i ∈ S, NativePieceRepresented.{u} s F gap (f i)) :
    ∃ D : NativeNilmanifoldData.{u} s, ∀ i ∈ S, nativePieceOn D F gap (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨seed, by simp⟩
  | @insert a S ha ih =>
    obtain ⟨A, hA⟩ := hf a (Finset.mem_insert_self _ _)
    obtain ⟨B, hB⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    refine ⟨nativeNilmanifoldProduct A B, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact nativePieceOn_product_left A B F gap _ hA
    · exact nativePieceOn_product_right A B F gap _ (hB i hi)

end Hindman168
