import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.Fin.Tuple.Basic

namespace Hindman168
open Submodule Set

theorem projection_append_layer_span {R E F : Type*} [CommRing R]
    [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
    {m n : ℕ} (q : E →ₗ[R] F) (u : Fin m → E) (v : Fin m → F) (c : Fin n → E)
    (hu : ∀ i, q (u i) = v i) (hc : span R (range c) = q.ker)
    (P : Submodule R E) (Q : Submodule R F) (hker : q.ker ≤ P)
    (hmap : P.map q = Q) (hmem : ∀ i, u i ∈ P ↔ v i ∈ Q)
    (hspan : span R (v '' {i | v i ∈ Q}) = Q) :
    span R (Fin.append u c '' {i | Fin.append u c i ∈ P}) = P := by
  let B := span R (Fin.append u c '' {i | Fin.append u c i ∈ P})
  have hBP : B ≤ P := span_le.mpr (by rintro x ⟨i, hi, rfl⟩; exact hi)
  have hcP : ∀ i, c i ∈ P := fun i =>
    hker (hc ▸ subset_span (mem_range_self i))
  have hkerB : q.ker ≤ B := by
    rw [← hc]
    apply span_le.mpr
    rintro x ⟨i, rfl⟩
    apply subset_span
    exact ⟨Fin.natAdd m i, by simpa only [Set.mem_setOf_eq, Fin.append_right] using hcP i,
      Fin.append_right u c i⟩
  have hQB : Q ≤ B.map q := by
    rw [← hspan]
    apply span_le.mpr
    rintro x ⟨i, hi, rfl⟩
    refine ⟨u i, ?_, hu i⟩
    apply subset_span
    exact ⟨Fin.castAdd n i, by simpa only [Set.mem_setOf_eq, Fin.append_left] using (hmem i).mpr hi,
      Fin.append_left u c i⟩
  apply le_antisymm hBP
  intro x hx
  have hqx : q x ∈ Q := hmap ▸ ⟨x, hx, rfl⟩
  obtain ⟨a, ha, he⟩ := hQB hqx
  have hdiff : x-a ∈ q.ker := by
    change q (x-a) = 0
    rw [map_sub, he, sub_self]
  have h := B.add_mem (hkerB hdiff) ha
  simpa only [sub_add_cancel] using h

end Hindman168
