import Hindman168.FiniteFlagOrder
import Hindman168.IntegerFlagBasis

namespace Hindman168
open Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem ordered_flag_basis_exists {k n : ℕ} (b : Basis (Fin n) R M)
    (V : Fin k → Submodule R M) (hV : Antitone V)
    (hb : ∀ j, Submodule.span R (b '' {i | b i ∈ V j}) = V j) :
    ∃ c : Basis (Fin n) R M, ∃ t : Fin k → ℕ,
      ∀ j, t j ≤ n ∧
        (∀ i : Fin n, c i ∈ V j ↔ t j ≤ i.val) ∧
          Submodule.span R (c '' {i | t j ≤ i.val}) = V j := by
  let P := fun j i => b i ∈ V j
  have hP : ∀ i j : Fin k, i ≤ j → ∀ x, P j x → P i x :=
    fun i j hij x hx => hV hij hx
  let e := Tuple.sort (finiteFlagDepth P)
  let c := b.reindex e.symm
  let t := fun j => finiteUpperStart (fun i => P j (e i))
  have hc : ∀ i, c i = b (e i) := fun i => by simp [c]
  have hm : ∀ j i, c i ∈ V j ↔ t j ≤ i.val := by
    intro j i
    rw [hc]
    exact finite_upper_mem_iff_start _ (fun a d had => finite_flag_sort_upper P hP j had) i
  refine ⟨c, t, fun j => ⟨finite_upper_start_le _, hm j, ?_⟩⟩
  have he : {i : Fin n | t j ≤ i.val} = {i | c i ∈ V j} :=
    Set.ext (fun i => (hm j i).symm)
  rw [he]
  exact (integer_basis_adapted_reindex b e.symm (V j)).trans (hb j)

end Hindman168
