import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Connected.Basic
import Mathlib.GroupTheory.Finiteness

/-! In the original connected topological group, an open set whose right
translates by a specified subgroup cover the group determines generators:
the subgroup elements in K^-1*K generate whenever the open set lies in K.
The proof uses actual translate overlaps and preconnectedness. -/

namespace Hindman168
open Set
open scoped Pointwise

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PreconnectedSpace G]

 theorem subgroup_eq_closure_overlaps_of_open_cover (Γ : Subgroup G)
    {O K : Set G} (hO : IsOpen O) (hOK : O ⊆ K) (hcover : O * (Γ : Set G) = univ) :
    Subgroup.closure {g : G | g ∈ Γ ∧ g ∈ K⁻¹ * K} = Γ := by
  let T : Set G := {g : G | g ∈ Γ ∧ g ∈ K⁻¹ * K}
  let L : Subgroup G := Subgroup.closure T
  have hle : L ≤ Γ := (Subgroup.closure_le (K := Γ)).mpr (fun _ hg => hg.1)
  have hoverlap : ∀ a ∈ O, ∀ b ∈ O, ∀ h ∈ Γ, ∀ k ∈ Γ,
      a * h = b * k → h * k⁻¹ ∈ L := by
    intro a ha b hb h hh k hk he
    have he' : h * k⁻¹ = a⁻¹ * b := by
      calc
        h * k⁻¹ = (a⁻¹ * (a * h)) * k⁻¹ := by rw [inv_mul_cancel_left]
        _ = (a⁻¹ * (b * k)) * k⁻¹ := by rw [he]
        _ = a⁻¹ * b := by rw [← mul_assoc, mul_inv_cancel_right]
    apply Subgroup.subset_closure
    refine ⟨Γ.mul_mem hh (Γ.inv_mem hk), ?_⟩
    rw [he']
    exact mul_mem_mul (inv_mem_inv.mpr (hOK ha)) (hOK hb)
  have hrecover : ∀ h ∈ L, ∀ k ∈ Γ, h * k⁻¹ ∈ L → k ∈ L := by
    intro h hh k _ ht
    have hk : k⁻¹ ∈ L := by
      simpa only [inv_mul_cancel_left] using L.mul_mem (L.inv_mem hh) ht
    simpa only [inv_inv] using L.inv_mem hk
  let A : Set G := ⋃ h : G, ⋃ (_ : h ∈ L), (fun a : G => a * h) '' O
  let B : Set G := ⋃ k : G, ⋃ (_ : k ∈ Γ ∧ k ∉ L), (fun b : G => b * k) '' O
  have hAo : IsOpen A := isOpen_iUnion (fun h => isOpen_iUnion
    (fun _ => isOpenMap_mul_right h _ hO))
  have hBo : IsOpen B := isOpen_iUnion (fun k => isOpen_iUnion
    (fun _ => isOpenMap_mul_right k _ hO))
  have hAB : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro x hxA hxB
    obtain ⟨h, hh, a, ha, he⟩ := mem_iUnion₂.mp hxA
    obtain ⟨k, hk, b, hb, ke⟩ := mem_iUnion₂.mp hxB
    exact hk.2 (hrecover h hh k hk.1
      (hoverlap a ha b hb h (hle hh) k hk.1 (he.trans ke.symm)))
  have hu : (univ : Set G) ⊆ A ∪ B := by
    intro x _
    have hx : x ∈ O * (Γ : Set G) := by rw [hcover]; trivial
    obtain ⟨a, ha, h, hh, rfl⟩ := mem_mul.mp hx
    by_cases hl : h ∈ L
    · exact Or.inl (mem_iUnion₂.mpr ⟨h, hl, a, ha, rfl⟩)
    · exact Or.inr (mem_iUnion₂.mpr ⟨h, ⟨hh, hl⟩, a, ha, rfl⟩)
  have hone : (1 : G) ∈ O * (Γ : Set G) := by rw [hcover]; trivial
  obtain ⟨o, ho, k, _, _⟩ := mem_mul.mp hone
  have hoA : o ∈ A := mem_iUnion₂.mpr ⟨1, L.one_mem, o, ho, mul_one o⟩
  have hall : (univ : Set G) ⊆ A :=
    isPreconnected_univ.subset_left_of_subset_union hAo hBo hAB hu ⟨o, mem_univ o, hoA⟩
  change L = Γ
  apply le_antisymm hle
  intro g hg
  obtain ⟨h, hh, a, ha, he⟩ := mem_iUnion₂.mp (hall (mem_univ (o * g)))
  exact hrecover h hh g hg (hoverlap a ha o ho h (hle hh) g hg he)

end Hindman168
