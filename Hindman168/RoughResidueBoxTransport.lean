import Hindman168.RoughResidueCoordinateStep

namespace Hindman168
open scoped Classical

def roughResidueBoxEndpoint {ι : Type*} (A u : ι → ℤ) (K : ℤ) : ι → ℤ :=
  fun j => roughResidueCoordinateEndpoint (A j) K (u j)

def roughResidueBoxAffine {ι : Type*} (u : ι → ℤ) (K : ℤ) (y : ι → ℤ) : ι → ℤ :=
  fun j => u j+K*y j

theorem rough_piFinset_coordinate_image {ι α β : Type*} [Fintype ι] [DecidableEq α] [DecidableEq β]
    (S : ι → Finset α) (f : ι → α → β) :
    (Fintype.piFinset S).image (fun y j => f j (y j)) =
      Fintype.piFinset (fun j => (S j).image (f j)) := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    exact Fintype.mem_piFinset.mpr (fun j => Finset.mem_image.mpr ⟨y j, Fintype.mem_piFinset.mp hy j, rfl⟩)
  · intro hz
    have hh : ∀ j, ∃ y, y ∈ S j ∧ f j y = z j := fun j =>
      Finset.mem_image.mp (Fintype.mem_piFinset.mp hz j)
    choose y hy he using hh
    exact Finset.mem_image.mpr ⟨y, Fintype.mem_piFinset.mpr hy, funext he⟩

theorem rough_residue_box_affine_injective {ι : Type*} (u : ι → ℤ) (K : ℤ) (hK : K ≠ 0) :
    Function.Injective (roughResidueBoxAffine u K) := by
  intro y y' he
  funext j
  have hj := congrFun he j
  change u j+K*y j = u j+K*y' j at hj
  exact (mul_left_cancel₀ hK) (add_left_cancel hj)

theorem rough_residue_box_unrestricted_image {ι : Type*} [Fintype ι]
    (A B u : ι → ℤ) (K : ℤ) (hK : 0 < K) :
    (Fintype.piFinset (fun j => Finset.Ico (roughResidueBoxEndpoint A u K j)
        (roughResidueBoxEndpoint B u K j))).image (roughResidueBoxAffine u K) =
      alignmentBoxClass A B u K := by
  rw [show roughResidueBoxAffine u K = (fun y j => u j+K*y j) from rfl]
  rw [rough_piFinset_coordinate_image
    (fun j => Finset.Ico (roughResidueBoxEndpoint A u K j) (roughResidueBoxEndpoint B u K j))
    (fun j y => u j+K*y)]
  simp only [roughResidueBoxEndpoint, rough_residue_coordinate_interval_image _ _ K _ hK, alignmentBoxClass]

theorem rough_residue_box_step_image {ι : Type*} [Fintype ι]
    (A B a u : ι → ℤ) (t K : ℕ) (ht : 0 < t) (hK : 0 < K) (hcop : t.Coprime K) :
    ∃ v : ι → ℤ,
      (alignmentBoxClass (roughResidueBoxEndpoint A u K) (roughResidueBoxEndpoint B u K) v t).image
        (roughResidueBoxAffine u K) = alignmentBoxClass A B a t ∩ alignmentBoxClass A B u K := by
  classical
  have hh : ∀ j, ∃ v : ℤ,
      (alignmentIntervalClass (roughResidueCoordinateEndpoint (A j) K (u j))
        (roughResidueCoordinateEndpoint (B j) K (u j)) t v).image (fun y => u j+(K : ℤ)*y) =
        alignmentIntervalClass (A j) (B j) t (a j) ∩ alignmentIntervalClass (A j) (B j) K (u j) :=
    fun j => rough_residue_coordinate_step_interval_image _ _ _ _ t K ht hK hcop
  choose v hv using hh
  refine ⟨v, ?_⟩
  simp only [alignmentBoxClass]
  rw [show roughResidueBoxAffine u (K : ℤ) = (fun y j => u j+(K : ℤ)*y j) from rfl]
  rw [rough_piFinset_coordinate_image
    (fun j => alignmentIntervalClass (roughResidueBoxEndpoint A u K j)
      (roughResidueBoxEndpoint B u K j) t (v j)) (fun j y => u j+(K : ℤ)*y)]
  simp only [roughResidueBoxEndpoint, hv]
  ext z
  simp only [Fintype.mem_piFinset, Finset.mem_inter]
  exact ⟨fun h => ⟨fun j => (h j).1, fun j => (h j).2⟩,
    fun h j => ⟨h.1 j, h.2 j⟩⟩

end Hindman168
