import Hindman168.RoughResidueCoordinateEndpoints
import Hindman168.RoughResidueCoordinateGeometry
import Mathlib.Data.Int.Interval

/-! Exact zero-based natural index range for the ORIGINAL integer residue
interval. The residue may be any signed integer. No tail is lost. -/
namespace Hindman168
open scoped Classical

theorem rough_residue_index_range_image (A B K r : ℤ) (hK : 0 < K) :
    (Finset.range ((roughResidueCoordinateEndpoint B K r -
      roughResidueCoordinateEndpoint A K r).toNat)).image
      (fun n : ℕ => alignmentResidueEndpoint A K r + K*(n : ℤ)) =
      alignmentIntervalClass A B K r := by
  rw [← rough_residue_coordinate_interval_image A B K r hK,
    Int.Ico_eq_finset_map, Finset.map_eq_image, Finset.image_image]
  apply Finset.image_congr
  intro n _hn
  change alignmentResidueEndpoint A K r+K*(n : ℤ) =
    r+K*(roughResidueCoordinateEndpoint A K r+(n : ℤ))
  rw [← rough_residue_coordinate_endpoint_reconstruct A K r]
  ring

theorem rough_residue_index_affine_injective (A K r : ℤ) (hK : 0 < K) :
    Function.Injective (fun n : ℕ => alignmentResidueEndpoint A K r+K*(n : ℤ)) := by
  intro n m he
  apply Int.ofNat_inj.mp
  apply mul_left_cancel₀ hK.ne'
  exact add_left_cancel he

theorem rough_residue_index_range_card (A B K r : ℤ) (hK : 0 < K) :
    (alignmentIntervalClass A B K r).card =
      (roughResidueCoordinateEndpoint B K r - roughResidueCoordinateEndpoint A K r).toNat := by
  rw [← rough_residue_index_range_image A B K r hK,
    Finset.card_image_of_injective _ (rough_residue_index_affine_injective A K r hK),
    Finset.card_range]

theorem rough_residue_index_dense_hits (A B K r : ℤ) (hK : 0 < K)
    (T : Finset ℤ) (hT : T ⊆ alignmentIntervalClass A B K r) :
    ((Finset.range ((roughResidueCoordinateEndpoint B K r -
      roughResidueCoordinateEndpoint A K r).toNat)).filter
      (fun n : ℕ => alignmentResidueEndpoint A K r+K*(n : ℤ) ∈ T)).card = T.card := by
  let f : ℕ → ℤ := fun n => alignmentResidueEndpoint A K r+K*(n : ℤ)
  let U := (Finset.range ((roughResidueCoordinateEndpoint B K r-
    roughResidueCoordinateEndpoint A K r).toNat)).filter (fun n => f n ∈ T)
  have he : U.image f=T := by
    ext x
    constructor
    · intro hx
      obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hn).2
    · intro hx
      have hxc := hT hx
      rw [← rough_residue_index_range_image A B K r hK] at hxc
      obtain ⟨n,hn,hf⟩ := Finset.mem_image.mp hxc
      exact Finset.mem_image.mpr ⟨n,Finset.mem_filter.mpr ⟨hn,by simpa only [f,hf] using hx⟩,hf⟩
  change U.card=T.card
  rw [← he,Finset.card_image_of_injective _ (rough_residue_index_affine_injective A K r hK)]

end Hindman168
