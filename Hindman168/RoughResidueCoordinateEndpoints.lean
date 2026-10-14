import Hindman168.RoughBoxPartition

namespace Hindman168

def roughResidueCoordinateEndpoint (A K u : ℤ) : ℤ :=
  (alignmentResidueEndpoint A K u-u)/K

theorem rough_residue_coordinate_endpoint_reconstruct (A K u : ℤ) :
    u+K*roughResidueCoordinateEndpoint A K u = alignmentResidueEndpoint A K u := by
  have hdiv : K ∣ alignmentResidueEndpoint A K u-u :=
    Int.modEq_iff_dvd.mp (alignmentResidueEndpoint_modEq A K u).symm
  rw [roughResidueCoordinateEndpoint, Int.mul_ediv_cancel' hdiv]
  ring

theorem rough_residue_coordinate_endpoint_bounds (A K u : ℤ) (hK : 0 < K) :
    A ≤ u+K*roughResidueCoordinateEndpoint A K u ∧
      u+K*roughResidueCoordinateEndpoint A K u < A+K := by
  rw [rough_residue_coordinate_endpoint_reconstruct]
  exact alignmentResidueEndpoint_bounds A K u hK

theorem rough_residue_coordinate_endpoint_mono (K u : ℤ) (hK : 0 < K) :
    Monotone (fun A => roughResidueCoordinateEndpoint A K u) := by
  intro A B hAB
  have hr := alignmentResidueEndpoint_modEq B K u
  have he := (alignmentResidueEndpoint_le_iff A K u (alignmentResidueEndpoint B K u) hK hr.symm).mpr
    (hAB.trans (alignmentResidueEndpoint_bounds B K u hK).1)
  rw [← rough_residue_coordinate_endpoint_reconstruct A K u,
    ← rough_residue_coordinate_endpoint_reconstruct B K u] at he
  nlinarith

theorem rough_residue_coordinate_interval_image (A B K u : ℤ) (hK : 0 < K) :
    (Finset.Ico (roughResidueCoordinateEndpoint A K u) (roughResidueCoordinateEndpoint B K u)).image
      (fun y => u+K*y) = alignmentIntervalClass A B K u := by
  have hh := alignment_affine_class_image K 1 u (roughResidueCoordinateEndpoint A K u)
    (roughResidueCoordinateEndpoint B K u) 0 hK
  have hfull (l r : ℤ) : alignmentIntervalClass l r 1 0 = Finset.Ico l r := by
    simp [alignmentIntervalClass, Int.ModEq]
  rw [hfull, mul_one, mul_zero, add_zero,
    rough_residue_coordinate_endpoint_reconstruct,
    rough_residue_coordinate_endpoint_reconstruct] at hh
  rw [hh]
  have he : alignmentIntervalClass A B K u =
      alignmentIntervalClass (alignmentResidueEndpoint A K u) (alignmentResidueEndpoint B K u) K u := by
    simpa only [alignmentIntervalClass] using alignmentResidueEndpoint_interval_exact A B K u hK
  exact he.symm

end Hindman168
