import Hindman168.RoughResidueBoxSampling
import Hindman168.ComplexMassTranslation

/-! Exact residual-step sampling x=u+q*y on the original box endpoints.
The finer step is q*t. NO coprimality between q and t is required. -/
namespace Hindman168
open FiniteMass
open scoped Classical

theorem rough_nested_residue_interval_image (A B q u t v : ℤ) (hq : 0 < q) :
    (alignmentIntervalClass (roughResidueCoordinateEndpoint A q u)
      (roughResidueCoordinateEndpoint B q u) t v).image (fun y => u+q*y) =
      alignmentIntervalClass A B (q*t) (u+q*v) := by
  rw [alignment_affine_class_image q t u _ _ v hq,
    rough_residue_coordinate_endpoint_reconstruct,rough_residue_coordinate_endpoint_reconstruct]
  ext x
  simp only [alignmentIntervalClass,Finset.mem_filter,Finset.mem_Ico]
  by_cases hmod : Int.ModEq (q*t) (u+q*v) x
  · have hbase : Int.ModEq q u (u+q*v) := Int.modEq_iff_add_fac.mpr ⟨v,rfl⟩
    have hcoarse : Int.ModEq q u x := hbase.trans (hmod.of_dvd (dvd_mul_right q t))
    have ha := alignmentResidueEndpoint_le_iff A q u x hq hcoarse
    have hb := alignmentResidueEndpoint_le_iff B q u x hq hcoarse
    simp only [hmod,and_true,← not_le,ha,hb]
  · simp only [hmod,and_false]

theorem rough_nested_residue_box_image {ι : Type*} [Fintype ι]
    (A B u v : ι → ℤ) (q t : ℤ) (hq : 0 < q) :
    (alignmentBoxClass (roughResidueBoxEndpoint A u q)
      (roughResidueBoxEndpoint B u q) v t).image (roughResidueBoxAffine u q) =
      alignmentBoxClass A B (fun j => u j+q*v j) (q*t) := by
  rw [show roughResidueBoxAffine u q = (fun y j => u j+q*y j) from rfl,
    alignmentBoxClass,rough_piFinset_coordinate_image
      (fun j => alignmentIntervalClass (roughResidueBoxEndpoint A u q j)
        (roughResidueBoxEndpoint B u q j) t (v j)) (fun j y => u j+q*y)]
  simp only [roughResidueBoxEndpoint,rough_nested_residue_interval_image _ _ q _ t _ hq]
  rfl

theorem rough_nested_residue_box_uniform_push {ι : Type*} [Fintype ι]
    (A B u v : ι → ℤ) (q t : ℤ) (hq : 0 < q) :
    (uniformFinsetMass (alignmentBoxClass (roughResidueBoxEndpoint A u q)
      (roughResidueBoxEndpoint B u q) v t)).mapDomain (roughResidueBoxAffine u q) =
      uniformFinsetMass (alignmentBoxClass A B (fun j => u j+q*v j) (q*t)) := by
  rw [uniformFinsetMass_push _ _ (rough_residue_box_affine_injective u q hq.ne')]
  apply congrArg uniformFinsetMass
  ext x
  simpa only [Finset.mem_image] using
    (Finset.ext_iff.mp (rough_nested_residue_box_image A B u v q t hq) x)

theorem rough_nested_residue_box_complex_discrepancy {ι : Type*} [Fintype ι]
    (A B u v : ι → ℤ) (q t : ℤ) (hq : 0 < q) (f : (ι → ℤ) → ℂ) :
    ‖complexExpectation (uniformFinsetMass (alignmentBoxClass A B (fun j => u j+q*v j) (q*t))) f-
      complexExpectation (uniformFinsetMass (alignmentBoxClass A B u q)) f‖ =
    ‖complexExpectation (uniformFinsetMass (alignmentBoxClass (roughResidueBoxEndpoint A u q)
        (roughResidueBoxEndpoint B u q) v t)) (fun y => f (roughResidueBoxAffine u q y))-
      complexExpectation (uniformFinsetMass (Fintype.piFinset (fun j =>
        Finset.Ico (roughResidueBoxEndpoint A u q j) (roughResidueBoxEndpoint B u q j))))
        (fun y => f (roughResidueBoxAffine u q y))‖ := by
  rw [← rough_nested_residue_box_uniform_push A B u v q t hq,
    ← rough_residue_box_uniform_push A B u q hq,complexExpectation_push,complexExpectation_push]

theorem rough_nested_residue_compatible_representatives {ι : Type*}
    (u b : ι → ℤ) (q t : ℤ) (hq : q ≠ 0)
    (hcompatible : ∀ j, Int.ModEq q (u j) (b j)) :
    ∃ v : ι → ℤ, (∀ j, b j=u j+q*v j) ∧ ∀ (j : ι) (y : ℤ),
      Int.ModEq (q*t) (b j) (u j+q*y) ↔ Int.ModEq t (v j) y := by
  have hrep (j : ι) : ∃ v : ℤ, b j=u j+q*v := Int.modEq_iff_add_fac.mp (hcompatible j)
  choose v hv using hrep
  refine ⟨v,hv,?_⟩
  intro j y
  rw [hv j]
  exact alignment_nested_step_class q t (u j) (v j) y hq

end Hindman168
