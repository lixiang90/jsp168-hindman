import Hindman168.RoughResidueCoordinateEndpoints
import Hindman168.AlignmentRetainedCRTClasses
import Hindman168.RoughCoprimeResidueIntersection

namespace Hindman168

theorem rough_residue_coordinate_step (t K : ℕ) (ht : 0 < t)
    (hcop : t.Coprime K) (a u : ℤ) :
    ∃ v : ℤ, ∀ y : ℤ, Int.ModEq t a (u+(K : ℤ)*y) ↔ Int.ModEq t v y := by
  obtain ⟨c, hc⟩ := rough_coprime_residue_pair t K hcop a u
  have hclasses := (hc c).mpr (Int.ModEq.refl c)
  obtain ⟨v, hv⟩ := Int.modEq_iff_add_fac.mp hclasses.2
  refine ⟨v, fun y => ?_⟩
  have hvT : Int.ModEq t a (u+(K : ℤ)*v) := by simpa only [← hv] using hclasses.1
  constructor
  · intro hy
    have hmul : Int.ModEq t ((K : ℤ)*v) ((K : ℤ)*y) := (hvT.symm.trans hy).add_left_cancel' u
    exact alignment_coprime_modEq_cancel K t ht hcop.symm v y hmul
  · intro hy
    exact hvT.trans ((hy.mul_left K).add_left u)

theorem rough_residue_coordinate_step_interval_image (A B a u : ℤ) (t K : ℕ)
    (ht : 0 < t) (hK : 0 < K) (hcop : t.Coprime K) :
    ∃ v : ℤ,
      (alignmentIntervalClass (roughResidueCoordinateEndpoint A K u)
        (roughResidueCoordinateEndpoint B K u) t v).image (fun y => u+(K : ℤ)*y) =
      alignmentIntervalClass A B t a ∩ alignmentIntervalClass A B K u := by
  obtain ⟨v, hv⟩ := rough_residue_coordinate_step t K ht hcop a u
  have hp : (0 : ℤ) < K := by exact_mod_cast hK
  refine ⟨v, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have hi := (Finset.mem_filter.mp hy).1
    have hm : u+(K : ℤ)*y ∈ alignmentIntervalClass A B K u := by
      rw [← rough_residue_coordinate_interval_image A B K u hp]
      exact Finset.mem_image.mpr ⟨y, hi, rfl⟩
    exact Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hm).1, (hv y).mpr (Finset.mem_filter.mp hy).2⟩, hm⟩
  · intro hx
    obtain ⟨hxT, hxK⟩ := Finset.mem_inter.mp hx
    rw [← rough_residue_coordinate_interval_image A B K u hp] at hxK
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hxK
    exact Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr
      ⟨hy, (hv y).mp (Finset.mem_filter.mp hxT).2⟩, rfl⟩

end Hindman168
