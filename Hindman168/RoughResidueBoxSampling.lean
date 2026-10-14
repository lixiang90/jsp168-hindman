import Hindman168.RoughResidueBoxTransport
import Hindman168.UniformFiniteMass

namespace Hindman168
open FiniteMass
open scoped Classical

theorem rough_residue_box_uniform_push {ι : Type*} [Fintype ι]
    (A B u : ι → ℤ) (K : ℤ) (hK : 0 < K) :
    (uniformFinsetMass (Fintype.piFinset (fun j =>
      Finset.Ico (roughResidueBoxEndpoint A u K j) (roughResidueBoxEndpoint B u K j)))).mapDomain
      (roughResidueBoxAffine u K) = uniformFinsetMass (alignmentBoxClass A B u K) := by
  rw [uniformFinsetMass_push _ _ (rough_residue_box_affine_injective u K hK.ne')]
  apply congrArg uniformFinsetMass
  ext x
  simpa only [Finset.mem_image] using
    (Finset.ext_iff.mp (rough_residue_box_unrestricted_image A B u K hK) x)

theorem rough_residue_box_step_push {ι : Type*} [Fintype ι]
    (A B a u : ι → ℤ) (t K : ℕ) (ht : 0 < t) (hK : 0 < K) (hcop : t.Coprime K) :
    ∃ v : ι → ℤ,
      (uniformFinsetMass (alignmentBoxClass (roughResidueBoxEndpoint A u K)
        (roughResidueBoxEndpoint B u K) v t)).mapDomain (roughResidueBoxAffine u K) =
      uniformFinsetMass (alignmentBoxClass A B a t ∩ alignmentBoxClass A B u K) := by
  have hp : (0 : ℤ) < K := by exact_mod_cast hK
  obtain ⟨v, hv⟩ := rough_residue_box_step_image A B a u t K ht hK hcop
  refine ⟨v, ?_⟩
  rw [uniformFinsetMass_push _ _ (rough_residue_box_affine_injective u K hp.ne')]
  apply congrArg uniformFinsetMass
  ext x
  simpa only [Finset.mem_image] using (Finset.ext_iff.mp hv x)

theorem rough_residue_box_discrepancy_transport {ι : Type*} [Fintype ι]
    (A B a u : ι → ℤ) (t K : ℕ) (ht : 0 < t) (hK : 0 < K) (hcop : t.Coprime K) :
    ∃ v : ι → ℤ, ∀ f : (ι → ℤ) → ℝ,
      |expectation (uniformFinsetMass (alignmentBoxClass A B a t ∩ alignmentBoxClass A B u K)) f -
        expectation (uniformFinsetMass (alignmentBoxClass A B u K)) f| =
      |expectation (uniformFinsetMass (alignmentBoxClass (roughResidueBoxEndpoint A u K)
          (roughResidueBoxEndpoint B u K) v t)) (fun y => f (roughResidueBoxAffine u K y)) -
        expectation (uniformFinsetMass (Fintype.piFinset (fun j =>
          Finset.Ico (roughResidueBoxEndpoint A u K j) (roughResidueBoxEndpoint B u K j))))
          (fun y => f (roughResidueBoxAffine u K y))| := by
  have hp : (0 : ℤ) < K := by exact_mod_cast hK
  obtain ⟨v, hv⟩ := rough_residue_box_step_push A B a u t K ht hK hcop
  refine ⟨v, fun f => ?_⟩
  rw [← hv, ← rough_residue_box_uniform_push A B u K hp, expectation_push, expectation_push]

end Hindman168
