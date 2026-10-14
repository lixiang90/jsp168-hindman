import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.GroupTheory.Subgroup.Center

/-! The center lattice acts trivially on arbitrary, possibly nonnormal, cosets.
The descended center action is genuinely jointly continuous. -/

namespace Hindman168

variable {G : Type*} [Group G]

theorem central_lattice_smul_trivial (Γ : Subgroup G) (z : Subgroup.center G)
    (hz : (z : G) ∈ Γ) (q : G ⧸ Γ) : (z : G) • q = q := by
  induction q using Quotient.inductionOn with
  | _ g =>
    change ((z : G)*g : G ⧸ Γ) = (g : G ⧸ Γ)
    rw [← Subgroup.mem_center_iff.mp z.property g]
    apply QuotientGroup.eq.mpr
    simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one] using Γ.inv_mem hz

noncomputable def centralCosetAction (Γ : Subgroup G) :
    ((Subgroup.center G) ⧸ Γ.subgroupOf (Subgroup.center G)) → (G ⧸ Γ) → (G ⧸ Γ) :=
  Quotient.lift (fun z : Subgroup.center G => fun q : G ⧸ Γ => (z : G) • q)
    (fun z w hzw => by
      funext q
      have hz : z⁻¹*w ∈ Γ.subgroupOf (Subgroup.center G) :=
        (QuotientGroup.leftRel_apply (s := Γ.subgroupOf (Subgroup.center G))).mp hzw
      have h := central_lattice_smul_trivial Γ (z⁻¹*w) hz q
      have he := congrArg (fun x : G ⧸ Γ => (z : G) • x) h
      change (z : G) • (((z : G)⁻¹*(w : G)) • q) = (z : G) • q at he
      rw [← mul_smul, mul_inv_cancel_left] at he
      exact he.symm)

theorem central_coset_action_mk (Γ : Subgroup G) (z : Subgroup.center G) (q : G ⧸ Γ) :
    centralCosetAction Γ (z : (Subgroup.center G) ⧸ Γ.subgroupOf (Subgroup.center G)) q =
      (z : G) • q := rfl

theorem central_coset_action_one (Γ : Subgroup G) (q : G ⧸ Γ) :
    centralCosetAction Γ (1 : (Subgroup.center G) ⧸ Γ.subgroupOf (Subgroup.center G)) q = q := by
  change (1 : G) • q = q
  exact one_smul G q

theorem central_coset_action_mul (Γ : Subgroup G)
    (z w : (Subgroup.center G) ⧸ Γ.subgroupOf (Subgroup.center G)) (q : G ⧸ Γ) :
    centralCosetAction Γ (z*w) q = centralCosetAction Γ z (centralCosetAction Γ w q) := by
  induction z, w using Quotient.inductionOn₂ with
  | _ z w =>
    change ((z : G)*(w : G)) • q = (z : G) • ((w : G) • q)
    exact mul_smul _ _ _

theorem central_coset_action_commutes (Γ : Subgroup G)
    (z : (Subgroup.center G) ⧸ Γ.subgroupOf (Subgroup.center G)) (g : G) (q : G ⧸ Γ) :
    centralCosetAction Γ z (g • q) = g • centralCosetAction Γ z q := by
  induction z using Quotient.inductionOn with
  | _ z =>
    change (z : G) • (g • q) = g • ((z : G) • q)
    rw [← mul_smul, ← mul_smul, Subgroup.mem_center_iff.mp z.property g]

theorem central_coset_action_continuous [TopologicalSpace G] [IsTopologicalGroup G]
    (Γ : Subgroup G) :
    Continuous (fun p : (((Subgroup.center G) ⧸ Γ.subgroupOf (Subgroup.center G)) × (G ⧸ Γ)) =>
      centralCosetAction Γ p.1 p.2) := by
  rw [← (QuotientGroup.isOpenQuotientMap_mk.prodMap IsOpenQuotientMap.id).continuous_comp_iff]
  exact (continuous_subtype_val.comp continuous_fst).smul continuous_snd

end Hindman168
