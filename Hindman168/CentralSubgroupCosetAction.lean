import Hindman168.CentralCosetAction

/-! ACTUAL arbitrary central subgroup modulo its ORIGINAL lattice
intersection acts on original possibly NONNORMAL lattice cosets. -/

namespace Hindman168
variable {G : Type*} [Group G]

theorem central_subgroup_lattice_normal (N Γ : Subgroup G) (hN : N ≤ Subgroup.center G) :
    (Γ.comap N.subtype).Normal := by
  refine ⟨?_⟩
  intro a ha g
  have he : g*a = a*g := Subtype.ext (Subgroup.mem_center_iff.mp (hN a.property) (g : G))
  simpa only [he,mul_inv_cancel_right] using ha

noncomputable def centralSubgroupCosetAction (N Γ : Subgroup G) (hN : N ≤ Subgroup.center G) :
    (N ⧸ Γ.comap N.subtype) → (G ⧸ Γ) → (G ⧸ Γ) :=
  Quotient.lift (fun z : N => fun q : G ⧸ Γ => (z : G) • q)
    (fun z w hzw => by
      funext q
      have hz : z⁻¹*w ∈ Γ.comap N.subtype :=
        (QuotientGroup.leftRel_apply (s := Γ.comap N.subtype)).mp hzw
      have h := central_lattice_smul_trivial Γ ⟨(z⁻¹*w : N),hN (z⁻¹*w).property⟩ hz q
      have he := congrArg (fun x : G ⧸ Γ => (z : G) • x) h
      change (z : G) • (((z : G)⁻¹*(w : G)) • q) = (z : G) • q at he
      rw [← mul_smul,mul_inv_cancel_left] at he
      exact he.symm)

theorem central_subgroup_coset_action_mk (N Γ : Subgroup G) (hN : N ≤ Subgroup.center G)
    (z : N) (q : G ⧸ Γ) :
    centralSubgroupCosetAction N Γ hN (z : N ⧸ Γ.comap N.subtype) q = (z : G) • q := rfl

theorem central_subgroup_coset_action_continuous [TopologicalSpace G] [IsTopologicalGroup G]
    (N Γ : Subgroup G) (hN : N ≤ Subgroup.center G) :
    Continuous (fun p : (N ⧸ Γ.comap N.subtype) × (G ⧸ Γ) => centralSubgroupCosetAction N Γ hN p.1 p.2) := by
  rw [← (QuotientGroup.isOpenQuotientMap_mk.prodMap IsOpenQuotientMap.id).continuous_comp_iff]
  exact (continuous_subtype_val.comp continuous_fst).smul continuous_snd

theorem central_subgroup_coset_action_one (N Γ : Subgroup G) (hN : N ≤ Subgroup.center G)
    (q : G ⧸ Γ) :
    letI := central_subgroup_lattice_normal N Γ hN
    centralSubgroupCosetAction N Γ hN (1 : N ⧸ Γ.comap N.subtype) q = q := by
  letI := central_subgroup_lattice_normal N Γ hN
  change (1 : G) • q = q
  exact one_smul G q

theorem central_subgroup_coset_action_mul (N Γ : Subgroup G) (hN : N ≤ Subgroup.center G)
    (z w : N ⧸ Γ.comap N.subtype) (q : G ⧸ Γ) :
    letI := central_subgroup_lattice_normal N Γ hN
    centralSubgroupCosetAction N Γ hN (z*w) q =
      centralSubgroupCosetAction N Γ hN z (centralSubgroupCosetAction N Γ hN w q) := by
  letI := central_subgroup_lattice_normal N Γ hN
  induction z,w using Quotient.inductionOn₂ with
  | _ z w => exact mul_smul (z : G) (w : G) q

theorem central_subgroup_coset_action_commutes (N Γ : Subgroup G) (hN : N ≤ Subgroup.center G)
    (z : N ⧸ Γ.comap N.subtype) (g : G) (q : G ⧸ Γ) :
    centralSubgroupCosetAction N Γ hN z (g • q) = g • centralSubgroupCosetAction N Γ hN z q := by
  induction z using Quotient.inductionOn with
  | _ z =>
    change (z : G) • (g • q) = g • ((z : G) • q)
    rw [← mul_smul,← mul_smul,Subgroup.mem_center_iff.mp (hN z.property) g]

end Hindman168
