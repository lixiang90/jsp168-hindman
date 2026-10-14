import Hindman168.CompactQuotientFinitePatches
import Hindman168.FinitePatchTransversal
import Mathlib.Topology.Covering.Quotient
import Mathlib.MeasureTheory.Measure.Haar.Quotient

namespace Hindman168
open Set MeasureTheory Measure
open scoped Classical

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

theorem discrete_cocompact_transversal (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    ∃ F K : Set G, MeasurableSet F ∧ IsCompact K ∧ F ⊆ K ∧
      F.InjOn ((↑) : G → G ⧸ Γ) ∧ ∀ y : G ⧸ Γ, ∃ x ∈ F, (x : G ⧸ Γ) = y := by
  letI : MeasurableSpace (G ⧸ Γ) := borel (G ⧸ Γ)
  letI : BorelSpace (G ⧸ Γ) := ⟨rfl⟩
  let π := ((↑) : G → G ⧸ Γ)
  have hcov := (Γ.isQuotientCoveringMap (SetLike.isDiscrete_iff_discreteTopology.mpr
    (inferInstance : DiscreteTopology Γ))).isCoveringMap
  obtain ⟨m, K, hK, hcover⟩ := compact_quotient_finite_patches π
    QuotientGroup.isOpenMap_coe QuotientGroup.mk_surjective hcov.isLocalHomeomorph.isLocallyInjective
  let U := fun i => interior (K i)
  refine ⟨finitePatchTransversal π U, ⋃ i, K i,
    finite_patch_transversal_measurable π U QuotientGroup.continuous_mk QuotientGroup.isOpenMap_coe
      (fun _ => isOpen_interior), isCompact_iUnion (fun i => (hK i).1),
    finite_patch_transversal_subset π U K (fun _ => interior_subset),
    finite_patch_transversal_injective π U (fun i => (hK i).2),
    finite_patch_transversal_surjective π U hcover⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [MeasurableSpace G] [BorelSpace G] in
theorem coset_transversal_unique_op_translate (Γ : Subgroup G) (F : Set G)
    (hinj : F.InjOn ((↑) : G → G ⧸ Γ))
    (hcover : ∀ y : G ⧸ Γ, ∃ x ∈ F, (x : G ⧸ Γ) = y) (x : G) :
    ∃! a : Γ.op, a • x ∈ F := by
  obtain ⟨y, hyF, hy⟩ := hcover (x : G ⧸ Γ)
  have hxy : x⁻¹*y ∈ Γ := QuotientGroup.eq.mp hy.symm
  let a : Γ.op := ⟨MulOpposite.op (x⁻¹*y), hxy⟩
  have ha : a • x = y := by
    change x*(x⁻¹*y) = y
    group
  refine ⟨a, ?_, ?_⟩
  · change x*(x⁻¹*y) ∈ F
    simpa only [mul_inv_cancel_left] using hyF
  intro b hb
  have hbπ : ((b • x : G) : G ⧸ Γ) = (x : G ⧸ Γ) := by
    symm
    apply QuotientGroup.eq.mpr
    change x⁻¹*(x*b.val.unop) ∈ Γ
    simpa only [inv_mul_cancel_left] using (Subgroup.mem_op.mp b.property)
  have hby : b • x = y := hinj hb hyF (hbπ.trans hy.symm)
  apply Subtype.ext
  apply MulOpposite.unop_injective
  apply mul_left_cancel (a := x)
  change b • x = a • x
  exact hby.trans ha.symm

theorem discrete_cocompact_fundamental_domain (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] [Countable Γ]
    (μ : Measure G) [IsHaarMeasure μ] [IsMulRightInvariant μ] :
    ∃ F : Set G, MeasurableSet F ∧ IsFundamentalDomain Γ.op F μ ∧ 0 < μ F ∧ μ F < ⊤ ∧
      ∃ K : Set G, IsCompact K ∧ F ⊆ K := by
  obtain ⟨F, K, hF, hK, hFK, hinj, hcover⟩ := discrete_cocompact_transversal Γ
  have hfund : IsFundamentalDomain Γ.op F μ :=
    IsFundamentalDomain.mk' hF.nullMeasurableSet (coset_transversal_unique_op_translate Γ F hinj hcover)
  have hμ : μ ≠ 0 := by
    intro hz
    have hu := isOpen_univ.measure_ne_zero μ (Set.univ_nonempty : (Set.univ : Set G).Nonempty)
    exact hu (by rw [hz]; rfl)
  exact ⟨F, hF, hfund, (hfund.measure_ne_zero hμ).bot_lt,
    (measure_mono hFK).trans_lt hK.measure_lt_top, K, hK, hFK⟩

end Hindman168
