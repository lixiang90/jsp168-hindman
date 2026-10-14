import Hindman168.AlignmentJointNativeCylinderLists

/-! COMPLETE numerical tests on ACTUAL native quotient have ONE finite
original cylinder-observer/slot pool and strict coefficient budget BEFORE
all original source formulae, endpoints/residues and posterior samples. -/
namespace Hindman168
open scoped Manifold ContDiff Classical NNReal Topology
universe u

variable {ι : Type} [Fintype ι] {σ : ι → Type} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → σ ν → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))

theorem alignment_joint_native_complete_cylinder_pool (B : ℝ) (L : NNReal) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    letI : CompactSpace (J.G ⧸ J.Γ) := native_metric_quotient_compact J
    ∀ ε : ℝ, 0 < ε →
      ∃ (P : Finset C(J.G ⧸ J.Γ,ℂ))
        (terms : C(J.G ⧸ J.Γ,ℂ) → List (ℂ × List C(J.G ⧸ J.Γ,ℂ)))
        (pool : Finset C(J.G ⧸ J.Γ,ℂ)) (R : ℝ), 0 < R ∧
        (∀ f ∈ pool, f ∈ alignmentJointNativeCylinderGenerators D n v hv) ∧
        (∀ G ∈ P, G=continuousCylinderLinearCombination (terms G) ∧
          (∀ t ∈ terms G, ∀ f ∈ t.2, f ∈ pool) ∧
          ((terms G).map (fun t => ‖t.1‖)).sum < R) ∧
        ∀ F ∈ boundedComplexLipschitzObservables (J.G ⧸ J.Γ) B L,
          ∃ G ∈ P, ‖F-G‖ < ε := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (J.G ⧸ J.Γ) := native_metric_quotient_compact J
  intro ε hε
  obtain ⟨P,hP,hclose⟩ := alignment_joint_native_compact_cylinder_approximation D n v hv
    (boundedComplexLipschitzObservables (J.G ⧸ J.Γ) B L)
    (bounded_complex_lipschitz_observables_compact (J.G ⧸ J.Γ) B L) ε hε
  have ha : ∀ G : C(J.G ⧸ J.Γ,ℂ), ∃ l : List (ℂ × List C(J.G ⧸ J.Γ,ℂ)),
      G ∈ P → (∀ t ∈ l, ∀ f ∈ t.2, f ∈ alignmentJointNativeCylinderGenerators D n v hv) ∧
        G=continuousCylinderLinearCombination l := by
    intro G
    by_cases hg : G ∈ P
    · obtain ⟨l,hl,he⟩ := alignment_joint_native_cylinder_list_representation D n v hv G (hP G hg)
      exact ⟨l,fun _ => ⟨hl,he⟩⟩
    · exact ⟨[],fun h => (hg h).elim⟩
  choose terms hterms using ha
  let pool := P.biUnion (fun G => ((terms G).flatMap Prod.snd).toFinset)
  have hpool : ∀ f ∈ pool, f ∈ alignmentJointNativeCylinderGenerators D n v hv := by
    intro f hf
    obtain ⟨G,hG,hf⟩ := Finset.mem_biUnion.mp hf
    obtain ⟨t,ht,hf⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hf)
    exact (hterms G hG).1 t ht f hf
  let size (G : C(J.G ⧸ J.Γ,ℂ)) := ((terms G).map (fun t => ‖t.1‖)).sum
  have hsize (G : C(J.G ⧸ J.Γ,ℂ)) : 0 ≤ size G := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨t,_ht,rfl⟩ := List.mem_map.mp hx
    exact norm_nonneg t.1
  have htotal : 0 ≤ ∑ G ∈ P, size G := Finset.sum_nonneg (fun G _ => hsize G)
  let R : ℝ := 1+∑ G ∈ P, size G
  refine ⟨P,terms,pool,R,by dsimp only [R]; linarith,hpool,?_,hclose⟩
  intro G hG
  refine ⟨(hterms G hG).2,?_,?_⟩
  · intro t ht f hf
    exact Finset.mem_biUnion.mpr ⟨G,hG,List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨t,ht,hf⟩)⟩
  · have hs := Finset.single_le_sum (f := size) (fun G _ => hsize G) hG
    change size G < R
    dsimp only [R]
    linarith

end Hindman168
