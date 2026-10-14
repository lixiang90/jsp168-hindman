import Hindman168.AlignmentJointNativeCompleteCylinderPool
import Hindman168.ContinuousCylinderMeanTransfer

/-! One finite ORIGINAL cylinder detector list controls EVERY bounded/Lipschitz
test of the actual native quotient. The list and positive tolerance precede
both arbitrary empirical sample sets and their maps into the native quotient. -/
namespace Hindman168
open FiniteMass
open scoped Manifold ContDiff Classical NNReal Topology
universe u

variable {ι : Type} [Fintype ι] {σ : ι → Type} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → σ ν → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))

theorem alignment_joint_native_complete_cylinder_detection (B : ℝ) (L : NNReal)
    (η : ℝ) (hη : 0 < η) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    letI : CompactSpace (J.G ⧸ J.Γ) := native_metric_quotient_compact J
    ∃ (Q : Finset (List C(J.G ⧸ J.Γ,ℂ))) (τ : ℝ), 0 < τ ∧
      (∀ l ∈ Q, ∀ f ∈ l, f ∈ alignmentJointNativeCylinderGenerators D n v hv) ∧
      ∀ {α β : Type} (S : Finset α) (T : Finset β)
        (x : α → J.G ⧸ J.Γ) (y : β → J.G ⧸ J.Γ)
        (F : C(J.G ⧸ J.Γ,ℂ)),
        F ∈ boundedComplexLipschitzObservables (J.G ⧸ J.Γ) B L →
        η ≤ ‖complexExpectation (uniformFinsetMass S) (fun a => F (x a))-
          complexExpectation (uniformFinsetMass T) (fun b => F (y b))‖ →
        ∃ l ∈ Q, τ ≤ ‖complexExpectation (uniformFinsetMass S) (fun a => l.prod (x a))-
          complexExpectation (uniformFinsetMass T) (fun b => l.prod (y b))‖ := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (J.G ⧸ J.Γ) := native_metric_quotient_compact J
  obtain ⟨P,terms,pool,R,hR,hpool,hterms,hclose⟩ :=
    alignment_joint_native_complete_cylinder_pool D n v hv B L (η/4) (by positivity)
  let Q := P.biUnion (fun G => ((terms G).map Prod.snd).toFinset)
  refine ⟨Q,η/(2*R),by positivity,?_,?_⟩
  · intro l hl f hf
    obtain ⟨G,hG,hl⟩ := Finset.mem_biUnion.mp hl
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hl)
    exact hpool f ((hterms G hG).2.1 t ht f hf)
  · intro α β S T x y F hF hbad
    obtain ⟨G,hG,hFG⟩ := hclose F hF
    rw [(hterms G hG).1] at hFG
    obtain ⟨t,ht,hdetect⟩ := continuous_cylinder_approximant_detects S T x y F (terms G)
      η R hη hR hFG (hterms G hG).2.2 hbad
    exact ⟨t.2,Finset.mem_biUnion.mpr
      ⟨G,hG,List.mem_toFinset.mpr (List.mem_map.mpr ⟨t,ht,rfl⟩)⟩,hdetect⟩

end Hindman168
