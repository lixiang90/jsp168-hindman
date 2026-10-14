import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Compactness.Compact

/-! The covering-space step in Proposition 7.5.  If a continuous map starts
in a subgroup cover and its quotient image stays in the embedded subgroup
orbit, uniqueness of lifts forces the original map itself to stay in that
cover.  The lift is constructed by the genuine covering lifting theorem. -/
namespace Hindman168
open Function Set Topology

 theorem affineShear_cover_range_lifting
    {A G H X Y : Type*} [TopologicalSpace A] [TopologicalSpace G]
    [TopologicalSpace H] [TopologicalSpace X] [TopologicalSpace Y]
    [SimplyConnectedSpace A] [LocallyPathConnectedSpace A]
    (p : G → X) (q : H → Y) (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    (i : H → G) (hi : Continuous i) (j : Y → X) (hj : IsEmbedding j)
    (hcomm : p ∘ i = j ∘ q) (f : A → G) (hf : Continuous f)
    (a₀ : A) (h₀ : H) (hstart : f a₀ = i h₀)
    (hrange : ∀ a, p (f a) ∈ range j) :
    ∀ a, f a ∈ range i := by
  choose g hg using hrange
  have hgcont : Continuous g := hj.isInducing.continuous_iff.mpr (by
    have he : j ∘ g = p ∘ f := funext hg
    rw [he]
    exact hp.continuous.comp hf)
  have hbase : q h₀ = g a₀ := by
    apply hj.injective
    calc
      j (q h₀) = p (i h₀) := (congrFun hcomm h₀).symm
      _ = p (f a₀) := congrArg p hstart.symm
      _ = j (g a₀) := (hg a₀).symm
  obtain ⟨F, ⟨hFstart, hFlift⟩, _⟩ := hq.existsUnique_continuousMap_lifts
    ⟨g, hgcont⟩ a₀ h₀ hbase
  have hsame : p ∘ f = p ∘ (i ∘ F) := by
    funext a
    calc
      p (f a) = j (g a) := (hg a).symm
      _ = j (q (F a)) := congrArg j (congrFun hFlift a).symm
      _ = p (i (F a)) := (congrFun hcomm (F a)).symm
  have he : f = i ∘ F := hp.eq_of_comp_eq hf (hi.comp F.continuous) hsame a₀ (by
    change f a₀ = i (F a₀)
    rw [hFstart]
    exact hstart)
  intro a
  exact ⟨F a, (congrFun he a).symm⟩

/-- Compact embedded quotient orbits supply the embedding required above;
only continuity and injectivity of the actual orbit map are needed. -/
 theorem affineShear_compact_cover_range_lifting
    {A G H X Y : Type*} [TopologicalSpace A] [TopologicalSpace G]
    [TopologicalSpace H] [TopologicalSpace X] [TopologicalSpace Y]
    [SimplyConnectedSpace A] [LocallyPathConnectedSpace A]
    [CompactSpace Y] [T2Space X]
    (p : G → X) (q : H → Y) (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    (i : H → G) (hi : Continuous i) (j : Y → X)
    (hj : Continuous j) (hinj : Injective j)
    (hcomm : p ∘ i = j ∘ q) (f : A → G) (hf : Continuous f)
    (a₀ : A) (h₀ : H) (hstart : f a₀ = i h₀)
    (hrange : ∀ a, p (f a) ∈ range j) :
    ∀ a, f a ∈ range i :=
  affineShear_cover_range_lifting p q hp hq i hi j
    (hj.isClosedEmbedding hinj).isEmbedding hcomm f hf a₀ h₀ hstart hrange

/-- Product ambient covers need only coordinatewise uniqueness of lifts.
This avoids assuming a covering structure for a recursively encoded product. -/
 theorem affineShear_pi_cover_range_lifting
    {ι A G H X Y : Type*} [TopologicalSpace A] [TopologicalSpace G]
    [TopologicalSpace H] [TopologicalSpace X] [TopologicalSpace Y]
    [SimplyConnectedSpace A] [LocallyPathConnectedSpace A]
    [CompactSpace Y] [T2Space X]
    (p : G → X) (q : H → Y) (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    (i : H → (ι → G)) (hi : Continuous i) (j : Y → (ι → X))
    (hj : Continuous j) (hinj : Injective j)
    (hcomm : ∀ y v, p (i y v) = j (q y) v)
    (f : A → (ι → G)) (hf : Continuous f)
    (a₀ : A) (h₀ : H) (hstart : f a₀ = i h₀)
    (hrange : ∀ a, (fun v => p (f a v)) ∈ range j) :
    ∀ a, f a ∈ range i := by
  choose g hg using hrange
  have hemb := (hj.isClosedEmbedding hinj).isEmbedding
  have hgcont : Continuous g := hemb.isInducing.continuous_iff.mpr (by
    have he : j ∘ g = fun a v => p (f a v) := funext hg
    rw [he]
    exact continuous_pi (fun v => hp.continuous.comp ((continuous_apply v).comp hf)))
  have hbase : q h₀ = g a₀ := by
    apply hinj
    funext v
    calc
      j (q h₀) v = p (i h₀ v) := (hcomm h₀ v).symm
      _ = p (f a₀ v) := congrArg (fun z => p (z v)) hstart.symm
      _ = j (g a₀) v := (congrFun (hg a₀) v).symm
  obtain ⟨F, ⟨hFstart, hFlift⟩, _⟩ := hq.existsUnique_continuousMap_lifts
    ⟨g, hgcont⟩ a₀ h₀ hbase
  have he (v : ι) : (fun a => f a v) = fun a => i (F a) v := by
    refine hp.eq_of_comp_eq ((continuous_apply v).comp hf)
      ((continuous_apply v).comp (hi.comp F.continuous)) ?_ a₀ ?_
    · funext a
      calc
        p (f a v) = j (g a) v := (congrFun (hg a) v).symm
        _ = j (q (F a)) v := congrArg (fun y => j y v) (congrFun hFlift a).symm
        _ = p (i (F a) v) := (hcomm (F a) v).symm
    · change f a₀ v = i (F a₀) v
      rw [hFstart]
      exact congrFun hstart v
  intro a
  exact ⟨F a, funext (fun v => (congrFun (he v) a).symm)⟩

end Hindman168
