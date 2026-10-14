import Hindman168.NilLowerCentralFiltration
import Mathlib.Topology.Algebra.Group.Basic

/-! Closed lower-central layers form an actual filtration in any
Hausdorff topological nilpotent group. This does not assert rationality
or cocompactness of a restricted lattice. -/

namespace Hindman168
open scoped commutatorElement

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem topologicalClosure_commutator_le (A B C : Subgroup G) (h : ⁅A, B⁆ ≤ C) :
    ⁅A.topologicalClosure, B.topologicalClosure⁆ ≤ C.topologicalClosure := by
  apply Subgroup.commutator_le.mpr
  intro g hg k hk
  let f : G × G → G := fun z => ⁅z.1, z.2⁆
  have hf : Continuous f := by
    dsimp [f]
    simp only [commutatorElement_def]
    exact ((continuous_fst.mul continuous_snd).mul continuous_fst.inv).mul continuous_snd.inv
  have hs : (A : Set G) ×ˢ (B : Set G) ⊆ f ⁻¹' (C.topologicalClosure : Set G) := by
    intro z hz
    exact C.le_topologicalClosure (h (Subgroup.commutator_mem_commutator hz.1 hz.2))
  have hc := closure_minimal hs (C.isClosed_topologicalClosure.preimage hf)
  change (g, k) ∈ f ⁻¹' (C.topologicalClosure : Set G)
  apply hc
  simpa only [closure_prod_eq, Subgroup.topologicalClosure_coe] using
    (show (g, k) ∈ (A.topologicalClosure : Set G) ×ˢ (B.topologicalClosure : Set G) from ⟨hg, hk⟩)

theorem CubeGroupFiltration.topologicalClosure {F : ℕ → Subgroup G}
    (hF : CubeGroupFiltration F) : CubeGroupFiltration (fun i => (F i).topologicalClosure) := by
  refine ⟨fun i j hij => Subgroup.topologicalClosure_mono (hF.antitone hij), ?_⟩
  intro i j g hg k hk
  exact topologicalClosure_commutator_le (F i) (F j) (F (i+j))
    (Subgroup.commutator_le.mpr (hF.commutator_mem i j))
    (Subgroup.commutator_mem_commutator hg hk)

def nilClosedLowerCentralFiltration (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (i : ℕ) : Subgroup G :=
  (nilLowerCentralFiltration G i).topologicalClosure

theorem nilClosedLowerCentralFiltration_zero : nilClosedLowerCentralFiltration G 0 = ⊤ := by
  apply top_unique
  exact (nilLowerCentralFiltration_zero (G := G)) ▸ (Subgroup.le_topologicalClosure _)

theorem nilClosedLowerCentralFiltration_one : nilClosedLowerCentralFiltration G 1 = ⊤ := by
  apply top_unique
  exact (nilLowerCentralFiltration_one (G := G)) ▸ (Subgroup.le_topologicalClosure _)

theorem nilClosedLowerCentralFiltration_conditions :
    CubeGroupFiltration (nilClosedLowerCentralFiltration G) :=
  (nilLowerCentralFiltration_conditions (G := G)).topologicalClosure

theorem nilClosedLowerCentralFiltration_isClosed (i : ℕ) :
    IsClosed (nilClosedLowerCentralFiltration G i : Set G) := Subgroup.isClosed_topologicalClosure _

theorem nilClosedLowerCentralFiltration_contains (i : ℕ) :
    nilLowerCentralFiltration G i ≤ nilClosedLowerCentralFiltration G i :=
  Subgroup.le_topologicalClosure _

theorem nilClosedLowerCentralFiltration_eq_of_isClosed (i : ℕ)
    (hc : IsClosed (nilLowerCentralFiltration G i : Set G)) :
    nilClosedLowerCentralFiltration G i = nilLowerCentralFiltration G i := by
  exact le_antisymm (Subgroup.topologicalClosure_minimal _ le_rfl hc)
    (Subgroup.le_topologicalClosure _)

theorem nilClosedLowerCentralFiltration_terminal [T1Space G] [Group.IsNilpotent G]
    {s : ℕ} (hs : Group.nilpotencyClass G ≤ s) :
    nilClosedLowerCentralFiltration G (s+1) = ⊥ := by
  dsimp [nilClosedLowerCentralFiltration]
  rw [nilLowerCentralFiltration_terminal hs]
  apply SetLike.ext'
  simp only [Subgroup.topologicalClosure_coe, Subgroup.coe_bot, isClosed_singleton.closure_eq]

theorem nilClosedLowerCentralFiltration_beyond_terminal [T1Space G] [Group.IsNilpotent G]
    {s i : ℕ} (hs : Group.nilpotencyClass G ≤ s) (hi : s+1 ≤ i) :
    nilClosedLowerCentralFiltration G i = ⊥ := by
  apply le_antisymm _ bot_le
  rw [← nilClosedLowerCentralFiltration_terminal hs]
  exact nilClosedLowerCentralFiltration_conditions.antitone hi

theorem nilClosedLowerCentralFiltration_normal (i : ℕ) :
    (nilClosedLowerCentralFiltration G i).Normal := Subgroup.is_normal_topologicalClosure _

attribute [instance] nilClosedLowerCentralFiltration_normal

end Hindman168
