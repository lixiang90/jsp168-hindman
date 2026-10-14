import Hindman168.NativeLieExponentialCentralKernel
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Connected.Clopen
import Mathlib.GroupTheory.Subgroup.Centralizer

/-! In the actual connected original Lie group, an element with identity
native adjoint is central. Genuine exponential conjugation first proves
commutation on an actual identity neighborhood; the original centralizer
is then an open-and-closed subgroup, hence the whole connected group. -/

namespace Hindman168
open Function Set Filter Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeLieExponential_commute_of_adjoint_eq_one {g : G}
    (hg : nativeLieAdjoint (I := I) g = 1) (w : E) :
    Commute g (nativeLieExponential (I := I) (G := G) w) := by
  have ha : nativeLieAdjoint (I := I) g w = w := by
    have h := congrArg (fun A : E →L[ℝ] E => A w) hg
    exact h
  have h := nativeLieAdjoint_exponential_conjugation (I := I) g w
  rw [ha] at h
  have he := congrArg (fun x : G => x * g) h
  change g * nativeLieExponential (I := I) (G := G) w =
    nativeLieExponential (I := I) (G := G) w * g
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using he

 theorem nativeLie_mem_center_of_adjoint_eq_one [ConnectedSpace G] {g : G}
    (hg : nativeLieAdjoint (I := I) g = 1) : g ∈ Subgroup.center G := by
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  let C : Subgroup G := Subgroup.centralizer ({g} : Set G)
  have he : ∀ w : E, nativeLieExponential (I := I) (G := G) w ∈ C := by
    intro w
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact (nativeLieExponential_commute_of_adjoint_eq_one hg w).eq.symm
  have hC : (C : Set G) ∈ 𝓝 (1 : G) := by
    apply mem_of_superset (nativeLieExponential_image_mem_nhds (I := I) (G := G)
      (Filter.univ_mem : (univ : Set E) ∈ 𝓝 0))
    rintro x ⟨w, _, rfl⟩
    exact he w
  have hCo : IsOpen (C : Set G) := C.isOpen_of_mem_nhds hC
  have hCc : IsClopen (C : Set G) := ⟨C.isClosed_of_isOpen hCo, hCo⟩
  have htop : (C : Set G) = univ := hCc.eq_univ ⟨1, C.one_mem⟩
  rw [Subgroup.mem_center_iff]
  intro x
  have hx : x ∈ C := by
    change x ∈ (C : Set G)
    rw [htop]
    trivial
  exact Subgroup.mem_centralizer_singleton_iff.mp hx

omit [CompleteSpace E] [BoundarylessManifold I G] [T2Space G] [LieGroup I ∞ G] in
 theorem nativeLieAdjoint_eq_one_of_mem_center {g : G} (hg : g ∈ Subgroup.center G) :
    nativeLieAdjoint (I := I) g = 1 := by
  have he : (fun x : G => g * x * g⁻¹) = id := by
    funext x
    rw [← (Subgroup.mem_center_iff.mp hg x), mul_assoc, mul_inv_cancel, mul_one]
    rfl
  unfold nativeLieAdjoint
  rw [he, mfderiv_id]
  rfl

 theorem nativeLieAdjoint_eq_one_iff_mem_center [ConnectedSpace G] (g : G) :
    nativeLieAdjoint (I := I) g = 1 ↔ g ∈ Subgroup.center G :=
  ⟨nativeLie_mem_center_of_adjoint_eq_one, nativeLieAdjoint_eq_one_of_mem_center⟩

 theorem nativeLiePeriodCurve_mem_center [ConnectedSpace G] [Group.IsNilpotent G]
    {v : E} (hv : nativeLieExponential (I := I) (G := G) v = 1) (t : ℝ) :
    lieOneParameterCurve (I := I) (G := G) v t ∈ Subgroup.center G := by
  apply nativeLie_mem_center_of_adjoint_eq_one (I := I)
  exact nativeLieAdjointCurve_eq_one_of_exponential_eq_one hv t

end Hindman168
