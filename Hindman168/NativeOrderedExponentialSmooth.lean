import Hindman168.NativeOrderedExponentialCoordinates
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

namespace Hindman168
open scoped Manifold ContDiff

variable {F E : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace F M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]

attribute [local instance] lieGroup_smooth_min_three

omit [CompleteSpace E] [BoundarylessManifold I G] [T2Space G] in
theorem native_smooth_ordered_list_product (l : List (M → G))
    (hl : ∀ f ∈ l, ContMDiff 𝓘(ℝ, F) I ∞ f) :
    ContMDiff 𝓘(ℝ, F) I ∞ (fun x => (l.map (fun f => f x)).prod) := by
  induction l with
  | nil => simpa only [List.map_nil, List.prod_nil] using
      (contMDiff_const : ContMDiff 𝓘(ℝ, F) I ∞ (fun _ : M => (1 : G)))
  | cons f l ih =>
      have h := (hl f (List.mem_cons_self)).mul
        (ih (fun g hg => hl g (List.mem_cons_of_mem f hg)))
      change ContMDiff 𝓘(ℝ, F) I ∞
        (fun x => f x * (l.map (fun g => g x)).prod) at h
      simpa only [List.map_cons, List.prod_cons] using h

theorem native_ordered_exponential_coordinates_contMDiff {m : ℕ} (v : Fin m → E) :
    ContMDiff 𝓘(ℝ, Fin m → ℝ) I ∞
      (nativeOrderedExponentialCoordinates (I := I) (G := G) v) := by
  have hf : ∀ i : Fin m, ContMDiff 𝓘(ℝ, Fin m → ℝ) I ∞
      (fun x : Fin m → ℝ => nativeLieExponential (I := I) (G := G) (x i • v i)) := by
    intro i
    have hx : ContDiff ℝ ∞ (fun x : Fin m → ℝ => x i • v i) :=
      (contDiff_apply ℝ ℝ i).smul contDiff_const
    exact (nativeLieExponential_contMDiff (I := I) (G := G)).comp hx.contMDiff
  have hp := native_smooth_ordered_list_product
    (F := Fin m → ℝ) (M := Fin m → ℝ) (I := I) (List.ofFn (fun i : Fin m => fun x : Fin m → ℝ =>
      nativeLieExponential (I := I) (G := G) (x i • v i))) (by
        intro f hf'
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf'
        exact hf i)
  have he : (fun x : Fin m → ℝ =>
      ((List.ofFn (fun i : Fin m => fun x : Fin m → ℝ =>
        nativeLieExponential (I := I) (G := G) (x i • v i))).map (fun f => f x)).prod) =
      nativeOrderedExponentialCoordinates (I := I) (G := G) v := by
    funext x
    simp only [List.map_ofFn, Function.comp_def, nativeOrderedExponentialCoordinates]
  rw [he] at hp
  exact hp

end Hindman168
