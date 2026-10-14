import Hindman168.UpperFaceLieFiltration
import Mathlib.Data.Finset.Powerset

/-! Boolean upper-face vectors are linearly independent; all coefficients
are recovered from actual vertex values. -/
namespace Hindman168
open scoped BigOperators
attribute [local instance] pointwiseLieRing pointwiseLieAlgebra
variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] {d : ℕ}

noncomputable def upperFaceLieSum (a : Finset (Fin d) → L) : Finset (Fin d) → L :=
  ∑ D, upperFaceLieArray (R := R) D (a D)

theorem upper_face_lie_sum_vertex (a : Finset (Fin d) → L) (V : Finset (Fin d)) :
    upperFaceLieSum (R := R) a V = ∑ D ∈ V.powerset, a D := by
  classical
  change (∑ D, upperFaceLieArray (R := R) D (a D)) V = _
  simp only [Finset.sum_apply]
  change (∑ D, if D ⊆ V then a D else 0) = _
  rw [← Finset.sum_filter]
  congr 1
  ext D
  simp

theorem upper_face_lie_sum_zero (a : Finset (Fin d) → L)
    (ha : upperFaceLieSum (R := R) a = 0) : a = 0 := by
  classical
  funext V
  refine Finset.strongInductionOn V ?_
  intro V ih
  have hv : (∑ D ∈ V.powerset, a D) = 0 := by
    rw [← upper_face_lie_sum_vertex (R := R)]
    exact congrFun ha V
  have hs : (∑ D ∈ V.powerset, a D) = a V := by
    apply Finset.sum_eq_single V
    · intro D hD hne
      exact ih D (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.mem_powerset.mp hD,hne⟩)
    · simp
  exact hs.symm.trans hv

theorem upper_face_lie_sum_injective :
    Function.Injective (upperFaceLieSum (R := R) (L := L) (d := d)) := by
  classical
  intro a b hab
  have hz : upperFaceLieSum (R := R) (a-b) = 0 := by
    simp only [upperFaceLieSum, Pi.sub_apply, map_sub, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr hab
  exact sub_eq_zero.mp (upper_face_lie_sum_zero (R := R) _ hz)

theorem upper_face_lie_layer_sum_mem (F : ℕ → Submodule R L) (i : ℕ)
    (a : Finset (Fin d) → L) (ha : ∀ D, a D ∈ F (max i D.card)) :
    upperFaceLieSum (R := R) a ∈ upperFaceLieLayer F d i := by
  apply Submodule.sum_mem
  intro D _
  exact upper_face_lie_layer_generator F d i D (a D) (ha D)

theorem upper_face_lie_layer_coordinates (F : ℕ → Submodule R L) (i : ℕ)
    (z : Finset (Fin d) → L) (hz : z ∈ upperFaceLieLayer F d i) :
    ∃! a : Finset (Fin d) → L, (∀ D, a D ∈ F (max i D.card)) ∧ upperFaceLieSum (R := R) a = z := by
  classical
  have he : ∃ a : Finset (Fin d) → L,
      (∀ D, a D ∈ F (max i D.card)) ∧ upperFaceLieSum (R := R) a = z := by
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨D,x,hx,rfl⟩ := hz
      refine ⟨fun E => if E=D then x else 0, ?_, ?_⟩
      · intro E; by_cases hE : E=D
        · simpa only [hE, if_true] using hx
        · simp [hE]
      · simp [upperFaceLieSum, apply_ite]
    | zero =>
      exact ⟨0,fun D => (F _).zero_mem,by simp [upperFaceLieSum]⟩
    | add x y _ _ hx hy =>
      obtain ⟨a,ha,rfl⟩ := hx
      obtain ⟨b,hb,rfl⟩ := hy
      refine ⟨a+b,fun D => (F _).add_mem (ha D) (hb D),?_⟩
      simp only [upperFaceLieSum, Pi.add_apply, map_add, Finset.sum_add_distrib]
    | smul r x _ hx =>
      obtain ⟨a,ha,rfl⟩ := hx
      refine ⟨r • a,fun D => (F _).smul_mem r (ha D),?_⟩
      simp only [upperFaceLieSum, Pi.smul_apply, map_smul, Finset.smul_sum]
  obtain ⟨a,ha,haz⟩ := he
  refine ⟨a,⟨ha,haz⟩,?_⟩
  rintro b ⟨_,hbz⟩
  exact upper_face_lie_sum_injective (R := R) (hbz.trans haz.symm)

end Hindman168
