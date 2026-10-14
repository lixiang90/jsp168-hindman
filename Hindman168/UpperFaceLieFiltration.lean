import Hindman168.UpperFaceLieArray
import Mathlib.Tactic

/-! The paper's explicit cube Lie filtration: face D uses layer max(i,|D|).
No lower-central replacement is made. -/
namespace Hindman168
attribute [local instance] pointwiseLieRing pointwiseLieAlgebra
variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

noncomputable def upperFaceLieLayer (F : ℕ → Submodule R L) (d i : ℕ) :
    Submodule R (Finset (Fin d) → L) :=
  Submodule.span R {z | ∃ (D : Finset (Fin d)) (x : L),
    x ∈ F (max i D.card) ∧ z = upperFaceLieArray (R := R) D x}

theorem upper_face_lie_layer_generator (F : ℕ → Submodule R L) (d i : ℕ)
    (D : Finset (Fin d)) (x : L) (hx : x ∈ F (max i D.card)) :
    upperFaceLieArray (R := R) D x ∈ upperFaceLieLayer F d i :=
  Submodule.subset_span ⟨D,x,hx,rfl⟩

theorem upper_face_lie_layer_antitone (F : ℕ → Submodule R L) (hF : Antitone F) (d : ℕ) :
    Antitone (upperFaceLieLayer F d) := by
  intro i j hij
  apply Submodule.span_le.mpr
  rintro z ⟨D,x,hx,rfl⟩
  exact upper_face_lie_layer_generator F d i D x (hF (max_le_max_right _ hij) hx)

theorem upper_face_lie_layer_initial (F : ℕ → Submodule R L) (hF : F 0 = F 1) (d : ℕ) :
    upperFaceLieLayer F d 0 = upperFaceLieLayer F d 1 := by
  have he (D : Finset (Fin d)) : F (max 0 D.card) = F (max 1 D.card) := by
    by_cases hD : D.card = 0
    · simp [hD,hF]
    · rw [max_eq_right (Nat.zero_le _), max_eq_right (by omega)]
  unfold upperFaceLieLayer
  congr 1
  ext z
  simp only [Set.mem_setOf_eq, he]

theorem upper_face_lie_layer_bracket (F : ℕ → Submodule R L) (hF : Antitone F)
    (hB : ∀ i j x y, x ∈ F i → y ∈ F j → ⁅x,y⁆ ∈ F (i+j))
    (d i j : ℕ) {x y : Finset (Fin d) → L}
    (hx : x ∈ upperFaceLieLayer F d i) (hy : y ∈ upperFaceLieLayer F d j) :
    ⁅x,y⁆ ∈ upperFaceLieLayer F d (i+j) := by
  refine Submodule.span_induction₂
    (p := fun x y _ _ => ⁅x,y⁆ ∈ upperFaceLieLayer F d (i+j))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨D,a,ha,rfl⟩ ⟨E,b,hb,rfl⟩
    rw [upper_face_lie_array_bracket]
    apply upper_face_lie_layer_generator
    apply hF _ (hB _ _ a b ha hb)
    exact max_le (add_le_add (le_max_left _ _) (le_max_left _ _))
      ((Finset.card_union_le D E).trans (add_le_add (le_max_right _ _) (le_max_right _ _)))
  · intro y _; rw [zero_lie]; exact Submodule.zero_mem _
  · intro x _; rw [lie_zero]; exact Submodule.zero_mem _
  · intro x y z _ _ _ hx hy; rw [add_lie]; exact Submodule.add_mem _ hx hy
  · intro x y z _ _ _ hx hy; rw [lie_add]; exact Submodule.add_mem _ hx hy
  · intro r x y _ _ h; rw [smul_lie]; exact Submodule.smul_mem _ r h
  · intro r x y _ _ h; rw [lie_smul]; exact Submodule.smul_mem _ r h

theorem upper_face_lie_layer_terminal (F : ℕ → Submodule R L) (hF : Antitone F)
    (d k : ℕ) (hk : F k = ⊥) : upperFaceLieLayer F d k = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro _ ⟨D,x,hx,rfl⟩
  have hzero : x = 0 := by
    have hm := hF (le_max_left k D.card) hx
    simpa only [hk, Submodule.mem_bot] using hm
  simp [hzero]

noncomputable def upperFaceLieAlgebra (F : ℕ → Submodule R L) (hF : Antitone F)
    (hB : ∀ i j x y, x ∈ F i → y ∈ F j → ⁅x,y⁆ ∈ F (i+j)) (d : ℕ) :
    LieSubalgebra R (Finset (Fin d) → L) where
  toSubmodule := upperFaceLieLayer F d 0
  lie_mem' := upper_face_lie_layer_bracket F hF hB d 0 0

end Hindman168
