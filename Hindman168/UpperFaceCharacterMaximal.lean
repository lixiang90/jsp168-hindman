import Hindman168.UpperFaceCharacterBracket
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat

/-! The maximal nonzero level is selected across ALL faces of the SAME
filtration. Nontriviality is detected from the actual spanning face arrays. -/
namespace Hindman168
attribute [local instance] pointwiseLieRing pointwiseLieAlgebra
variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

theorem upper_face_character_nonzero_generator (F : ℕ → Submodule R L) (d : ℕ)
    (chi : (Finset (Fin d) → L) →ₗ[R] R)
    (hne : ∃ z ∈ upperFaceLieLayer F d 0, chi z ≠ 0) :
    ∃ D : Finset (Fin d), ∃ x ∈ F D.card, chi (upperFaceLieArray (R := R) D x) ≠ 0 := by
  by_contra! h
  have hLe : upperFaceLieLayer F d 0 ≤ chi.ker := by
    apply Submodule.span_le.mpr
    rintro z ⟨D,x,hx,rfl⟩
    exact h D x hx
  obtain ⟨z,hz,hz0⟩ := hne
  exact hz0 (hLe hz)

theorem upper_face_character_maximal_level (F : ℕ → Submodule R L)
    (hF : Antitone F) (hInitial : F 0 = F 1) (ℓ d : ℕ) (hTerminal : F (ℓ+1) = ⊥)
    (chi : (Finset (Fin d) → L) →ₗ[R] R)
    (hne : ∃ z ∈ upperFaceLieLayer F d 0, chi z ≠ 0) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ ℓ ∧
      (∃ D : Finset (Fin d), D.card ≤ j ∧ ∃ x ∈ F j,
        chi (upperFaceLieArray (R := R) D x) ≠ 0) ∧
      ∀ k : ℕ, j < k → ∀ A : Finset (Fin d), A.card ≤ k →
        ∀ x ∈ F k, chi (upperFaceLieArray (R := R) A x) = 0 := by
  classical
  obtain ⟨D,x,hx,hx0⟩ := upper_face_character_nonzero_generator F d chi hne
  let k := max 1 D.card
  have hk1 : 1 ≤ k := le_max_left _ _
  have hDk : D.card ≤ k := le_max_right _ _
  have hxk : x ∈ F k := by
    by_cases hD : D.card = 0
    · have he : k = 1 := by simp only [k,hD,Nat.max_zero]
      rw [he,← hInitial,← hD]
      exact hx
    · have he : k = D.card := max_eq_right (by omega)
      exact he ▸ hx
  have hkTop : k ≤ ℓ := by
    by_contra hn
    have hz := hF (show ℓ+1 ≤ k by omega) hxk
    rw [hTerminal,Submodule.mem_bot] at hz
    exact hx0 (by rw [hz,map_zero,map_zero])
  let P (i : ℕ) : Prop := ∃ A : Finset (Fin d), A.card ≤ i ∧
    ∃ v ∈ F i, chi (upperFaceLieArray (R := R) A v) ≠ 0
  let T := (Finset.Icc 1 ℓ).filter P
  have hT : T.Nonempty :=
    ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hk1,hkTop⟩,D,hDk,x,hxk,hx0⟩⟩
  let j := T.max' hT
  obtain ⟨hjRange,hjNonzero⟩ := Finset.mem_filter.mp (T.max'_mem hT)
  obtain ⟨hj,hjTop⟩ := Finset.mem_Icc.mp hjRange
  refine ⟨j,hj,hjTop,hjNonzero,?_⟩
  intro m hjm A hA v hv
  by_cases hm : m ≤ ℓ
  · by_contra hbad
    have hmT : m ∈ T := Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨by omega,hm⟩,A,hA,v,hv,hbad⟩
    have hmj : m ≤ j := T.le_max' m hmT
    omega
  · have hz := hF (show ℓ+1 ≤ m by omega) hv
    rw [hTerminal,Submodule.mem_bot] at hz
    rw [hz,map_zero,map_zero]

end Hindman168
