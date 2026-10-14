import Hindman168.NativeCompactCosetRepresentatives

/-! Actual choices from ONE fixed compact original coset representative set,
with the actual original nonnormal lattice factors, for every native datum. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRationalRepresentativeSet {s : ℕ} (D : NativeNilmanifoldData.{u} s) : Set D.G :=
  Classical.choose (native_exists_compact_coset_representatives D)

theorem native_rational_representative_set_compact {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    IsCompact (nativeRationalRepresentativeSet D) :=
  (Classical.choose_spec (native_exists_compact_coset_representatives D)).1

theorem native_rational_representative_exists {s : ℕ} (D : NativeNilmanifoldData.{u} s) (g : D.G) :
    ∃ r ∈ nativeRationalRepresentativeSet D, ∃ γ : D.Γ, g = r * γ :=
  (Classical.choose_spec (native_exists_compact_coset_representatives D)).2 g

noncomputable def nativeRationalRepresentative {s : ℕ} (D : NativeNilmanifoldData.{u} s) (g : D.G) : D.G :=
  Classical.choose (native_rational_representative_exists D g)

theorem native_rational_representative_mem {s : ℕ} (D : NativeNilmanifoldData.{u} s) (g : D.G) :
    nativeRationalRepresentative D g ∈ nativeRationalRepresentativeSet D :=
  (Classical.choose_spec (native_rational_representative_exists D g)).1

noncomputable def nativeRationalRepresentativeLatticePart {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (g : D.G) : D.Γ :=
  Classical.choose (Classical.choose_spec (native_rational_representative_exists D g)).2

theorem native_rational_representative_factorization {s : ℕ} (D : NativeNilmanifoldData.{u} s) (g : D.G) :
    g = nativeRationalRepresentative D g * nativeRationalRepresentativeLatticePart D g :=
  Classical.choose_spec (Classical.choose_spec (native_rational_representative_exists D g)).2

theorem native_rational_representative_log_bound {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ a ∈ nativeRationalRepresentativeSet D,
      ‖nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) a‖ ≤ B := by
  obtain ⟨b,hb⟩ := (native_rational_representative_set_compact D).bddAbove_image
    ((nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)).continuous.norm.continuousOn)
  exact ⟨max b 0,le_max_right _ _,fun _ ha => (hb (Set.mem_image_of_mem _ ha)).trans (le_max_left _ _)⟩

end Hindman168
