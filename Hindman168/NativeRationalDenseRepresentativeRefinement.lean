import Hindman168.NativeRationalRepresentativeCoordinates
import Hindman168.FiniteDenseWitnessSelection

/-! Genuine finite integer-offset refinement of SAME actual useful shifts.
The fixed list precedes every original coefficient, group element and sample.
The retained density loss is explicit and the selected representatives remain
the actual compact representatives already used by the relative polynomial. -/
namespace Hindman168
open scoped Manifold ContDiff Classical
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_dense_representative_refinement {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    ∃ K : ℕ, ∃ C : Finset (NativeRationalFirstLayerIndex D L → ℤ), C.Nonempty ∧
      (∀ b ∈ C, ∀ i, |(b i : ℝ)| ≤ (K : ℝ)) ∧
      ∀ (a : D.G) (U : Finset ℕ), U.Nonempty →
        ∃ b ∈ C, ∃ V : Finset ℕ, V ⊆ U ∧ V.Nonempty ∧
          (U.card : ℝ) ≤ (C.card : ℝ)*(V.card : ℝ) ∧
          ∀ h ∈ V, ∀ i,
            nativeRationalFirstLayerCoordinates D L (nativeRationalRepresentative D (a^(h : ℤ))) i =
              Int.fract ((h : ℝ)*nativeRationalFirstLayerCoordinates D L a i)+(b i : ℝ) := by
  obtain ⟨K,C,hC,hbound,hoff⟩ := native_rational_representative_offsets_finite D L
  refine ⟨K,C,hC,hbound,?_⟩
  intro a U hU
  obtain ⟨b,hb,V,hVU,hV,hcard,he⟩ := finite_dense_witness_selection U hU C
    (fun h b => nativeRationalRepresentativeCoordinateOffset D L (a^(h : ℤ))=b)
    (fun h _ => ⟨_,hoff _,rfl⟩)
  refine ⟨b,hb,V,hVU,hV,hcard,?_⟩
  intro h hh i
  rw [native_rational_representative_fractional_coordinates,he h hh,
    native_rational_first_layer_coordinates_zpow]
  simp only [Int.cast_natCast]

end Hindman168
