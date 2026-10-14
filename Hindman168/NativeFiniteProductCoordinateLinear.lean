import Hindman168.NativeFiniteProductCoordinates

/-! The actual iterated-product coordinates as linear maps. -/
namespace Hindman168
attribute [local instance] nativeFiniteProductNormedAddCommGroup nativeFiniteProductNormedSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def nativeFiniteProductCoordinateLinear : (n : ℕ) →
    Fin (n+1) → nativeFiniteProduct E n →ₗ[ℝ] E
  | 0, _ => LinearMap.id
  | n+1, i => Fin.lastCases (LinearMap.snd ℝ (nativeFiniteProduct E n) E)
      (fun j => (nativeFiniteProductCoordinateLinear n j).comp
        (LinearMap.fst ℝ (nativeFiniteProduct E n) E)) i

theorem native_finite_product_coordinate_linear_apply (n : ℕ) (i : Fin (n+1))
    (v : nativeFiniteProduct E n) :
    nativeFiniteProductCoordinateLinear n i v = nativeFiniteProductCoordinate n v i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    refine Fin.lastCases ?_ ?_ i
    · simp only [nativeFiniteProductCoordinateLinear, Fin.lastCases_last,
        nativeFiniteProductCoordinate_last]
      rfl
    · intro j
      simp only [nativeFiniteProductCoordinateLinear, Fin.lastCases_castSucc,
        nativeFiniteProductCoordinate_castSucc]
      exact ih j v.1

end Hindman168
