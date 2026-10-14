import Hindman168.NativeFiniteProductCoordinates

/-! The actual finite product coordinates form an injective group homomorphism. -/
namespace Hindman168
attribute [local instance] nativeFiniteProductGroup
variable {G : Type*} [Group G]

theorem native_finite_product_coordinate_one (n : ℕ) (k : Fin (n+1)) :
    nativeFiniteProductCoordinate n (1 : nativeFiniteProduct G n) k = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    refine Fin.lastCases ?_ ?_ k
    · simp only [nativeFiniteProductCoordinate_last]; rfl
    · intro j
      exact (nativeFiniteProductCoordinate_castSucc n 1 j).trans (ih j)

theorem native_finite_product_coordinate_mul (n : ℕ) (x y : nativeFiniteProduct G n)
    (k : Fin (n+1)) : nativeFiniteProductCoordinate n (x*y) k =
      nativeFiniteProductCoordinate n x k * nativeFiniteProductCoordinate n y k := by
  induction n with
  | zero => rfl
  | succ n ih =>
    refine Fin.lastCases ?_ ?_ k
    · simp only [nativeFiniteProductCoordinate_last]; rfl
    · intro j
      simp only [nativeFiniteProductCoordinate_castSucc]
      exact ih x.1 y.1 j

noncomputable def nativeFiniteProductCoordinateHom (n : ℕ) :
    nativeFiniteProduct G n →* (Fin (n+1) → G) where
  toFun := nativeFiniteProductCoordinate n
  map_one' := funext (native_finite_product_coordinate_one n)
  map_mul' x y := funext (native_finite_product_coordinate_mul n x y)

noncomputable def nativeCubeVertexHom (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) :
    nativeFiniteProduct G n →* (Finset (Fin d) → G) where
  toFun g V := nativeFiniteProductCoordinate n g (e.symm V)
  map_one' := funext (fun V => native_finite_product_coordinate_one n (e.symm V))
  map_mul' x y := funext (fun V => native_finite_product_coordinate_mul n x y (e.symm V))

theorem native_cube_vertex_hom_injective (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) :
    Function.Injective (nativeCubeVertexHom (G := G) d n e) := by
  intro x y hxy
  apply nativeFiniteProductCoordinate_injective n
  funext k
  have hk := congrFun hxy (e k)
  simpa only [nativeCubeVertexHom, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.symm_apply_apply] using hk

end Hindman168
