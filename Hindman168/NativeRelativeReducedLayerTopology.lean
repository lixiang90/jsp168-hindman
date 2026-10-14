import Hindman168.NativeRelativeReducedLieFiltration
import Hindman168.NativeLieGlobalTopology

/-! Every actual reduced filtration layer is the exponential image of
its finite dimensional projected Lie subspace, hence closed and connected. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRelativeReducedLayerHomeomorph {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ) :
    nativeRelativeReducedLieFiltration D d hd i ≃ₜ nativeRelativeReducedNativeFiltration D d hd i where
  toFun v := ⟨nativeLieExponential (E := (nativeRelativeReducedData D d hd).E)
    (I := (nativeRelativeReducedData D d hd).I) (G := (nativeRelativeReducedData D d hd).G) v.val,
    native_relative_reduced_lie_filtration_exponential_mem D d hd i v.property⟩
  invFun g := ⟨nativeLieGlobalLogarithm (E := (nativeRelativeReducedData D d hd).E)
    (I := (nativeRelativeReducedData D d hd).I) (G := (nativeRelativeReducedData D d hd).G) g.val,
    (native_relative_reduced_layer_logarithm_iff D d hd i g.val).mp g.property⟩
  left_inv v := Subtype.ext (nativeLieGlobalLogarithm_exponential
    (I := (nativeRelativeReducedData D d hd).I) (G := (nativeRelativeReducedData D d hd).G) v.val)
  right_inv g := Subtype.ext (nativeLieExponential_globalLogarithm
    (I := (nativeRelativeReducedData D d hd).I) (G := (nativeRelativeReducedData D d hd).G) g.val)
  continuous_toFun := ((nativeLieExponential_continuous
    (I := (nativeRelativeReducedData D d hd).I) (G := (nativeRelativeReducedData D d hd).G)).comp
      continuous_subtype_val).subtype_mk _
  continuous_invFun := ((nativeLieGlobalLogarithm (E := (nativeRelativeReducedData D d hd).E)
    (I := (nativeRelativeReducedData D d hd).I) (G := (nativeRelativeReducedData D d hd).G)).continuous.comp
      continuous_subtype_val).subtype_mk _

theorem native_relative_reduced_layer_closed {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ) :
    IsClosed (nativeRelativeReducedNativeFiltration D d hd i : Set (nativeRelativeReducedData D d hd).G) := by
  have he : (nativeRelativeReducedNativeFiltration D d hd i : Set (nativeRelativeReducedData D d hd).G) =
      (nativeLieGlobalLogarithm (E := (nativeRelativeReducedData D d hd).E)
        (I := (nativeRelativeReducedData D d hd).I) (G := (nativeRelativeReducedData D d hd).G)) ⁻¹'
          (nativeRelativeReducedLieFiltration D d hd i : Set (nativeRelativeReducedData D d hd).E) :=
    Set.ext (native_relative_reduced_layer_logarithm_iff D d hd i)
  rw [he]
  exact (nativeRelativeReducedLieFiltration D d hd i).closed_of_finiteDimensional.preimage
    (nativeLieGlobalLogarithm (E := (nativeRelativeReducedData D d hd).E)
      (I := (nativeRelativeReducedData D d hd).I) (G := (nativeRelativeReducedData D d hd).G)).continuous

theorem native_relative_reduced_layer_contractible {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ) :
    ContractibleSpace (nativeRelativeReducedNativeFiltration D d hd i) := by
  let V := nativeRelativeReducedLieFiltration D d hd i
  letI : ContractibleSpace V := V.convex.contractibleSpace ⟨0,V.zero_mem⟩
  exact (nativeRelativeReducedLayerHomeomorph D d hd i).symm.contractibleSpace

theorem native_relative_reduced_layer_connected {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ) :
    ConnectedSpace (nativeRelativeReducedNativeFiltration D d hd i) := by
  letI := native_relative_reduced_layer_contractible D d hd i
  infer_instance

theorem native_relative_reduced_layer_simplyConnected {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ) :
    SimplyConnectedSpace (nativeRelativeReducedNativeFiltration D d hd i) := by
  letI := native_relative_reduced_layer_contractible D d hd i
  infer_instance

end Hindman168
