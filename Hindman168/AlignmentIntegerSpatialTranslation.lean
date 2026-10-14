import Hindman168.AlignmentNativeIntegerSpatialArray

/-! A genuine integer coordinate shift changes exactly the corresponding
weighted base exponent. Its own-pair Delta is the original slot translation,
including weights zero (lower face) and one (upper face). -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators Classical
universe u

theorem alignment_integer_spatial_vertex_single {κ : Type*} [Fintype κ]
    (spatial : Option κ → ℤ) (weight : κ → ℤ) (j : κ) (delta : ℤ) :
    alignmentIntegerSpatialVertex (fun k => spatial k+if k=some j then delta else 0) weight=
      alignmentIntegerSpatialVertex spatial weight+weight j*delta := by
  have hn : ¬ (none : Option κ)=some j := by intro h; cases h
  simp only [alignmentIntegerSpatialVertex,hn,if_false,add_zero,
    Option.some.injEq,mul_add,Finset.sum_add_distrib]
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  ring

theorem alignment_integer_spatial_base_single {κ : Type*} [Fintype κ] {N : ℕ}
    (F : MasterParameterFamily) (q₀ w : ℕ) (i : Fin N) (T : Finset (Fin N)) (y : Fin N → ℕ)
    (shift : AlignmentAddingPair N i → ℤ) (weight : κ → ℤ) (spatial : Option κ → ℤ)
    (j : κ) (delta : ℤ) :
    alignmentIntegerSpatialBase F q₀ w i T y shift weight
      (fun k => spatial k+if k=some j then delta else 0)=
      alignmentIntegerSpatialBase F q₀ w i T y shift weight spatial+weight j*delta := by
  unfold alignmentIntegerSpatialBase
  rw [alignment_integer_spatial_vertex_single]
  ring

variable {κ : Type*} [Fintype κ] {N : ℕ} {i : Fin N} {s : ℕ}
  (D : NativeNilmanifoldData.{u} s) (n : ℕ)
  (v : Fin (n+1) → AlignmentAddingPair N i → ℤ)
  (hv : Function.Injective (alignmentNativeFiniteEvaluation (E := D.E) (I := D.I) (G := D.G) n v))

noncomputable def alignmentNativeDataSlotTranslation
    (slots : AlignmentAddingPair N i → ℤ) :
    (alignmentNativeArrayData D n v hv).G ≃* (alignmentNativeArrayData D n v hv).G :=
  alignmentNativeArrayTranslation (E := D.E) (I := D.I) (G := D.G) n v hv slots

theorem alignment_integer_spatial_array_own_pair_translation
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (y : Fin N → ℕ)
    (shift : AlignmentAddingPair N i → ℤ) (weight : κ → ℤ) (g a : D.G)
    (spatial : Option κ → ℤ) (j : κ) (e : AlignmentAddingPair N i) (he : e.targetTail=T) :
    alignmentNativeDataSlotTranslation D n v hv (Pi.single e (weight j))
      (alignmentNativeIntegerSpatialArray D n v hv F q₀ w T y shift weight g a spatial)=
      alignmentNativeIntegerSpatialArray D n v hv F q₀ w T y shift weight g a
        (fun k => spatial k+if k=some j then alignmentPairProgression q₀ w (F.modulus w) e y else 0) := by
  letI := alignmentAddingPairFintype N i
  let delta : AlignmentAddingPair N i → ℤ :=
    fun e => if e.targetTail=T then alignmentPairProgression q₀ w (F.modulus w) e y else 0
  have ht := alignmentNativeModelArray_input_translation (E := D.E) (I := D.I) (G := D.G)
    n v hv g a (alignmentIntegerSpatialBase F q₀ w i T y shift weight spatial)
    delta (Pi.single e (weight j))
  have hsum : (∑ k, (Pi.single e (weight j) : AlignmentAddingPair N i → ℤ) k*delta k)=
      weight j*alignmentPairProgression q₀ w (F.modulus w) e y := by
    simp only [Pi.single_apply,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    simp only [delta,he,if_true]
  rw [hsum] at ht
  have hb := alignment_integer_spatial_base_single F q₀ w i T y shift weight spatial j
    (alignmentPairProgression q₀ w (F.modulus w) e y)
  have hh := ht.trans (congrArg
    (fun k => alignmentNativeModelArray (E := D.E) (I := D.I) (G := D.G) n v hv g a k delta) hb.symm)
  exact congrArg (alignmentNativeArrayDataValue D n v hv) hh

end Hindman168
