import Hindman168.NativeCoordinateSourceReindex
import Hindman168.NativeRealResidualLargeEvent

/-! Exact transport of original ceil-box means and non-strict real residual
bad events. Both full q and q*t laws are retained, with no coprimality. -/
namespace Hindman168
universe u
open FiniteMass

theorem rough_native_coordinate_box_mean {κ τ : Type*} [Fintype κ] [Fintype τ]
    {s : ℕ} (D : NativeNilmanifoldData.{u} s) (e : κ ≃ τ)
    (Q : (Option κ → ℝ) → D.G) (lo hi a : κ → ℤ) (q : ℤ) (z : ℝ)
    (F : (D.G ⧸ D.Γ) → ℂ) :
    complexExpectation (uniformFinsetMass (alignmentBoxClass (fun j => lo (e.symm j))
      (fun j => hi (e.symm j)) (fun j => a (e.symm j)) q))
      (fun y => F (QuotientGroup.mk (roughNativeCoordinateSource D e Q
        (Option.elim · z (fun j => (y j : ℝ)))))) =
    complexExpectation (uniformFinsetMass (alignmentBoxClass lo hi a q))
      (fun y => F (QuotientGroup.mk (Q (Option.elim · z (fun j => (y j : ℝ)))))) := by
  rw [rough_coordinate_box_complex_mean e lo hi a q]
  congr 1
  funext y
  congr 2
  unfold roughNativeCoordinateSource
  congr 1
  funext j
  cases j with
  | none => rfl
  | some j =>
    change (y (e.symm (e j)) : ℝ)=(y j : ℝ)
    rw [Equiv.symm_apply_apply]

theorem rough_native_real_residual_event_reindex {κ τ : Type*} [Fintype κ] [Fintype τ]
    {s : ℕ} (D : NativeNilmanifoldData.{u} s) (e : κ ≃ τ)
    (Q : (Option κ → ℝ) → D.G) (a : κ → ℤ) (q z t : ℕ)
    (Z c C : ℝ) (L : NNReal) (B η : ℝ)
    (h : RoughNativeRealResidualComplexLargeIndex D Q a q z t Z c C L B η) :
    RoughNativeRealResidualComplexLargeIndex D (roughNativeCoordinateSource D e Q)
      (fun j => a (e.symm j)) q z t Z c C L B η := by
  obtain ⟨lo,hi,b,F,hL,hB,hgeom,hcompatible,hdiscrepancy⟩ := h
  refine ⟨(fun j => lo (e.symm j)),(fun j => hi (e.symm j)),
    (fun j => b (e.symm j)),F,hL,hB,(fun j => hgeom (e.symm j)),
    (fun j => hcompatible (e.symm j)),?_⟩
  rw [rough_native_coordinate_box_mean D e Q (fun j => ⌈lo j⌉)
    (fun j => ⌈hi j⌉) b (q*t : ℕ) (z : ℝ) F,
    rough_native_coordinate_box_mean D e Q (fun j => ⌈lo j⌉)
    (fun j => ⌈hi j⌉) a q (z : ℝ) F]
  exact hdiscrepancy

end Hindman168
