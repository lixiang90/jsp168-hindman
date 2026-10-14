import Hindman168.NativeNilmanifoldConstruction
import Hindman168.ProductPieceNilMultiplication

/-! Full native recipes and binary closure with their actual manifold
models, compatible metrics, specified lattices and common step bound. -/

namespace Hindman168
open NNReal
universe u

def nativePieceOn {s N : ℕ} (D : NativeNilmanifoldData.{u} s)
    (F : MasterParameterFamily) (gap : ℕ → Fin N) (f : ℕ → ℤ → ℝ) : Prop :=
  letI := D.metric
  IsBoundedPieceNilsequence D.Γ F gap f

def NativePieceRepresented (s : ℕ) {N : ℕ} (F : MasterParameterFamily)
    (gap : ℕ → Fin N) (f : ℕ → ℤ → ℝ) : Prop :=
  ∃ D : NativeNilmanifoldData.{u} s, nativePieceOn D F gap f

theorem nativePieceOn_const {s N : ℕ} (D : NativeNilmanifoldData.{u} s)
    (F : MasterParameterFamily) (gap : ℕ → Fin N) (c : ℝ) :
    nativePieceOn D F gap (fun _ _ => c) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  refine ⟨fun _ _ => ContinuousMap.const _ c, fun _ _ => 1, fun _ _ => 1,
    |c|, 0, abs_nonneg c, ?_, ?_, ?_⟩
  · exact fun _ _ _ => le_rfl
  · exact fun _ _ => LipschitzWith.const c
  · rfl

theorem nativePieceOn_add {s N : ℕ} (A B : NativeNilmanifoldData.{u} s)
    (F : MasterParameterFamily) (gap : ℕ → Fin N) (f g : ℕ → ℤ → ℝ)
    (hf : nativePieceOn A F gap f) (hg : nativePieceOn B F gap g) :
    nativePieceOn (nativeNilmanifoldProduct A B) F gap (fun w y => f w y + g w y) := by
  letI := A.metric
  letI := B.metric
  exact boundedPieceNilsequence_add_product A.Γ B.Γ F gap f g hf hg

theorem nativePieceOn_mul {s N : ℕ} (A B : NativeNilmanifoldData.{u} s)
    (F : MasterParameterFamily) (gap : ℕ → Fin N) (f g : ℕ → ℤ → ℝ)
    (hf : nativePieceOn A F gap f) (hg : nativePieceOn B F gap g) :
    nativePieceOn (nativeNilmanifoldProduct A B) F gap (fun w y => f w y * g w y) := by
  letI := A.metric
  letI := B.metric
  exact boundedPieceNilsequence_mul_product A.Γ B.Γ F gap f g hf hg

theorem nativePieceOn_smul {s N : ℕ} (D : NativeNilmanifoldData.{u} s)
    (F : MasterParameterFamily) (gap : ℕ → Fin N) (f : ℕ → ℤ → ℝ)
    (hf : nativePieceOn D F gap f) (r : ℝ) : nativePieceOn D F gap (fun w y => r * f w y) := by
  letI := D.metric
  exact boundedPieceNilsequence_smul D.Γ F gap f hf r

theorem nativePieceOn_clip {s N : ℕ} (D : NativeNilmanifoldData.{u} s)
    (F : MasterParameterFamily) (gap : ℕ → Fin N) (f : ℕ → ℤ → ℝ)
    (hf : nativePieceOn D F gap f) : nativePieceOn D F gap (fun w y => unitIntervalClip (f w y)) := by
  letI := D.metric
  exact boundedPieceNilsequence_clip D.Γ F gap f hf

theorem nativePieceOn_refine {s N : ℕ} (D : NativeNilmanifoldData.{u} s)
    (F : MasterParameterFamily) (fine coarse : ℕ → Fin N)
    (hdiv : ∀ w, F.gap w (fine w).val ∣ F.gap w (coarse w).val)
    (f : ℕ → ℤ → ℝ) (hf : nativePieceOn D F coarse f) : nativePieceOn D F fine f := by
  letI := D.metric
  exact boundedPieceNilsequence_refine D.Γ F fine coarse hdiv f hf

end Hindman168
