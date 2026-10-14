import Hindman168.NativeRelativeExponentialLogarithm
import Hindman168.NativeRelativeSquareRational

/-! The true relative inclusion preserves AND reflects rational directions
against the actual restricted original product lattice. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_relative_rational_inclusion_iff {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (v : (nativeRelativeSquareData D d hd 1).E) :
    letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
    v ∈ nativeSubgroupRationalLogSpan (E := (nativeRelativeSquareData D d hd 1).E)
      (I := (nativeRelativeSquareData D d hd 1).I) (nativeRelativeSquareData D d hd 1).Γ ↔
    nativeRelativeModelInclusion D d hd 1 v ∈ nativeSubgroupRationalLogSpan
      (E := D.E × D.E) (I := D.I.prod D.I) (D.Γ.prod D.Γ) := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  rw [nativeSubgroupRationalLogSpan_mem_iff_positive_power,
    nativeSubgroupRationalLogSpan_mem_iff_positive_power]
  have he := native_relative_data_exponential D d hd 1 v
  have hPow : ∀ n : ℕ,
      nativeLieExponential (E := (nativeRelativeSquareData D d hd 1).E)
        (I := (nativeRelativeSquareData D d hd 1).I) (G := (nativeRelativeSquareData D d hd 1).G) v ^ n ∈
          (nativeRelativeSquareData D d hd 1).Γ ↔
      nativeLieExponential (E := D.E × D.E) (I := D.I.prod D.I) (G := D.G × D.G)
        (nativeRelativeModelInclusion D d hd 1 v) ^ n ∈ D.Γ.prod D.Γ := by
    intro n
    change nativeRelativeGroupInclusion D d hd 1
      (nativeLieExponential (E := (nativeRelativeSquareData D d hd 1).E)
        (I := (nativeRelativeSquareData D d hd 1).I) (G := (nativeRelativeSquareData D d hd 1).G) v ^ n) ∈
        D.Γ.prod D.Γ ↔ _
    rw [map_pow,he]
  exact exists_congr (fun n => and_congr_right (fun _ => hPow n))

end Hindman168
