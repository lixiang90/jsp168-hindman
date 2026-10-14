from pathlib import Path

src=Path('Hindman168/NativeRationalConstructedChildSignal.lean').read_text(encoding='utf-8')
start=src.index('    ∃ (j : ℕ)'); end=src.index(' := by',start)
data=src[start:end]
data=data.replace('0 < K ∧ 0 < θ ∧','''0 < K ∧ q ≤ B ∧ K ≤ B ∧ ‖y‖ ≤ (B : ℝ) ∧ 4*K*(S*q) ≤ B ∧''')
data=data.replace('4*K*(S*q) ≤ N','B ≤ N')
data=data.replace('(N : ℝ)/(4*(K : ℝ)*((S*q : ℕ) : ℝ)) ≤ T','(N : ℝ)/(B : ℝ) ≤ T')
head='''import Hindman168.NativeRationalConstructedChildSignal
import Hindman168.FiniteConditionedSignalBudgets

/-! Named ACTUAL child-budget proposition is PROVED for every valid
character. It retains genuine geometry/source relations and UNIT signal.
This is not a datum field, inverse premise or formalization target. -/
namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

def NativeRationalNonlinearityCharacterGood {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) : Prop :=
  RoughNativeHorizontalFunctional (I := (nativeRationalRelativeData D L 1).I)
    (nativeRationalRelativeData D L 1).Γ χ.toLinearMap ∧
    (∀ g h : D.G, nativeRationalRelativeCommutatorValue D L χ g h=0) ∧
      nativeRationalRelativeDifferenceCharacter D L χ ≠ 0

def NativeRationalCharacterChildBudget {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (k : nativeRationalTerminalIndex D L → ℤ) (A δ : ℝ) (S : ℕ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) (B : ℕ) (θ : ℝ) : Prop :=
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ hHor : RoughNativeHorizontalFunctional (I := (nativeRationalRelativeData D L 1).I)
      (nativeRationalRelativeData D L 1).Γ χ.toLinearMap,
    ∃ hzero : ∀ g h : D.G, nativeRationalRelativeCommutatorValue D L χ g h=0,
    nativeRationalRelativeDifferenceCharacter D L χ ≠ 0 ∧
    let K0 := nativeRationalNonlinearKernelFiltration D L χ hHor hzero
'''
data=data.replace('    ∃ (j : ℕ) (y : D.E) (q K : ℕ) (θ : ℝ),','    ∃ (j : ℕ) (y : D.E) (q K : ℕ),')
exist='''
theorem native_rational_character_child_budget_exists {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (hdeg : 2 ≤ ℓ)
    (k : nativeRationalTerminalIndex D L → ℤ) (hk : k ≠ 0) (A δ : ℝ) (S : ℕ)
    (hA : 0 ≤ A) (hδ : 0 < δ) (hS : 0 < S)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) (hGood : NativeRationalNonlinearityCharacterGood D L χ) :
    ∃ B : ℕ, 0 < B ∧ ∃ θ : ℝ, 0 < θ ∧ NativeRationalCharacterChildBudget D L k A δ S χ B θ := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨hHor,hzero,hDiff⟩ := hGood
  obtain ⟨j,y,q,K,θ,hj2,hjL,hy,hyRat,hFy,hHigher,hq,hpow,hK,hθ,hSelect⟩ :=
    native_rational_constructed_nonlinearity_child_signal D L hdeg χ hHor hzero hDiff k hk A δ S hA hδ hS
  let B := 4*K*(S*q)+⌈‖y‖⌉₊+q+K+1
  have hB : 0 < B := by dsimp only [B]; omega
  have h4B : 4*K*(S*q) ≤ B := by dsimp only [B]; omega
  have hqB : q ≤ B := by dsimp only [B]; omega
  have hKB : K ≤ B := by dsimp only [B]; omega
  have hyB : ‖y‖ ≤ (B : ℝ) := (Nat.le_ceil _).trans (by
    exact_mod_cast (show ⌈‖y‖⌉₊ ≤ B by dsimp only [B]; omega))
  refine ⟨B,hB,θ,hθ,hHor,hzero,hDiff,j,y,q,K,hj2,hjL,hy,hyRat,hFy,hHigher,hq,hpow,hK,hqB,hKB,hyB,h4B,?_⟩
  intro M hM hMS p hp N hBN hBounds F hF hSignal
  obtain ⟨a,T,m,ha0,haN,hT,hm,hLength,hRest⟩ :=
    hSelect M hM hMS p hp N (h4B.trans hBN) hBounds F hF hSignal
  have hLengthB : (N : ℝ)/(B : ℝ) ≤ T :=
    (div_le_div_of_nonneg_left (Nat.cast_nonneg N) (by positivity)
      (by exact_mod_cast h4B)).trans hLength
  exact ⟨a,T,m,ha0,haN,hT,hm,hLengthB,hRest⟩

theorem native_rational_character_child_budget_mono {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (k : nativeRationalTerminalIndex D L → ℤ) (A δ : ℝ) (S : ℕ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) (B B' : ℕ) (θ θ' : ℝ)
    (hB : 0 < B) (hBB : B ≤ B') (hθ : θ' ≤ θ)
    (hData : NativeRationalCharacterChildBudget D L k A δ S χ B θ) :
    NativeRationalCharacterChildBudget D L k A δ S χ B' θ' := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨hHor,hzero,hDiff,j,y,q,K,hj2,hjL,hy,hyRat,hFy,hHigher,hq,hpow,hK,hqB,hKB,hyB,h4B,hSelect⟩ := hData
  refine ⟨hHor,hzero,hDiff,j,y,q,K,hj2,hjL,hy,hyRat,hFy,hHigher,hq,hpow,hK,
    hqB.trans hBB,hKB.trans hBB,hyB.trans (by exact_mod_cast hBB),h4B.trans hBB,?_⟩
  intro M hM hMS p hp N hBN hBounds F hF hSignal
  obtain ⟨a,T,m,ha0,haN,hT,hm,hLength,Km,hLayers,hDrop,pNew,hW,hD,hFactors,J,hJ,hUnit⟩ :=
    hSelect M hM hMS p hp N (hBB.trans hBN) hBounds F hF hSignal
  have hLengthB' : (N : ℝ)/(B' : ℝ) ≤ T :=
    (div_le_div_of_nonneg_left (Nat.cast_nonneg N) (by exact_mod_cast hB)
      (by exact_mod_cast hBB)).trans hLength
  exact ⟨a,T,m,ha0,haN,hT,hm,hLengthB',Km,hLayers,hDrop,pNew,hW,hD,hFactors,J,hJ,hθ.trans_lt hUnit⟩

end Hindman168
'''
Path('Hindman168/NativeRationalCharacterChildBudget.lean').write_text(head+data+'\n'+exist,encoding='utf-8')
