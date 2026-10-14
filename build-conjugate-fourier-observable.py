from pathlib import Path

metric='''  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : MetricSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) := (nativeConjugateNilmanifoldData D ρ).metric
  letI : TopologicalSpace (D.G ⧸ roughConjugateSubgroup D.Γ ρ) :=
    (nativeConjugateNilmanifoldData D ρ).metric.toUniformSpace.toTopologicalSpace
'''
intro='''    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (k : nativeRationalTerminalIndex D L → ℤ) (ρ : D.G)'''
metric_header='\n'.join('  '+line for line in metric.splitlines())+'\n'
def theorem(name,args,statement,proof,measure=False):
    m='''  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
''' if measure else ''
    m_header='\n'.join('  '+line for line in m.splitlines())+'\n' if m else ''
    return '\ntheorem '+name+' {s ℓ : ℕ}\n'+intro+args+' :\n'+m_header+metric_header+statement+' := by\n'+m+metric+proof+'\n'
text='''import Hindman168.NativeConjugateRightObservable
import Hindman168.NativeRationalTerminalFourierCompactFamilies

/-! Actual original Fourier signal, frozen LEFT group parameter and TRUE
right-coset map give genuine compact families of continuous observables
on conjugated native data. Haar mean is zero for nonzero original mode.
Freezing error / short-progression selection is NOT assumed. -/
namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

noncomputable def nativeConjugateFourierObservable {s ℓ : ℕ}
'''+intro+''' (ε : D.G) :
'''+metric_header+'''    C(D.G ⧸ D.Γ,ℂ) → C(D.G ⧸ roughConjugateSubgroup D.Γ ρ,ℂ) := by
'''+metric+'''  intro F
  exact nativeConjugateRightObservable D ρ
    (nativeBasepointObservable D ε (nativeRationalTerminalFourierProjection D L k F))
'''
text+=theorem('native_conjugate_fourier_observable_apply',' (ε : D.G)',
'''    ∀ (F : C(D.G ⧸ D.Γ,ℂ)) (q : D.G ⧸ roughConjugateSubgroup D.Γ ρ),
      nativeConjugateFourierObservable D L k ρ ε F q=
        nativeRationalTerminalFourierProjection D L k F (ε • roughConjugateRightCosetMap D.Γ ρ q)''',
'''  intro F q
  rfl''')
text+=theorem('native_conjugate_fourier_observable_continuous','',
'''    Continuous (fun p : D.G × C(D.G ⧸ D.Γ,ℂ) => nativeConjugateFourierObservable D L k ρ p.1 p.2)''',
'''  letI := native_nilmanifold_metric_quotient_compact D
  have hFourier : Continuous (nativeRationalTerminalFourierProjection D L k) :=
    (native_rational_terminal_fourier_projection_functionspace_lipschitz D L k).continuous
  exact (native_conjugate_right_observable_continuous D ρ).comp
    ((native_basepoint_observable_continuous D).comp (continuous_fst.prodMk (hFourier.comp continuous_snd)))''')
text+=theorem('native_conjugate_fourier_observable_family_compact',
''' (K : Set D.G) (hK : IsCompact K)''',
'''    IsCompact ((fun p : D.G × C(D.G ⧸ D.Γ,ℂ) => nativeConjugateFourierObservable D L k ρ p.1 p.2) ''
      (K ×ˢ unitLipschitzObservables (D.G ⧸ D.Γ)))''',
'''  exact (hK.prod (unit_lipschitz_observables_compact (D.G ⧸ D.Γ))).image
    (native_conjugate_fourier_observable_continuous D L k ρ)''')
text+=theorem('native_conjugate_fourier_observable_unit_bound',' (ε : D.G)',
'''    ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ), ∀ q : D.G ⧸ roughConjugateSubgroup D.Γ ρ,
      ‖nativeConjugateFourierObservable D L k ρ ε F q‖ ≤ 1''',
'''  intro F hF q
  rw [native_conjugate_fourier_observable_apply,native_rational_terminal_fourier_projection_apply]
  exact torus_vertical_fourier_coefficient_bound (nativeRationalTerminalAction D L) k F
    (ε • roughConjugateRightCosetMap D.Γ ρ q) 1 hF.2''')
text+=theorem('native_conjugate_fourier_observable_zero_mean',' (ε : D.G) (hk : k ≠ 0)',
'''    ∀ F : C(D.G ⧸ D.Γ,ℂ),
      (∫ q, nativeConjugateFourierObservable D L k ρ ε F q
        ∂nativeNilmanifoldQuotientProbability (nativeConjugateNilmanifoldData D ρ))=0''',
'''  intro F
  exact (native_conjugate_right_observable_integral D ρ _).trans
    ((native_basepoint_observable_canonical_integral D ε _).trans
      (native_rational_terminal_fourier_projection_nonzero_mean D L k hk F))''',True)
text+=theorem('native_conjugate_fourier_observable_sample',' (ε h : D.G)',
'''    ∀ F : C(D.G ⧸ D.Γ,ℂ),
      nativeConjugateFourierObservable D L k ρ ε F (h : D.G ⧸ roughConjugateSubgroup D.Γ ρ)=
        nativeRationalTerminalFourierProjection D L k F (ε*h*ρ : D.G ⧸ D.Γ)''',
'''  intro F
  rw [native_conjugate_fourier_observable_apply,rough_conjugate_right_coset_map_mk]
  change nativeRationalTerminalFourierProjection D L k F (ε*(h*ρ) : D.G ⧸ D.Γ)=_
  rw [mul_assoc]''')
text+='\nend Hindman168\n'
Path('Hindman168/NativeConjugateFourierObservable.lean').write_text(text,encoding='utf-8')
