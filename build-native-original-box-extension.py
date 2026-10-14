from pathlib import Path
import re

for old,new in [
    ('NativeAbelianBoundedCubeObstruction','NativeOriginalBoundedCubeObstruction'),
    ('NativeAbelianAffineCubeInput','NativeOriginalAffineCubeInput'),
    ('NativeAbelianRealBoxObstruction','NativeOriginalRealBoxObstruction'),
]:
    source=Path('Hindman168/'+old+'.lean').read_text(encoding='utf-8')
    source=source.replace('import Hindman168.NativeAbelianBinomialObstruction',
                          'import Hindman168.NativeOriginalPolynomialInverse')
    source=source.replace('NativeAbelianBoundedCubeObstruction','NativeOriginalBoundedCubeObstruction')
    source=source.replace('NativeAbelianAffineCubeInput','NativeOriginalAffineCubeInput')
    source=source.replace('native_abelian_bounded_cube_obstruction','native_original_bounded_cube_obstruction')
    source=source.replace('native_abelian_affine_cube_binomial_input','native_original_affine_cube_binomial_input')
    source=source.replace('native_abelian_real_box_finite_obstruction','native_original_real_box_finite_obstruction')
    source=source.replace('native_abelian_binomial_observable_obstruction D n d',
                          'native_original_polynomial_observable_inverse (σ := Fin n) D d')
    source=source.replace('(D : NativeNilmanifoldData.{u} 1)', '{s : ℕ} (D : NativeNilmanifoldData.{u} s)')
    source=source.replace('nativeAbelianTorusHaar D','nativeNilmanifoldQuotientProbability D')
    source=re.sub(r'^ +letI : MeasurableSpace \(D.G ⧸ D.Γ\) := borel \(D.G ⧸ D.Γ\)\n',
                  '',source,flags=re.M)
    source=re.sub(r'^( +)letI := D.metric$',
                  lambda m: m[1]+'letI : MeasurableSpace D.E := borel D.E\n'
                          +m[1]+'letI : MeasurableSpace D.G := borel D.G\n'
                          +m[0],source,flags=re.M)
    source=source.replace('ORIGINAL abelian','ORIGINAL arbitrary-step native')
    Path('Hindman168/'+new+'.lean').write_text(source,encoding='utf-8')
