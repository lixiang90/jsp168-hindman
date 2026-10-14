from pathlib import Path

p = Path('Hindman168/FiniteComplexRealComponents.lean')
s = p.read_text(encoding='utf-8')
s = s.replace(', Complex.sum_re', '').replace(', Complex.sum_im', '')
s = s.replace('    push_neg at hr\n    linarith', '    have hrlt := lt_of_not_ge hr\n    linarith')
start = s.index('\nnamespace Hindman168\n')
Path('Hindman168/ComplexRealObservable.lean').write_text(
    'import Hindman168.FiniteComplexRealComponents\n'+s[start:], encoding='utf-8')
p.write_text(s[:start]+'\n', encoding='utf-8')
