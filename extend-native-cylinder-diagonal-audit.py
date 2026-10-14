from pathlib import Path
import importlib.util, re

prefix='round-native-cylinder-diagonal'
spec=importlib.util.spec_from_file_location('audit',prefix+'-audit.py')
audit=importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)
module='Hindman168/AlignmentJointNativeCylinderPresentation.lean'
assert module not in audit.MODULES
audit.MODULES.append(module)
component=('EVERY native cylinder-product list now has an EXACT Fin-indexed presentation by ORIGINAL duplicated component/slot observers, '
    'with genuine positive supremum and Lipschitz bounds before any source/sample. Repeated components and empty lists are retained. '
    'This proves the test-function identity; original empirical source and own-face sample-map identities remain to be assembled.')
audit.COMPONENTS.append(component)
audit.REMAINING=audit.REMAINING.replace(
    'instantiate finite native cylinder products by duplicated ORIGINAL component/slot observations with exact original own-face sample maps and common numerical budgets',
    'connect the proved duplicated ORIGINAL component/slot presentations and numerical budgets to exact original empirical source and own-face sample maps')
source=Path(prefix+'-audit.py').read_text(encoding='utf-8')
for key,value in [('MODULES',audit.MODULES),('COMPONENTS',audit.COMPONENTS),('REMAINING',audit.REMAINING)]:
    source=re.sub(r'^'+key+r'=.*$',lambda _:key+'='+repr(value),source,flags=re.M)
Path(prefix+'-audit.py').write_text(source,encoding='utf-8')
log=prefix+'-AlignmentJointNativeCylinderPresentation-focused.txt'
result=audit.run(['lake','env','lean','-DautoImplicit=false',module],log)
assert not Path(log).read_bytes().strip()
results=audit.obj(prefix+'-focused-results.json')
results.append(dict(result,module=module,source_sha256=audit.digest(module)))
audit.write(prefix+'-focused-results.json',results)
root=Path('Hindman168.lean')
root.write_text(root.read_text(encoding='utf-8')+'\nimport Hindman168.AlignmentJointNativeCylinderPresentation\n',encoding='utf-8')
registry=Path('Verification.lean')
registry.write_text(registry.read_text(encoding='utf-8')+'\n#print axioms Hindman168.alignment_native_cylinder_list_original_presentation\n',encoding='utf-8')
audit.write(prefix+'-registration.json',dict(modules=audit.MODULES,names=audit.names(),declarations=audit.decls()))
review=Path(prefix+'-mathematical-review.txt')
text=review.read_text(encoding='utf-8').replace('These nine modules','These ten modules')
text=text.replace('Remaining proof work:\n', '''8. Original finite presentation. For each entry of a cylinder list choose its
actual generator witness: original component, integer slot and original
continuous Lipschitz observer. The Fin list index preserves repeated components
and slots. B=observer sup norm+1 is positive, and the actual Lipschitz witness
gives membership in the original numerical class. The list product identity is
proved pointwise on the entire actual native quotient by Fin.prod_univ_getElem,
not only on selected samples. Empty lists have no fabricated original component
and retain their constant-one product. All choices precede source/sample data.
Exact original empirical source/own-face sample-map instantiation remains work.

Execution note. An initial concurrent registry check read the previous root
cache; the final registry check runs after the final completed build. A later
registry check identified two omitted FiniteMass namespace qualifications.
Those registry names were corrected without changing proof sources. Its full
diagnostic is retained in round-native-cylinder-diagonal-axioms-namespace-diagnostic.txt.
Only final successful checks are used for the recorded verification result.

Remaining proof work:
''')
text=text.split('Remaining proof work:\n')[0]+'Remaining proof work:\n'+audit.REMAINING+'\n'
review.write_text(text,encoding='utf-8')
print('Extended audit to',len(audit.MODULES),'modules')
