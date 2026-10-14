from pathlib import Path
import importlib.util,re

prefix='round-native-complete-cube-probability'
spec=importlib.util.spec_from_file_location('audit',prefix+'-audit.py')
audit=importlib.util.module_from_spec(spec);spec.loader.exec_module(audit)
module='Hindman168/AlignmentAllTargetsNativeCountableSelection.lean'
assert module not in audit.MODULES
audit.MODULES.append(module)
audit.COMPONENTS.append('ONE common supported positive-event sample sequence now works for countably many HETEROGENEOUS original target/model families. Actual target T, model index type, native groups, determining evaluations, basis, dimension, numerical data and exposure-key source family may vary with each fixed enumerated condition. This supplies simultaneous original marginal selection across ALL targets before a later global local-law period, without asserting other-marginal invariance.')
audit.REMAINING=audit.REMAINING.replace('and a countable diagonal on every cofinal width sequence',
 'and one heterogeneous ALL-target countable diagonal on every cofinal width sequence')
source=Path(prefix+'-audit.py').read_text(encoding='utf-8')
for key,value in [('MODULES',audit.MODULES),('COMPONENTS',audit.COMPONENTS),('REMAINING',audit.REMAINING)]:
 source=re.sub(r'^'+key+r'=.*$',lambda _:key+'='+repr(value),source,flags=re.M)
Path(prefix+'-audit.py').write_text(source,encoding='utf-8')
log=prefix+'-AlignmentAllTargetsNativeCountableSelection-focused.txt'
result=audit.run(['lake','env','lean','-DautoImplicit=false',module],log)
assert not Path(log).read_bytes().strip()
results=audit.obj(prefix+'-focused-results.json')
results.append(dict(result,module=module,source_sha256=audit.digest(module)))
audit.write(prefix+'-focused-results.json',results)
root=Path('Hindman168.lean')
root.write_text(root.read_text(encoding='utf-8')+'\nimport Hindman168.AlignmentAllTargetsNativeCountableSelection\n',encoding='utf-8')
registry=Path('Verification.lean')
registry.write_text(registry.read_text(encoding='utf-8')+'\n#print axioms Hindman168.alignment_all_targets_native_cube_countable_supported_selection\n',encoding='utf-8')
audit.write(prefix+'-registration.json',dict(modules=audit.MODULES,names=audit.names(),declarations=audit.decls()))
review=Path(prefix+'-mathematical-review.txt')
text=review.read_text(encoding='utf-8')
text=text.split('Remaining proof work:\n')[0]+'''10. ALL target families. Countable native selection now permits actual T(q),
finite model index types iota(q), native groups D(q,nu), determining evaluation
lists, bases and source formulae to vary with the fixed condition q. Every
q's failure limit is proved by the unconditional native cap and cofinal W;
all q use the SAME original raw law and prescribed positive event. The
generic finite-prefix diagonal therefore supplies ONE shared sample sequence
for every marginal target, modulus and numerical/dimension condition. This
does NOT assert invariance of other marginals of a translated component.

Next-source audit. Original 08_alignment.tex 377 explicitly calls the actual
joint array state a LINEAR orbit adapted to the LOWER CENTRAL filtration.
Before invoking 07_cube_limits.tex, identify the actual state/cube tuple with
this linear orbit and prove its adaptation to that original filtration.
The existing loose multivariate log-degree bound is NOT that adaptation
statement. A stretched filtration or higher degree must not silently replace
the paper's step s or its cube dimensions through s+1. Existing
alignmentNativeJointModelOrbit_linear is the exact algebraic starting point.

Remaining proof work:
'''+audit.REMAINING+'\n'
review.write_text(text,encoding='utf-8')
print('Extended native audit to',len(audit.MODULES),'modules')
