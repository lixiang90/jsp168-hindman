from pathlib import Path
import importlib.util
spec=importlib.util.spec_from_file_location('a','round-native-array-readings-audit.py')
a=importlib.util.module_from_spec(spec);spec.loader.exec_module(a)
results=a.obj(a.PREFIX+'-focused-results.json')[:4]
for p in a.MODULES[4:]:
 r=a.run(['lake','env','lean','-DautoImplicit=false',p],a.PREFIX+'-'+Path(p).stem+'-focused.txt')
 assert not a.read(r['log']).strip()
 r.update(module=p,source_sha256=a.digest(p));results.append(r)
 print('Checked '+p,flush=True)
a.write(a.PREFIX+'-focused-results.json',results)
ds=a.declarations()
names=['Hindman168.'+name for p,values in ds.items() for _,name in values]
root,reg=a.read('Hindman168.lean'),a.read('Verification.lean')
for p in a.MODULES[4:]:
 line='import '+p[:-5].replace('/','.')
 assert line not in root.splitlines();root+='\n'+line+'\n'
for name in names:
 if '#print axioms '+name not in reg.splitlines():reg+='\n#print axioms '+name+'\n'
Path('Hindman168.lean').write_text(root,encoding='utf-8')
Path('Verification.lean').write_text(reg,encoding='utf-8')
a.write(a.PREFIX+'-registration.json',dict(modules=a.MODULES,names=names,declarations=ds))
