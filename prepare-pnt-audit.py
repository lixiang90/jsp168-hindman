"""Make an isolated, attributed AP-PNT proof closure for Lean 4.32.2.

No theorem proofs are altered. Blueprint-only syntax is removed, together
with an unused block containing two unfinished decay lemmas. Compilation
must establish that the retained AP proof does not need that block.
"""
from pathlib import Path
import argparse
import json
import re
import shutil
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--source', type=Path, required=True, help='Pinned PNT+ Git checkout')
parser.add_argument('--output', type=Path, required=True, help='Separate audit directory')
args = parser.parse_args()
SOURCE = args.source.resolve()
DEST = args.output.resolve()
PROJECT = Path(__file__).resolve().parent
PIN = '747e480362ef6a0a7341055a84372333d72fa62a'
if DEST == PROJECT or DEST == SOURCE or DEST in SOURCE.parents or DEST in PROJECT.parents:
    parser.error('Output must be a separate audit directory, not a source/project root or ancestor')
source_commit = subprocess.check_output(
    ['git', '-C', str(SOURCE), 'rev-parse', 'HEAD'], text=True).strip()
if source_commit != PIN:
    parser.error(f'Source must be pinned to {PIN}, got {source_commit}')
DEST.mkdir(parents=True, exist_ok=True)

def skip_comment(s, i):
    assert s.startswith('/-', i)
    depth = 1
    j = i + 2
    while depth:
        if s.startswith('/-', j):
            depth += 1
            j += 2
        elif s.startswith('-/', j):
            depth -= 1
            j += 2
        else:
            j += 1
        if j > len(s):
            raise ValueError('unclosed Lean comment')
    return j

def strip_blueprints(s):
    s = re.sub(r'^import Architect\s*\n', 'import Batteries.Tactic.Lemma\n', s, flags=re.M)
    out = []
    i = 0
    while i < len(s):
        if s.startswith('blueprint_comment', i):
            j = i + len('blueprint_comment')
            while s[j].isspace():
                j += 1
            i = skip_comment(s, j)
        elif s.startswith('@[blueprint', i):
            j, depth = i + 2, 1
            while depth:
                if s.startswith('/-', j):
                    j = skip_comment(s, j)
                elif s[j] == '"':
                    j += 1
                    while s[j] != '"':
                        j += 2 if s[j] == '\\' else 1
                    j += 1
                elif s[j] == '[':
                    depth += 1
                    j += 1
                elif s[j] == ']':
                    depth -= 1
                    j += 1
                else:
                    j += 1
            i = j
        else:
            out.append(s[i])
            i += 1
    return ''.join(out)

todo = ['PrimeNumberTheoremAnd.Consequences']
seen = set()
while todo:
    mod = todo.pop()
    if mod in seen:
        continue
    seen.add(mod)
    relative = Path(*mod.split('.')).with_suffix('.lean')
    original = (SOURCE / relative).read_text(encoding='utf-8')
    todo.extend(re.findall(r'^import (PrimeNumberTheoremAnd\S+)', original, flags=re.M))
    result = strip_blueprints(original)
    if mod == 'PrimeNumberTheoremAnd.Wiener':
        first = result.index('theorem prelim_decay_2 ')
        last = result.index('lemma decay_bounds_key ')
        result = result[:first] + '-- Unused unfinished alternative decay block omitted.\n\n' + result[last:]
    notice = ('/- Modified excerpt of PrimeNumberTheoremAnd at ' + PIN + '.\n'
              'Original authors and contributors retain attribution; Apache-2.0.\n'
              'Changes: removed blueprint annotations and the unused unfinished\n'
              'alternative decay block. Retained proofs are unchanged. -/\n\n')
    path = DEST / relative
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(notice + result, encoding='utf-8')

shutil.copyfile(SOURCE / 'LICENSE', DEST / 'LICENSE-PNTPLUS')
config = '''name = "pnt_ap_audit"
defaultTargets = ["PrimeNumberTheoremAnd"]

[leanOptions]
autoImplicit = false

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4"
rev = "905b95818eb32af7874a58b427f50c1711a5e96c"

[[lean_lib]]
name = "PrimeNumberTheoremAnd"
'''
(DEST / 'lakefile.toml').write_text(config)
shutil.copyfile(SOURCE / 'lean-toolchain', DEST / 'lean-toolchain')
shutil.copyfile(PROJECT / 'lake-manifest.json', DEST / 'lake-manifest.json')
(DEST / 'CheckAP.lean').write_text('import PrimeNumberTheoremAnd.Consequences\n'
    '#print axioms WienerIkeharaTheorem\'\'\n'
    '#print axioms WeakPNT_AP\n'
    '#print axioms chebyshev_asymptotic_pnt\n')
(DEST / 'source-modules.json').write_text(json.dumps(sorted(seen), indent=2))
print(f'Prepared {len(seen)} attributed modules at {PIN}')
