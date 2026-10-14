from pathlib import Path
p = Path('Hindman168/NativeDiagonalFactorProbability.lean')
lines = p.read_text(encoding='utf-8').splitlines()
out = []
count = 0
for line in lines:
    out.append(line)
    if 'letI : MeasurableSpace (nativeNilmanifoldProduct D D).G :=' in line:
        indent = line[:len(line)-len(line.lstrip())]
        out.append(indent+'letI : MeasurableSpace (D.G × D.G) := borel (D.G × D.G)')
        out.append(indent+'letI : (diagonalCenterSubgroup D.G).Normal := diagonal_center_normal D.G')
        count += 1
assert count == 8
p.write_text('\n'.join(out)+'\n', encoding='utf-8')
print('Installed explicit actual product measurable space and proved diagonal normality in '+str(count)+' scopes')
