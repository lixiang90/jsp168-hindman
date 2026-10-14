"""Exact rational author certificate for the source's displayed slab bound.

This is NOT Lean measure formalization or a counterexample to Proposition 5.3.
It checks exact disjoint interval endpoints and their lengths on [0,1].
"""
from fractions import Fraction as F
from pathlib import Path
import json

delta = F(1,100)
zeta = F(100)
theta = F(0)
tolerance = delta*zeta/10
assert zeta == 1/delta and tolerance == F(1,10)
intervals = [(max(F(0),(F(k)-tolerance)/zeta),
              min(F(1),(F(k)+tolerance)/zeta),k) for k in range(101)]
assert all(a <= b for a,b,k in intervals)
assert all(intervals[j][1] < intervals[j+1][0] for j in range(100))
assert all(abs(theta+zeta*a-k) <= tolerance and
           abs(theta+zeta*b-k) <= tolerance for a,b,k in intervals)
assert (theta+zeta*F(0),theta+zeta*F(1)) == (F(0),F(100))
# Every nearby integer lies in [0,100]; each affine preimage is the checked
# clipped interval. The endpoints do not affect one-dimensional Lebesgue volume.
volume = sum((b-a for a,b,k in intervals),F(0))
claimed = delta/2
assert volume == F(1,5) and claimed == F(1,200) and volume > claimed
result = dict(reference='https://arxiv.org/html/0709.3562v4',
    location='Proposition 5.3 proof, Omega and enlarged Omega before (5.10)-(5.11)',
    kind='exact rational author interval certificate; NOT Lean measure proof',
    theta=str(theta),delta=str(delta),zeta=str(zeta),tolerance=str(tolerance),
    interval_count=len(intervals),intervals=[dict(left=str(a),right=str(b),nearby_integer=k)
                                         for a,b,k in intervals],
    exact_slab_volume=str(volume),displayed_upper_bound=str(claimed),
    violates_displayed_volume_bound=True,
    refutes_proposition_itself=False,unavoidable_obstruction=False,
    next_action='Prove corrected slab/neighborhood bounds with explicit dependence on the coefficient budget; do not use displayed bound unchanged.')
path = Path('round-native-rational-fractional-bracket-input-slab-review.json')
path.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in result.items() if k!='intervals'}))
