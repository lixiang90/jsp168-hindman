from pathlib import Path
import re

def context(src, closed=False):
    marker='attribute [local instance] lieGroup_smooth_min_three'
    return src.replace(marker,
        'variable (V : Submodule ℝ E) '+('[IsClosed (V : Set E)] ' if closed else '')+
        '\n  (hV : V ≤ nativeLieCenterModel (I := I) (G := G))\n'
        '  (hrat : nativeLatticeRationalSubspace (E := E) (I := I) (G := G) Γ V)\n\n'+marker)

# Each generated proof remains a separate actual proof, reviewed and compiled.
src=Path('Hindman168/NativeCenterLatticeCoordinates.lean').read_text(encoding='utf-8')
src=src.replace('import Hindman168.NativeCenterRationalBasis',
    'import Hindman168.NativeCentralSubspaceLogSpanning\nimport Hindman168.NativeCentralSubspaceExponentialHomeomorph')
src=src.replace('nativeLieCenterModel (I := I) (G := G)','V')
src=src.replace('Subgroup.center G','nativeCentralSubspaceSubgroup (I := I) V hV')
src=src.replace('nativeLieCenterExponentialHomeomorph (I := I) (G := G)',
    'nativeCentralSubspaceExponentialHomeomorph (I := I) V hV')
src=src.replace('nativeCenterLogLattice_isZLattice (E := E) (I := I) Γ',
    'nativeCentralSubspaceLogLattice_isZLattice (I := I) Γ V hV hrat')
src=src.replace('nativeCenterLogLattice_discrete (E := E) (I := I) Γ',
    'nativeCentralSubspaceLogLattice_discrete (I := I) Γ V hV')
src=src.replace('nativeCenterLogLattice (I := I) Γ',
    'nativeCentralSubspaceLogLattice (I := I) Γ V hV')
src=src.replace('nativeCenterLattice','nativeCentralSubspaceLattice')
src=src.replace('native_center_lattice','native_central_subspace_lattice')
src=re.sub(r'(nativeCentralSubspaceLattice[A-Za-z0-9_]*|native_central_subspace_lattice[A-Za-z0-9_]*) (?:\(I := I\) )?Γ',
    r'\1 (I := I) Γ V hV hrat',src)
# Γ remains an explicit parameter of each theorem/definition, so hrat does too.
src=src.replace('(Γ : Subgroup G)\n    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]',
    '(Γ : Subgroup G)\n    [DiscreteTopology Γ] (V : Submodule ℝ E)\n'
    '    (hV : V ≤ nativeLieCenterModel (I := I) (G := G))\n'
    '    (hrat : nativeLatticeRationalSubspace (E := E) (I := I) Γ V)')
src=re.sub(r'(native_central_subspace_lattice[A-Za-z0-9_]*)(?=[,\]])',
    r'\1 (I := I) Γ V hV hrat',src)
Path('Hindman168/NativeCentralSubspaceLatticeCoordinates.lean').write_text(src,encoding='utf-8')
print('Prepared actual central-subspace lattice coordinate source.')

def transform_calls(src):
    src=src.replace('nativeLieCenterModel (I := I) (G := G)','V')
    src=src.replace('Subgroup.center G','(nativeCentralSubspaceSubgroup (I := I) V hV)')
    src=src.replace('nativeCenterQuotientProjection (I := I) (G := G)',
        'finiteRealQuotientProjection V')
    src=src.replace('nativeCenterQuotient_nativeExponential_projection (I := I) (G := G)',
        'nativeCentralSubspaceQuotient_nativeExponential_projection (I := I) V hV')
    src=src.replace('nativeCenterQuotient_nativeLogarithm_projection (I := I) (G := G)',
        'nativeCentralSubspaceQuotient_nativeLogarithm_projection (I := I) V hV')
    src=src.replace('NativeCenterQuotientNormedModel','NativeCentralSubspaceQuotientCharted')
    src=src.replace('NativeCenterQuotientNativeExponential','NativeCentralSubspaceQuotientNativeExponential')
    src=src.replace('nativeCenterQuotient','nativeCentralSubspaceQuotient')
    src=re.sub(r'(nativeCentralSubspaceQuotient[A-Za-z0-9_]*) \(I := I\) \(G := G\)',
        r'\1 (I := I) V hV',src)
    for part in ['LatticeCoordinates','CoordinateRecovery','OrderedCoordinates','LatticeIndependent',
                 'PairSmoothInverse','LatticeGeneratorLift','CoordinateExtension']:
        src=src.replace('NativeCenter'+part,'NativeCentralSubspace'+part)
    for old,new in [('nativeCenterLattice','nativeCentralSubspaceLattice'),
                    ('native_center_lattice','native_central_subspace_lattice'),
                    ('nativeCenterCoordinateRecovery','nativeCentralSubspaceCoordinateRecovery'),
                    ('native_center_coordinate_recovery','native_central_subspace_coordinate_recovery')]:
        src=src.replace(old,new)
    src=re.sub(r'(nativeCentralSubspaceLattice[A-Za-z0-9_]*|native_central_subspace_lattice[A-Za-z0-9_]*|nativeCentralSubspaceCoordinateRecovery|native_central_subspace_coordinate_recovery[A-Za-z0-9_]*) (?:\(I := I\) )?Γ',
        r'\1 (I := I) Γ V hV hrat',src)
    src=src.replace('(Γ : Subgroup G)\n    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]',
        '(Γ : Subgroup G)\n    [DiscreteTopology Γ] (V : Submodule ℝ E) [IsClosed (V : Set E)]\n'
        '    (hV : V ≤ nativeLieCenterModel (I := I) (G := G))\n'
        '    (hrat : nativeLatticeRationalSubspace (E := E) (I := I) Γ V)')
    src=src.replace('attribute [local instance] lieGroup_smooth_min_three',
        'attribute [local instance] lieGroup_smooth_min_three\n'
        'attribute [local instance] nativeCentralSubspaceSubgroup_normal')
    src=re.sub(r'(native_central_subspace_(?:lattice|coordinate_recovery)[A-Za-z0-9_]*)(?=[,\]])',
        r'\1 (I := I) Γ V hV hrat',src)
    return src

src=transform_calls(Path('Hindman168/NativeCenterCoordinateRecovery.lean').read_text(encoding='utf-8'))
src=src.replace('true lattice center coordinates','true lattice central-subspace coordinates')
src=src.replace('genuinely central original group element','original group element in the specified subgroup')
Path('Hindman168/NativeCentralSubspaceCoordinateRecovery.lean').write_text(src,encoding='utf-8')

src=transform_calls(Path('Hindman168/NativeCenterOrderedCoordinates.lean').read_text(encoding='utf-8'))
src=src.replace('native_center_exponential_list_sum','native_central_subspace_exponential_list_sum')
src=src.replace('(l : List (V))',
    '(V : Submodule ℝ E) (hV : V ≤ nativeLieCenterModel (I := I) (G := G))\n    (l : List V)')
src=src.replace('nativeLieExponential_add_of_mem_centerModel v.property',
    'nativeLieExponential_add_of_mem_centerModel (hV v.property)')
src=src.replace('native_central_subspace_exponential_list_sum (I := I) (G := G)',
    'native_central_subspace_exponential_list_sum (I := I) (G := G) V hV')
Path('Hindman168/NativeCentralSubspaceOrderedCoordinates.lean').write_text(src,encoding='utf-8')

src=transform_calls(Path('Hindman168/NativeCenterLatticeIndependent.lean').read_text(encoding='utf-8'))
# One theorem uses implicit Γ and a shorter binder layout.
src=src.replace('{m : ℕ} (Γ : Subgroup G)\n    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]',
    '{m : ℕ} (Γ : Subgroup G)\n    [DiscreteTopology Γ] (V : Submodule ℝ E) [IsClosed (V : Set E)]\n'
    '    (hV : V ≤ nativeLieCenterModel (I := I) (G := G))\n'
    '    (hrat : nativeLatticeRationalSubspace (E := E) (I := I) Γ V)')
Path('Hindman168/NativeCentralSubspaceLatticeIndependent.lean').write_text(src,encoding='utf-8')
print('Prepared actual central-subspace recovery, ordered products and independence sources.')

src=transform_calls(Path('Hindman168/NativeCenterPairSmoothInverse.lean').read_text(encoding='utf-8'))
src=src.replace('native_center_pair_smooth_inverse','native_central_subspace_pair_smooth_inverse')
src=src.replace('native_ordered_exponential_coordinates_center_projection (I := I) (G := G)',
    'native_ordered_exponential_coordinates_central_subspace_projection (I := I) V hV')
src=src.replace('import Hindman168.NativeCenterQuotientSmoothProjection',
    'import Hindman168.NativeCentralSubspaceQuotientSmoothProjection\nimport Hindman168.NativeCentralSubspaceOrderedProjection')
Path('Hindman168/NativeCentralSubspacePairSmoothInverse.lean').write_text(src,encoding='utf-8')
print('Prepared actual central-subspace pair smooth inverse source.')
