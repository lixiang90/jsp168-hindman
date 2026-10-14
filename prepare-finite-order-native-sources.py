from pathlib import Path

base = Path('Hindman168/SelectedNativeShortCubeModels.lean').read_text(encoding='utf-8')
base = base.replace('import Hindman168.MasterModelDifferenceShortCube',
                    'import Hindman168.FiniteOrderModelShortCubeThreshold')
base = base.replace('selected_native_shortCube_models', 'finite_order_native_shortCube_models')
base = base.replace('(n s d : ℕ)\n    (hinverse : HasNativePeriodicIntervalInverse.{u} s (2 ^ d + 2 ^ d - 1))',
                    '(n s : ℕ)\n    (Q : Type*) [Fintype Q] (dim : Q → ℕ)\n    (hinverse : ∀ q, HasNativePeriodicIntervalInverse.{u} s (2 ^ dim q + 2 ^ dim q - 1))')
base = base.replace('∀ (pol : MvPolynomial', '∀ q : Q, ∀ (pol : MvPolynomial')
base = base.replace('e b)) d J pol', 'e b)) (dim q) J pol')
base = base.replace('master_model_difference_shortCube_threshold s d hinverse η hη',
                    'finite_order_model_shortCube_threshold Q s dim hinverse η hη')
base = base.replace('intro pol hpol P hP hpolP', 'intro q pol hpol P hP hpolP')
base = base.replace('exact hshort hM D', 'exact hshort q hM D')
base = base.replace('The chosen coarse model then works at every permissible',
                    'One J and one positive threshold serve the entire finite dimension list.\nThe chosen coarse model then works at every permissible')
assert '(n s d : ℕ)' not in base and 's d hinverse' not in base
Path('Hindman168/FiniteOrderNativeShortCubeModels.lean').write_text(base, encoding='utf-8')

chain = Path('Hindman168/SelectedNativeChainShortCubeModels.lean').read_text(encoding='utf-8')
chain = chain.replace('import Hindman168.SelectedNativeShortCubeModels',
                      'import Hindman168.FiniteOrderNativeShortCubeModels')
chain = chain.replace('chain_selected_native_shortCube_models', 'finite_order_native_chain_prediction')
chain = chain.replace('(n s d : ℕ)\n    (hinverse : HasNativePeriodicIntervalInverse.{u} s (2 ^ d + 2 ^ d - 1))',
                      '(n s : ℕ)\n    (Q : Type*) [Fintype Q] (dim : Q → ℕ)\n    (hinverse : ∀ q, HasNativePeriodicIntervalInverse.{u} s (2 ^ dim q + 2 ^ dim q - 1))')
chain = chain.replace('∀ i a (pol : MvPolynomial', '∀ i a (q : Q) (pol : MvPolynomial')
chain = chain.replace('e (p i))) d J pol', 'e (p i))) (dim q) J pol')
chain = chain.replace('selected_native_shortCube_models.{u} ι n s d hinverse η hη',
                      'finite_order_native_shortCube_models.{u} ι n s Q dim hinverse η hη')
chain = chain.replace('intro i a pol hpol P hP hpolP', 'intro i a q pol hpol P hP hpolP')
chain = chain.replace(')).2 pol hpol P hP hpolP', ')).2 q pol hpol P hP hpolP')
chain = chain.replace('The same J and pre-Ramsey thresholds',
                      'The same J and pre-Ramsey thresholds for the whole finite dimension list')
assert '(n s d : ℕ)' not in chain and 's d hinverse' not in chain
Path('Hindman168/FiniteOrderNativeChainPrediction.lean').write_text(chain, encoding='utf-8')
print('Wrote the finite-order selected model and chain prediction sources.')
