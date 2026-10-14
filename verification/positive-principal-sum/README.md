# Tolerance-first deduction of a finite FS/FP witness

The eleven `PositivePrincipalSum...` modules implement the finite counting
deduction in Section 2.5 of the OpenAI paper. The main interface is
`Hindman168.principal_final_deduction_tolerances`.

For fixed `n,m,r`, finite scale catalogues `B,A` with `FiniteScaleClosure`,
and a positive alignment mass bound `delta`, it chooses positive
`theta < 1/4` and `eta` BEFORE the master parameters and models. It then
uses the exact existing `PrincipalPredictionLimitData` at tolerance `eta`,
unit-range models, admissible master parameters, and a positive ordinary
liminf for the explicit simultaneous adding-pair event to obtain a set of
exactly `m+1` positive integers with all nonempty sums and products in one
color.

The proof removes calibration failures by a finite union bound, selects a
product chain on the actual scaled integer inputs, proves the exact model
integrand lower bound, sums prediction errors, and extracts an actual
witness. It assumes neither positivity of a model/weighted count nor a
samplewise choice of a large model term. Its finite chain-selection input
is still explicit in the fixed-`n` endpoint, but a suitable `n` and that
input are already supplied by `principal_product_chain_selection` using
the repository's existing product-chain theorem. No new Ramsey assertion
is left unproved.

## Remaining input boundary

`PrincipalSumAlignmentEvent` and `PrincipalAddingAlignment` are new concrete
predicates expressing the paper's simultaneous adding-pair condition.
The integer coefficient ratios are proved to equal the original rational
ratios at all sufficiently late stages. However, no named adapter from an
existing native Alignment predicate to this event's liminf has yet been
proved in these eleven modules. That adapter and the uniform Principle 2.4
construction remain open, including choosing `B,A,delta` independently of
`theta` and model complexity.

Likewise, the original prediction-data structure is an input, not an
unconditional proof of Principle 2.3. Its required higher-order native
inverse input remains open. Thus this is the conditional final deduction,
not an unconditional proof of `FiniteConjecture` or `StrongConjecture`.

## Reproduce

Use the unchanged Lean 4.32.2 and locked mathlib revision:

```sh
lake build Hindman168.PositivePrincipalSumFinalDeduction
lake env lean verification/positive-principal-sum/Axioms.lean
```

The focused build completed with 5,114 jobs. All eleven frozen sources
were subsequently re-elaborated individually; the commands and output are
in `source-check.txt`. All 22 named new theorems have axiom sets contained
in `propext`, `Classical.choice`, and `Quot.sound`. The source hashes are
recorded separately.

These author-side checks are not external peer review or a complete
independent kernel replay. Canonical imports and the original 3,059-file
snapshot manifest remain unchanged; the additions are not covered by that
original manifest. Its existing source hashes were separately rechecked.
No competing proof core or new axiom was introduced.
