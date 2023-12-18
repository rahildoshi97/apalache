# ADR-025: Transpilation to constrained Horn clauses

| authors                    | last revised |
|----------------------------|-------------:|
| Rahil Doshi, Rodrigo Otoni |   18-12-2023 |

**Table of Contents**

- [Overview](#Overview)
- [CLI Transpilation Target Option](#cli)
- [Code changes](#code)
- [Testing](#testing)
- [Summary](#summary)

## Overview
CHC is to be an alternate transpilation target to the already available vmt option in Apalache.
Given this, a new option is to be added to the `transpile` command of the CLI in addition to adding support for integers .

## CLI Transpilation Target Option

Added `--transpile-target` flag for chc (no envvar equivalent yet), whose default value will be `vmt`.
The option description is shown below.

```
--transpile-target : the transpilation target: vmt, chc (experimental), default: vmt
```

### Code changes

The following changes will be made to add target formalism option to the transpile command,
add support for chc transpile, arithmetics and invariants in chc transpilation 
and implement this in the CLI option:

#### Target formalism option to the transpile command and CLI option implementation

- Add new class `Transpiler` with `@param` `transpilationTarget` in `options.scala` 
  to specify the transpilation target options added under the new class `TranspilationTarget` 
  with `TranspilationTarget.VMT` and `TranspilationTarget.CHC` for vmt and chc respectively.
- Add new string `var` `transpilationTarget` to class `TranspileCmd` to add support for chc encoding in the CLI using the `--transpile-target` flag.

#### Support for CHC transpile

- Add new class `ReTLACombinedPredicateForCHC` extending `ReTLACombinedPredicate` to use in `ReTLAToVMTModule` with
  new class `ReTLALanguagePredForCHC` to test whether the expression fits into the reTLA with arithmetics fragment.
- Add new class `ReTLALanguagePredForCHC` extending `ReTLALanguagePred` to include `TlaBoolOper` and `TlaArithOper`.
- Add new class `ReTLAPreproPassImplForCHC` that extends `ReTLAPreproPassImpl` 
  to simplify TLA+ expressions to chc by running multiple transformations supported with `ReTLALanguagePredForCHC`.
- Add new class `ReTLAToCHCModule` extending `ReTLAToVMTModule` to bind the chc classes together and
  transpiles reTLA input to chc.
- Add new class `ReTLAToCHCTranspilePassImpl` with `TlaExToCHCWriter` to handle the last step of transpiling
  by assembling the .chc output file. Given a disassembled module (extracted init, next, inv, etc.), 
  CHCWriter determines which parts get which `VMTExpr` wrappers. Then, using TermToCHCWriter, 
  it translates the terms to output strings, and adds sort/function declarations and definitions.
- Add `TermToCHCWriter` to manage the translation of terms to strings to be written to the final output file.
- Add new class `ToTermRewriterImplForCHC` extending `ToTermRewriterImpl` to implement the `ToTermRewriter` from reTLA to SMT Terms with additional
  support for arithmetics with a new `IntRuleForCHC` and `BoolRuleForCHC`.
- Add new class `ValueRuleForCHC` extending `ValueRule` to handle the conversion of literals to names. 
  It renames all variables from  `x'` to `x.prime` for chc.

#### Support for arithmetics and invariants

- Add new `BoolRuleForCHC` extending `BoolRule` for `TlaArithOper` such as `lt`, `le`, `gt`, `ge` in addition to 
  `TLABoolOper` such as `and`, `or`, `not`, `implies` already supported for vmt. 
- Add new `IntRuleForCHC` to add support for `TlaArithOper` such as `plus`, `minus`, `mult`, `div`.
- Add support for invariants in `TlaExToCHCWriter`.


- The infrastructure changes made for the `chc` transpilation type mirror the ones made for the `vmt` one.
  See [[PR 9](https://github.com/rahildoshi97/apalache/pull/9)] for details.

## Testing

### Unit test

Unit tests can be run using the below command:
```
make test
```

- Add new class `TestReTLALanguagePredForCHC` to add support for testing language predicates 
  with `ReTLALanguagePredForCHC`, supporting arithmetics (integer expressions) for `chc`.

### Integration test

Integration tests can be run using the below command:
```
make integration
```

- Add new `NoArithOper.tla` with `EXITCODE: OK` for `--transpile-target=vmt` and `--transpile-target=chc` flag.
- Add new `ArithOper.tla` with `EXITCODE: OK` for `--transpile-target=chc` flag to test support for arithmetic operations
  and `EXITCODE: ERROR` for `transpile` (no flag) and `--transpile-target=vmt`.

## Summary

<!-- Statement to summarize, following the following formula: -->

This ADR describes the support for transpilation from (a subset of) TLA+ to constrained [Horn clauses](https://en.wikipedia.org/wiki/Horn_clause) (CHC).
The support added is based on the transpilation machinery targeting vmt that was implemented following in [ADR-016](https://apalache.informal.systems/docs/adr/016adr-retla.html).

The modified code successfully transpiles the TLA spec to it's CHC equivalent.
It passes all the unit and integration tests with `make test` and `make integration`.
