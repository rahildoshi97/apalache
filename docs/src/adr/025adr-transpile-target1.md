# ADR-025: Transpilation to constrained Horn clauses

| authors                    |     last revised |
|----------------------------|-----------------:|
| Rahil Doshi, Rodrigo Otoni |       29-11-2023 |

**Table of Contents**

- [CLI Transpilation Target Option](#cli)
- [Code changes](#code)
- [Testing](#testing)
- [Summary](#summary)

## CLI Transpilation Target Option

CHC is to be an alternate transpilation target to the already available VMT option in Apalache.
Given this, a new option is to be added to the `transpile` command of the CLI.
Added `--transpile-target` flag (no envvar equivalent yet), whose default value will be `vmt`.
The option description is shown below.

```
--transpile-target : the transpilation target: vmt, chc (experimental), default: vmt
```

### Code changes

The following changes will be made to add target formalism option to the transpile command,
add support for CHC transpile, arithmetics and invariants in CHC transpilation 
and implement this in the CLI option:

- Add new string `var` to class `TranspileCmd` to add support for CHC encoding in the CLI using the `--transpile-target` flag.
- Add `ReTLAPreproPassImplForCHC` preprocessing pass that simplifies TLA+ expressions to CHC by running multiple transformations.
- Add `ReTLACombinedPredicateForCHC` for combined predicate to be used in `ReTLAToCHCModule`.
- Add `ReTLALanguagePredForCHC` to include the set of `TlaBoolOper` and `TlaArithOper`.
- Add new rules for CHC including `BoolRuleForCHC` for `TLABoolOper` such as `and`, `or`, `not`, `implies` and `TlaArithOper` such as `lt`, `le`, `gt`, `ge`. 
- Add new `IntRuleForCHC` to class `ToTermRewriterImplForCHC` which is a subclass of `ToTermRewriterForCHC`.
- `IntRuleForCHC` adds support for `TlaArithOper` such as `plus`, `minus`, `mult`, `div` and `ToTermRewriterImplForCHC` is the `ToTermRewriterForCHC` implementation from reTLA to SMT terms.
- `ToTermRewriterForCHC` defines a translation from TLA+ to SMT Terms.
- Add new value `chcWriter` in `ReTLAToCHCTranspilePassImpl` to transpile reTLA to CHC.
- Add new values to `TlaExToCHCWriter` to handle the last step of transpiling: convert the TLA spec to assemble the `.chc` output file.
- Add `TermToCHCWriter` to manages the translation of terms to strings, to be written to the final `.chc` output file.
- `ReTLAToCHCModule` binds all the CHC classes together like `ReTLAToVMTModule` for VMT classes.
- The infrastructure changes made for the `chc` transpilation type mirror the ones made for the `vmt` one.
  See [PR ---] for details.

## Testing

### Unit test

- Add file `TestReTLALanguagePredForCHC` to add support for integer expressions for CHC based on `TestReTLALanguagePred` for VMT.

### Integration test

- Add new file `NoArithOper.tla` to test for `--transpile-target=vmt` flag.
- Add new file `ArithOper.tla` to test for `--transpile-target=chc` flag to check support for arithmetic operations.

## Summary

<!-- Statement to summarize, following the following formula: -->

This ADR describes the support for transpilation from (a subset of) TLA+ to constrained [Horn clauses](https://en.wikipedia.org/wiki/Horn_clause) (CHC).
The support added is based on the transpilation machinery targeting VMT that was implemented following in [ADR-016](https://apalache.informal.systems/docs/adr/016adr-retla.html).

The modified code successfully transpiles the TLA to it's CHC equivalent.
It passes all the unit and integration tests with `make test` and `make integration`.

## Context

<!-- Communicates the forces at play (technical, political, social, project).
     This is the story explaining the problem we are looking to resolve.
-->

## Options

<!-- Communicate the options considered.
     This records evidence of our circumspection and documents the various alternatives
     considered but not adopted.
-->

## Solution

<!-- Communicates what solution was decided, and it is expected to solve the
     problem. -->

## Consequences

<!-- Records the results of the decision over the long term.
     Did it work, not work, was changed, upgraded, etc.
-->
