# ADR-025: Transpile-target

| authors     | last revised |
|-------------|-------------:|
| Rahil Doshi |   2023-03-10 |

**Table of Contents**

- [Summary (Overview)](#summary)
- [Context (Problem)](#context)
- [Options (Alternatives)](#options)
- [Solution (Decision)](#solution)
- [Consequences (Retrospection)](#consequences)

## Summary

<!-- Statement to summarize, following the following formula: -->

This ADR describes the support for arithmetic operators as well as an alternate (experimental) transpilation taget for SMT encoding called CHC.
This is an extension of an already available transpilation target in Apalache called VMT.

## CLI Transpilation Target Option

CHC is to be an alternate transpilation target to the already available VMT option in Apalache.
Given this, a new option is to be added to the `transpile` command of the CLI. The default transpilaton target will be
the existing one (VMT). The option description is shown below. 
The envvar `ENCODING_TYPE ?????` can also be used to set the target, see the [model checking parameters] for details. 

```
--transpile-target : the transpile targets: vmt, chc (experimental), default: vmt
```

### Code changes

The following changes will be made to implement the new CLI option:

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
  See [PR -----] for details.

## Testing

## Summary

<!-- Statement to summarize, following the following formula: -->

In the context of our development of Apalache
facing the need to communicate and record our significant decisions
we decided for adopting an ADR template adapted from the "Alexandrian Form"
to achieve concise and consistent records of our architectural decisions
accepting the regimentation and loss of unexpected possibility that comes with adopting a template.

## Context

<!-- Communicates the forces at play (technical, political, social, project).
     This is the story explaining the problem we are looking to resolve.
-->

The development of Apalache is picking up momentum. We have more contributors
joining us immanently, and hope to welcome and support external OSS contributors
soon. As the number of contributors grows, so does the importance of
establishing supports to encourage communication between individuals and accross
time.

Maintaining records of architectural decisions (aka "ADR"s) is advised by
informal.systems company policy, but the details of how such records should be
written, kept, or used, have not been settled. I hypothesize that we have much
to gain by experimenting with a consistent, well reasoned format for our ADRs. I
think it will help us be mindful of their purpose, make them more useful as
diagnostic and prognostic tools, and help reduce the amount of time needed for
drafting and approval.

## Options

<!-- Communicate the options considered.
     This records evidence of our circumspection and documents the various alternatives
     considered but not adopted.
-->

While considering approaches to ADRs, I consulted the following resources, and
many of the children links to found therein, :

- https://adr.github.io/
- https://github.com/joelparkerhenderson/architecture-decision-record
- https://en.wikipedia.org/wiki/Architectural_decision

I was surprised by the amount of literature surrounding this topic, and wanted
to select something that would help focus and clarify our ADRs, while avoiding
any undue burden that might come from associated management or development
practices.

Each approach to ADRs can inspire a family of templates. I found most of them to
be too involved or intimidating, and I opted for the most light weight approach
I could find, while making some changes to clarify the language and content to
support our context and existing styles of communication.

## Solution

<!-- Communicates what solution was decided, and it is expected to solve the
     problem. -->
     
I propose adopting this simple articulation of ADRs and their purpose as our
guide:

> An architecture decision record (ADR) is a document that captures an important
> architecture decision made along with its context and consequences.

(see
https://github.com/joelparkerhenderson/architecture-decision-record#what-is-an-architecture-decision-record)

Following the [Teamwork
advice](https://github.com/joelparkerhenderson/architecture-decision-record#teamwork-advice)
offered in that same document, I propose adopting an ADR template that puts all
emphasis on the key purposes of the communication, leaving it up to each author
to fill in the template with as much or as little detail as they think necessary
to support the particular decision in question.

To this end, I propose [this template](./NNNadr-template.md), which is adapted
from the [Alexandrian
pattern](https://github.com/joelparkerhenderson/architecture-decision-record/blob/main/templates/decision-record-template-for-alexandrian-pattern/index.md).
This template is itself adapted from the so-called ["Alexandrian
form"](https://wiki.c2.com/?AlexandrianForm).  Martin Fowler has a [succinct
summary of its
qualities](https://www.martinfowler.com/articles/writingPatterns.html#AlexandrianForm)
in its native context of "design patterns".

## Consequences

<!-- Records the results of the decision over the long term.
     Did it work, not work, was changed, upgraded, etc.
-->
