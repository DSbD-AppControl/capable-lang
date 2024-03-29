# README

[![Ubuntu](https://github.com/DSbD-AppControl/capable-lang/actions/workflows/ci-ubuntu.yml/badge.svg)](https://github.com/DSbD-AppControl/capable-lang/actions/workflows/ci-ubuntu.yml)

We are interested in how CHERI-Style Capabilities inter-play with session-types in imperative languages such as Rust/C.

Capable is a barebones imperative language with ML-style references written in Idris2 as a intrinsically-scoped/typed EDSL.
Capable is our experimental language to see how the type-system should work.

This repository should be seen as the reference implementation.
When realising on CHERIBSD (or another platform with access to capabilities through MUSL), we can use different languages.

## What is Capable:

Well... it is capable of

1. being an imperative language with n-ary functions and expression-oriented function bodies
1. supporting for ML style references
1. supporting type synonyms
1. supporting Ints, Strings, Chars, Bool, and various primitive operations
1. supporting file & process IO
1. supporting tuples, structures, and tagged unions
1. bi-directional type-checking
1. simple typed holes
1. supporting Multi-Party Session Types (although the runtime needs developing)

## Note

This is a constant work in progress.

The code is not polished.

## Contributions

What we contribute now:

1. Practical example of using dependent types to realise a barebones language with a _complete_ pipeline
1. Native support for specifying session types and their projection, rather than through embedding and (ab)use of existing functionality

What we will contribute:

1. A session typed runtime, including session error handling
1. Capabilities, and what they may look like

## Things to do that are interesting

+ true coverage checking & pattern matching...
+ Memory management _a la_ rust?
+ linear/quantitative types?
+ Completeness of Type-Checker. It would be nice to do the type-checking properly through a proof, but that is not a high priority.
+ How best to provide a session-typed runtime.
+ How best to add capabilities.
+ ...


## Some behind the scenes

Evaluation is through definitional interpretation based on work.

> Casper Bach Poulsen, Arjen Rouvoet, Andrew Tolmach, Robbert
> Krebbers, and Eelco Visser. 2017. Intrinsically-typed definitional
> interpreters for imperative languages. Proc. ACM Program. Lang. 2,
> POPL, Article 16 (January 2018), 34
> pages. https://doi.org/10.1145/3158104

Session Types is through _Less is More_, based on:

> Alceste Scalas and Nobuko Yoshida. 2019. Less is more: multiparty
> session types revisited. Proc. ACM Program. Lang. 3, POPL, Article
> 30 (January 2019), 29 pages. https://doi.org/10.1145/3290343

Use of Crash Local types is based on:

> Simon Fowler, Sam Lindley, J. Garrett Morris, and Sára
> Decova. 2019. Exceptional asynchronous session types: session types
> without tiers. Proc. ACM Program. Lang. 3, POPL, Article 28 (January
> 2019), 29 pages. https://doi.org/10.1145/3290341

## Artefact

We also include scripts to generate a reproducible artefact.

Please consult the following project to generate the base virtual box image required, and how we approach the building of the artefact.

https://github.com/jfdm/packer-idris

Once you have generated the image you can generate the artefact as follows:

```bash
SOURCE_VM="<location of the base ovf>" make artefact
```

This will generate in `artefact` the following files:

1. `capable.box` :: A Virtual Box virtual machine that contains Capable's source code & test suite;
2. `capable.tar.gz` :: A copy of Capable's source code, and generated IdrisDoc;
3. `capable_doc.tar.gz` :: A copy of the IdrisDoc for the coding project;
4. `capable_html.tar.gz` :: A copy of the katla generated html showing semantically highlighted code;

<!-- EOF -->
