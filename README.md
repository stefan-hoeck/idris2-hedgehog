# idris2-hedgehog
An Idris port of the [Haskell Hedgehog library](https://hackage.haskell.org/package/hedgehog),
a property-based testing library in the spirit of QuickCheck.

This is still work in progress but the core functionality is already
there and a [tutorial](src/Doc/Intro.md) is in the making.

## Features

  * Monadic random value generators with integrated shrinking.

  * Numeric ranges with well-defined scaling and shrinking
    behavior.

  * Colorized test output with pretty printing of value
    diffs in case of failed tests (right now, colorize output
    has to be enabled by setting environment variable
    `HEDGEHOG_COLOR="1"`).

  * Conveniently define generators for regular
    algebraic data types via their generic representations
    as sums of products
    ([see idris2-sop](https://github.com/stefan-hoeck/idris2-sop)).

  * Provably total core: While the Haskell library allows us
    to define (and consume) infinite shrink trees, this
    is not possible here due to the codata nature of the
    trees we use for shrinking.

  * Classify generated values and verify test coverage.

## Limitations (compared to the Haskell version)

  * No filtering of generators: In my experience, generators
    should create random values constructively. Filtering
    values makes it too easy to write generators, the combination
    of which fails most of the time.

  * `Gen` is not a monad transformer right now, therefore
    it cannot be combined with additional monadic effects.
    The main reason for this is
    that we use a `Cotree` codata type for shrinking, and it
    is hard to combine this with monadic effects in a
    provably total way.

  * No support for state machine testing (yet).

  * No automatic detection of properties in source files (yet).

  * No parallel test execution (yet).

## Differences compared to QuickCheck

There are two main differences: First, there is no `Arbitrary` interface
and therefore, generators have typically to be hand-written. However, using
a sums of products approach (tutorial yet to be added) makes
it very easy to write generators for regular algebraic data types.
Second, shrinking is integrated, which makes it very easy to write
generators with good shrinking behavior, especially when using
an applicative style for writing generators, in which case shrinking
is completely free
(see also [integrated vs manual shrinkig](https://www.well-typed.com/blog/2019/05/integrated-shrinking/)).

## Prerequisites

The latest release requires Idri2 version 0.4.0.
The latest commit has been built against Idris 2, version 0.4.0-68db9fe0f.

In addition, the following external dependencies are
required:

  * [elab-util](https://github.com/stefan-hoeck/idris2-elab-util)
  * [sop](https://github.com/stefan-hoeck/idris2-sop)
  * [pretty-show](https://github.com/stefan-hoeck/idris2-pretty-show)
