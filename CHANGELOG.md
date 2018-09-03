#### 0.4.2 (2018-9-3)

  * Fix bug that made tests fail on systems without docker;
  * Remove some unused dependencies found by the weeder tool.

#### 0.4.1 (2018-8-31)

  * Minor fixes release:

    - Fix broken link and code in README;
    - Disable web server tests when docker isn't available (issue #222).

#### 0.4.0 (2018-8-21)

  * Major rewrite, addressing many issues:

    - The output of sequential runs now shows a diff of how the model changed in
      each step (related to issue #77);

    - The datatype of actions was renamed to commands and no longer is a GADT
      (discussed in issue #170, also makes issue #196 obsolete);

    - Commands can now return multiple references (issue #197);

    - Global invariants can now more easily be expressed (issue #200);

    - Counterexamples are now printed when post-conditions fail (issue #172).

#### 0.3.1 (2018-1-15)

  * Remove upper bounds for dependencies, to easier keep up with
    Stackage nightly.

#### 0.3.0 (2017-12-15)

  * A propositional logic module was added to help provide better
    counterexamples when pre- and post-conditions don't hold;

  * Generation of parallel programs was improved (base on
    a [comment](https://github.com/Quviq/QuickCheckExamples/issues/2) by
    Hans Svensson about how Erlang QuickCheck does it);

  * Support for semantics that might fail was added;

  * Pretty printing of counterexamples was improved.

#### 0.2.0

  * Z-inspired definition of relations and associated operations were
    added to help defining concise and showable models;

  * Template Haskell derivation of `shrink` and type classes: `Show`,
    `Constructors`, `HFunctor`, `HFoldable`, `HTraversable`;

  * New and more flexible combinators for building sequential and
    parallel properties replaced the old clunky ones;

  * Circular buffer example was added;

  * Two examples of how to test CRUD web applications were added.

#### 0.1.0

  * The API was simplified, thanks to ideas stolen from
    [Hedgehog](https://github.com/hedgehogqa/haskell-hedgehog/commit/385c92f9dd0aa7e748fc677b2eeead5e3572685f).

#### 0.0.0

  * Initial release.
