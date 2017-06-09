## quickcheck-state-machine

[![Hackage](https://img.shields.io/hackage/v/quickcheck-state-machine.svg)](https://hackage.haskell.org/package/quickcheck-state-machine)
[![Build Status](https://api.travis-ci.org/advancedtelematic/quickcheck-state-machine.svg?branch=master)](https://travis-ci.org/advancedtelematic/quickcheck-state-machine)

`quickcheck-state-machine` is a Haskell library, based
on [QuickCheck](https://hackage.haskell.org/package/QuickCheck), for testing
stateful programs. The library is different from
the
[`Test.QuickCheck.Monadic`](https://hackage.haskell.org/package/QuickCheck/docs/Test-QuickCheck-Monadic.html) approach
in that it lets the user specify the correctness by means of a state machine
based model using pre- and post-conditions. The advantage of the state machine
approach is twofold: 1) specifying the correctness of your programs becomes less
adhoc, and 2) you get testing for race conditions for free.

The combination of state machine based model specification and property based
testing first appeard in Erlang's proprietary QuickCheck. The
`quickcheck-state-machine` library can be seen as an attempt to provide similar
functionality to Haskell's QuickCheck library.

### Sample run (teaser)

Here's a sample output from when we look for race conditions in the mutable
reference example:

```
> quickCheck (MutableReference.prop_parallel RaceCondition)
*** Failed! (after 5 tests and 6 shrinks):

Couldn't linearise:

┌──────────────────────┐
│ New                  │
│                 ⟶ $0 │
└──────────────────────┘
            │ ┌────────┐
            │ │ Inc $0 │
┌─────────┐ │ │        │
│ Inc $0  │ │ │        │
│         │ │ │   ⟶ () │
│         │ │ └────────┘
│    ⟶ () │ │
└─────────┘ │
┌─────────┐ │
│ Read $0 │ │
│     ⟶ 1 │ │
└─────────┘ │


```

Clearly, if we increment a mutable reference in parallel we can end up with a
race condition. We shall come back to this example below, but if your are
impatient you can find the full source
code
[here](https://github.com/advancedtelematic/quickcheck-state-machine/blob/master/example/src/MutableReference.hs).

### How it works

The rought idea is that the user of the library is asked to provide:

  * a datatype of commands;
  * a datatype model;
  * pre- and post-conditions of the commands on the model;
  * a state transition function that given a model and a command advances the
    model to its next state;
  * a way to generate and shrink commands;
  * semantics for executing the commands.

The library then gives back a sequential and a parallel property.

#### Sequential property

The *sequential property* checks if the model is consistent with respect to the
semantics. The way this is done is:

  1. generate a list of commands;

  2. starting from the initial model, for each command do the the following:

       1. check that the pre-condition holds;
       2. if so, execute the command using the semantics;
       3. check if the the post-condition holds;
       4. advance the model using the transition function.

  3. If something goes wrong, shrink the initial list of commands and present a
     minimal counter example.

#### Parallel property

The *parallel property* checks if parallel execution of the semantics can be
explained in terms of the sequential model. This is useful for trying to find
race conditions -- which normally can be tricky to test for. It works as
follows:

  1. generate a list of commands that will act as a sequential prefix for the
     parallel program (think of this as an initialisation bit that setups up
     some state);

  2. generate two lists of commands that will act as parallel suffixes;

  3. execute the prefix sequentially;

  4. execute the suffixes in parallel and gather the a trace (or history) of
     invocations and responses of each command;

  5. try to find a possible sequential interleaving of command invocations and
     responses that respects the post-conditions.

The last step basically tries to find
a [linearisation](https://en.wikipedia.org/wiki/Linearizability) of calls that
could have happend on a single thread.

### Examples

To get started it is perhaps easiest to have a look at one of the several
examples:

  * The water jug problem from *Die Hard 2* -- this is a
    simple
    [example](https://github.com/advancedtelematic/quickcheck-state-machine/blob/master/example/src/DieHard.hs) of
    a specification where we use the sequential property to find a solution
    (counter example) to a puzzle from an action movie. Note that this example
    has no meaningful semantics, we merely model-check. It might be helpful to
    compare the solution to the
    Hedgehog
    [solution](http://clrnd.com.ar/posts/2017-04-21-the-water-jug-problem-in-hedgehog.html) and
    the
    TLA+
    [solution](https://github.com/tlaplus/Examples/blob/master/specifications/DieHard/DieHard.tla);

  * The
    union-find
    [example](https://github.com/advancedtelematic/quickcheck-state-machine/blob/master/example/src/UnionFind.hs) --
    another use of the sequential property, this time with a useful semantics
    (imperative implementation of the union-find algorithm). It could be useful
    to compare the solution to the one that appears in the paper *Testing
    Monadic Code with
    QuickCheck* [[PS](http://www.cse.chalmers.se/~rjmh/Papers/QuickCheckST.ps)],
    which is
    the
    [`Test.QuickCheck.Monadic`](https://hackage.haskell.org/package/QuickCheck/docs/Test-QuickCheck-Monadic.html) module
    is based on;


  * Mutable
    reference
    [example](https://github.com/advancedtelematic/quickcheck-state-machine/blob/master/example/src/MutableReference.hs) --
    this is a bigger example that shows both how the sequential property can
    find normal bugs, and how the parallel property can find race conditions.
    Several metaproperties, that for example check if the counter examples are
    minimal, are specified in a
    separate
    [module](https://github.com/advancedtelematic/quickcheck-state-machine/blob/master/example/src/MutableReference/Prop.hs);

  * Ticket
    dispenser
    [example](https://github.com/advancedtelematic/quickcheck-state-machine/blob/master/example/src/TicketDispenser.hs) --
    a simple example where the parallel property is used once again to find a
    race condition. The semantics in this example uses a simple database file
    that needs to be setup and teared down. This example also appears in the
    *Testing a Database for Race Conditions with QuickCheck* and *Testing the
    Hard Stuff and Staying
    Sane*
    [[PDF](http://publications.lib.chalmers.se/records/fulltext/232550/local_232550.pdf),
    [video](https://www.youtube.com/watch?v=zi0rHwfiX1Q)] papers.

All examples have an associated `Spec` module located in
the
[`example/test`](https://github.com/advancedtelematic/quickcheck-state-machine/tree/master/example/test) directory.
These make use of the properties in the examples, and get tested as part
of
[Travis CI](https://travis-ci.org/advancedtelematic/quickcheck-state-machine).

To get a better feel for the examples it might be helpful to `git clone` this
repo, `cd` into the `example/` directory and fire up `stack ghci` and run the
different properties interactively.

### How to contribute

The `quickcheck-state-machine` library is still very experimental.

We would like to encourage users to try it out, and join the discussion of how
we can improve it on the issue tracker!

### See also

  * The QuickCheck
    bugtrack [issue](https://github.com/nick8325/quickcheck/issues/139) -- where
    the initial discussion about how how to add state machine based testing to
    QuickCheck started;

  * *Finding Race Conditions in Erlang with QuickCheck and
    PULSE*
    [[PDF](http://www.cse.chalmers.se/~nicsma/papers/finding-race-conditions.pdf),
    [video](https://vimeo.com/6638041)] -- this is the first paper to describe
    how Erlang's QuickCheck works (including the parallel testing);

  * *Linearizability: a correctness condition for concurrent
    objects* [[PDF](https://cs.brown.edu/~mph/HerlihyW90/p463-herlihy.pdf)], this
    is a classic paper that describes the main technique of the parallel
    property;

  * Aphyr's blogposts about [Jepsen](https://github.com/jepsen-io/jepsen), which
    also uses the linearisability technique, and has found bugs in many
    distributed systems:

    - [Knossos: Redis and linearizability](https://aphyr.com/posts/309-knossos-redis-and-linearizability)
    - [Strong consistency models](https://aphyr.com/posts/313-strong-consistency-models)
    - [Computational techniques in Knossos](https://aphyr.com/posts/314-computational-techniques-in-knossos)
    - [Serializability, linearizability, and locality](https://aphyr.com/posts/333-serializability-linearizability-and-locality)

  * The use of state machines to model and verify properties about programs is
    quite well-established, as witnessed by several books on the subject:

      - [Specifying Systems](https://www.microsoft.com/en-us/research/publication/specifying-systems-the-tla-language-and-tools-for-hardware-and-software-engineers/):
        The TLA+ Language and Tools for Hardware and Software Engineers
      - [Modeling in Event-B](http://www.event-b.org/abook.html): System and
        Software Engineering
      - [Abstract State Machines](http://www.di.unipi.it/~boerger/AsmBook/): A
        Method for High-Level System Design and Analysis

    The books contain general advice how to model systems using state machines,
    and are hence relevant to us. For shorter texts on why state machines are
    important for modeling, see:

      - Lamport's
        [*Computation and State Machines*](https://www.microsoft.com/en-us/research/publication/computation-state-machines/);

      - Gurevich's
        [*Evolving Algebras 1993: Lipari Guide*](https://www.microsoft.com/en-us/research/publication/103-evolving-algebras-1993-lipari-guide/) and
        *Sequential Abstract State Machines Capture Sequential
        Algorithms*
        [[PDF](http://delta-apache-vm.cs.tau.ac.il/~nachumd/models/gurevich.pdf)].

### License

BSD-style (see the file LICENSE).
