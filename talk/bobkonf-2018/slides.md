% Testing monadic programs using QuickCheck and state machine based models
% Stevan Andjelkovic
% 2018.2.23, BOBKonf (Berlin)

# Introduction

* Property based testing in general
* How to apply property based testing to stateful programs
* Running example, simple CRUD web application
    - Familiar type of program
    - Obviously stateful
    - Non-obvious property?
* Using the
  [`quickcheck-state-machine`](https://github.com/advancedtelematic/quickcheck-state-machine)
  library

---

# Overview

* Reminder
    - What are property based tests?
    - Why are they so effective?
* Basic idea and motivation behind how the library applies property based
  testing principles to stateful programs
* Demo, sequential property
* How we can get concurrent tests (catch race conditions) for free via
  linearisation
* Demo, concurrent property
* Comparison to other tools

---

# Property based testing

* Unit tests

```haskell
      test :: Bool
      test = reverse (reverse [1,2,3]) == [1,2,3]

```

* Property based tests

```haskell
      prop :: [Int] -> Bool
      prop xs = reverse (reverse xs) == xs
```

. . .

* Proof by (structural) induction

      $\quad\;\forall xs(\textsf{reverse}(\textsf{reverse}(xs)) = xs)$
      
. . .

* Type theory

```haskell
      proof : forall xs -> reverse (reverse xs) == xs
```

---

# Stateful programs, basic idea / motivation

* Obvious idea, that doesn't work so well: proof by induction modulo
  monad laws

* A much more successful approach is to take inspiration from physics
    - Simplified model of reality that can predict what will happen
    - Experiments against reality validate the model

* How do we model algorithms/programs?

    - Turing's machines/thesis: too "low level", because Turing was
      concerned about functions on natural numbers (not arbitrary algorithms)

    - Gurevich's abstract state machines/new thesis, think of finite
      state machines were the states are arbitrary datatypes

# The `quickcheck-state-machine` library

* Use abstract state machine to model the program
    - A model datatype, and an initial model
    - A datatype of actions (things that can be happen)
    - A transition function that given an action advances the model to the
      next state

* Use pre- and post-conditions on the model to enforce invariants

* Use QuickCheck's generation to conduct experiments that validate the
  model

* Abstract state machines are also used by:

    - Quiviq's closed source version of QuickCheck for Erlang (Volvo
      cars, Ericsson, ...)

    - Z/B/Event-B familiy (Paris metro line 14)

    - TLA+ (AWS, XBox)

    - Jepsen (Kafka, Cassandra, Zookeeper, ...)

# The properties / experiments

* Sequential property

    - Generate list of actions, such that all actions' pre-condition holds
    - For each action starting with the inital model
        - Run the action against the real system
        - Ensure that the post-condition for the action holds
        - Advanced the model using the transition function

* Parallel/concurrent property

     - Generate two lists of actions (one per thread)
  
     - Run the actions concurrently against the system, and gather a trace
       of invocations and responses for each action
  

     - Try to find a possible sequential interleaving of action
       invocations and responses that respects the post-conditions (cf.
       linearisation by Herlihy and Wing, 1987)

# Demo

* Simple web application
    - `data User { name :: Text, age :: Int }`
    - Create user (post request)
    - Read/lookup user (get request)
    - Update age (put request)
    - Delete user (delete request)

* Implementation 
    - Servant and persistant
    - Could be written using any libraries or language
    - Completely independent of `quickcheck-state-machine`
    
* Specification

    - Uses the `quickcheck-state-machine` library in the way described
      above

# Comparison to other tools

* Quiviq's Erlang QuickCheck

* Z/B/Event-B

* TLA+

* Jepsen

# Conclusion

 
