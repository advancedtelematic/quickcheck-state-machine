
# Statistical testing of software

How does one effectively measure the quality of software?

In this talk I'll give a summary of how the literature on [Cleanroom Software
Engineering](https://en.wikipedia.org/wiki/Cleanroom_software_engineering)
([Harlan Mills](https://en.wikipedia.org/wiki/Harlan_mills) et al) and the
[Software Reliability
Engineering](https://en.wikipedia.org/wiki/Software_reliability_testing) ([John
Musa](https://doi.ieeecomputersociety.org/10.1109/MS.2009.132) et al) answer
this question.

The general principle, shared by both Mills' and Musa's approaches, consists of
four steps:

  1) Model the expected use of the software under test, i.e. what are the use
     cases and how often do they occur with relation to each other. This model
     is called a usage model or an operational profile, and is supposed to
     capture what realistic use of the software looks like;

  2) Use the usage model to generate test cases that correspond to realistic
     use;

  3) Use a test oracle to determine if the generated test cases passed or
     failed. A simple test oracle could for example check if the software under
     test crashes when we execute the generated test case;

  4) Statistically compute how reliable the software under test is based on the
     outcome of repeating step (2) and (3) some number of times.

I'll then show how one might go about implementing those steps using property
based testing and state machine modelling. Property based testing already has
machinery for generating random test cases which makes step (2) easy, and state
machine modelling gives us a way to define a test oracle that we need in step
(3). By doing some bookkeeping of test outcomes while running them, the
reliability can be computed at the end.

For example, if the reliability is say 90%, then that should be interpreted as:
if a user uses the system as specified by the usage model, then in 90% of the
cases the system will act according to the specification captured by the state
machine.

The demo I'll show will be using the Haskell library
[quickcheck-state-machine](https://github.com/advancedtelematic/quickcheck-state-machine)
which I've helped develop, but one could also use the Java program
[JUMBL](http://jumbl.sourceforge.net/jumblTop.html) developed by Mills'
collaborators.


## Key take-away points


1. The idea of modelling how the software will be used has several benefits:

     a) Priortising development work: frequently used parts of the program
        should be developed first. Pareto principle often applies, 20% of the
        use cases of the complete system supports 80% of the actual use of the
        system;

     b) Priortising testing work: frequently used parts of the program should be
        tested more often, because if those parts contain bugs they will
        manifest themselves often and lead to a bad user experience;

     c) Developing a usage model forces you to think from a user's perspective,
        a key principle of agile software development.

2. There's plenty of other ideas from statistics that can be applied to testing,
   for example:

     a) By modelling the use of the software as a Markov chain, we can get a lot
        of interesting statistics about the use of our software before even
        executing the tests. For example, expected test case length, which state
        we will spend most time in, average number of time until we reach some
        state, etc;

     b) Statistical testing can in a sound way account for flaky tests that are
        hard to avoid when developing complex systems.

     c) We can compute a stopping criteria, i.e. answer the question: when have
        we done enough testing?

3. The notion of reliability is used as a measure of quality in all other
   manufacturing processes. Take for example computer chip manufacturing, the
   way quality is measured there is by randomly sampling some of the
   manufactured chips and see if they meet the specification. Depending on how
   many pass this test we can statistically compute the reliability of the whole
   population. What Mills, Musa and et al argue is that we can do the same thing
   with software.
