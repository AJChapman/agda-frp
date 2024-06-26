# Work In Progress -- Agda Functional Reactive Programming (FRP)

This is my attempt at porting the system described in [Conal Elliot's Push-Pull Functional Reactive Programming](http://conal.net/papers/push-pull-frp/push-pull-frp.pdf) to [Agda](https://agda.readthedocs.io/en/latest/getting-started/what-is-agda.html).

The aim is to:

1. Describe a specification of FRP -- a simple and precise semantics for programming with:
    * Time-varying values (Behaviors),
    * Events, and
    * The interactions between Behaviors and Events.
2. Define an efficient implementation of this, and
3. Prove that the implementation is faithful to the specification by defining homomorphisms from implementation to specification.

## Dependencies

* [Agda](https://agda.readthedocs.io/en/latest/getting-started/what-is-agda.html) 2.6.4.3 (other versions may also work)
* [agda-stdlib](https://github.com/Agda/agda-stdlib) 2.0
* [felix](https://github.com/conal/felix)

To check that everything works, run `agda index.agda`.
If it gives no output then all is well!

## Reading the Code

The Agda source code is in [./src/FRP](./src/FRP).

### Time

First we define time.
We don't choose a concrete underlying type for time, but we do define constraints on it -- it must be decidably totally ordered, and it must be a group (i.e. informally, it must have +, - and 0).
Most modules are parameterised by this type, so a user of agda-frp as a library would need to define this, and create an object of type [DecOrderedGroup](./src/FRP/Time/DecOrderedGroup.agda).

We extend the underlying type by adding `-∞` and `∞` so that we can have time values which occur before or after any others, e.g. Events that are guaranteed to already have occurred.
This is done in [Time/T+.agda](./src/FRP/Time/T+.agda).

It is all tied together in [Time.agda](./src/FRP/Time.agda).
After importing this you will have the type `T` available as the underlying time type, with the convention of a `ₜ` (subscript 't') suffix on operators and properties, etc. E.g. compare values of type `T` with `≤ₜ`.
You will also have the type `T̂`, which extends `T` with `-∞` and `∞`.
This uses a `ᵗ` (superscript `t`) suffix.

### Semantics

The semantics, or specification, is in [./src/FRP/Semantics](./src/FRP/Semantics).
Here we have:

* [Semantics/Behavior.agda](./src/FRP/Semantics/Behavior.agda) for importing `Behavior` -- time-varying values
* [Semantics/Behavior/Type.agda](./src/FRP/Semantics/Behavior/Type.agda) the type and basic operators
* [Semantics/Behavior/Raw.agda](./src/FRP/Semantics/Behavior/Raw.agda) raw instances for e.g. functor and applicative.
* [Semantics/Behavior/Laws.agda](./src/FRP/Semantics/Behavior/Laws.agda) proofs that the raw instances behave the relevant laws.
* [Semantics/Future.agda](./src/FRP/Semantics/Future.agda) `Future` -- pairs of time (`T̂`) and value for use in `Event`s. We can map over either the time or the value, and sort by time (suffix `ᵗ,`).
* [Semantics/Event.agda](./src/FRP/Semantics/Event.agda) for importing `Event`.
* [Semantics/Event/Type.agda](./src/FRP/Semantics/Event/Type.agda) the type and basic operations (`merge`, `map`, `<$>`, etc.)
* [Semantics/Event/Raw.agda](./src/FRP/Semantics/Event/Raw.agda) raw instances for e.g. monoid and functor.
* [Semantics/Event/Laws.agda](./src/FRP/Semantics/Event/Laws.agda) proofs that operations on an event maintain the sorting of the occurrences of the event.

### Implementation

The implementation implements the specification in a more efficient way, or at least will one day.
At this stage the implementation is identical to the specification, but also has functions to map to the specification and proofs that these mappings are homomorphisms.

* [Implementation/Behavior.agda](./src/FRP/Implementation/Behavior.agda) as in `Semantics`, but adds timeᵇ, a behavior that returns the current time
* [Implementation/Behavior/Type.agda](./src/FRP/Implementation/Behavior/Type.agda) as in `Semantics`, but adds `at` to map from implementation `Behavior` to semantic `Behavior`.
* [Iķplementation/Behavior/Raw.agda](./src/FRP/Iķplementation/Behavior/Raw.agda) functor, applicative.
* [Implementation/Behavior/Laws.agda](./src/FRP/Implementation/Behavior/Laws.agda) proofs that `at` is a functor morphism and an applicative morphism.
* [Implementation/Event.agda](./src/FRP/Implementation/Event.agda)
* [Implementation/Event/Type.agda](./src/FRP/Implementation/Event/Type.agda) as in `Semantics`, but with `occs` (short for 'occurrences') to map from implementation `Event` to semantic `Event`.
* [Implementation/Event/Raw.agda](./src/FRP/Implementation/Event/Raw.agda) Monoid and Functor; Applicative and Monad still to do.
* [Implementation/Event/Laws.agda](./src/FRP/Implementation/Event/Laws.agda) proofs that `occs` is a Monoid and Functor morphism.

## Work in Progress

Things I haven't figured out yet:

* Should `Future` be under `Time` rather than under `Semantics`?
* Is there any point using Felix, e.g. I have defined a `Category` instance for `Behavior`, and it's lawful, but is it any use?
* Should we use absolute or relative semantics for Event times?
  Conal's paper uses absolute, but mentions the possibility of relative in a couple of places.
  Relative may make some things simpler, such as the `pure` Event simply having time `0`, instead of `-∞`, and `join` not needing to change the times of sub-events.

Still to do:

* Efficient implementations as per the paper.
  They are currently simply copies of the specification.
