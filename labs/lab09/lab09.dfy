// Credit: The lock service example is from Manos' lecture (Ch.6)
include "UtilitiesLibrary.dfy"

// World-visible events.
//
// A lock service is used by several clients, each with its own id. The
// outside world does not see the inside of the lock service. It only sees
// these events:
//   * Acquire(clientId): the client gets the lock. This can happen only when
//     no client holds the lock.
//   * Release(clientId): the client gives the lock back. This can happen only
//     when this client holds the lock.
// Initially, no client holds the lock.
//
// Your task:
//   * Part 1: Write the spec of the lock service: a state machine in which
//     each step is labeled by an event.
//   * Part 2: Decide which of the behaviors from lecture the spec accepts, and
//     prove it.
//   * Part 3 (preview of next week): A lock server implements the lock
//     service. Write a function that maps each state of the lock server to the
//     spec state it stands for.

module Events {
    // NoOp labels a step that the outside world does not see.
    datatype Event = Acquire(clientId: nat) | Release(clientId: nat) | NoOp
}

// ---------------------------------------------------------------------------
// Part 1: The spec
// ---------------------------------------------------------------------------

module Spec {
    import opened UtilitiesLibrary
    import opened Events

    datatype Constants = Constants()

    datatype Variables = Variables()

    ghost predicate Init(c: Constants, v: Variables)
    {
        true
    }

    // The client `clientId` gets the lock.
    ghost predicate AcquireLock(c: Constants, v: Variables, v': Variables, clientId: nat)
    {
        true
    }

    // The client `clientId` gives the lock back.
    ghost predicate ReleaseLock(c: Constants, v: Variables, v': Variables, clientId: nat)
    {
        true
    }

    // A step of the spec labeled by the event `evt`. A NoOp step does not
    // change the state.
    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Event)
    {
        true
    }
}

// ---------------------------------------------------------------------------
// Part 2: Which behaviors are correct?
// ---------------------------------------------------------------------------

module Behaviors {
    import opened UtilitiesLibrary
    import opened Events
    import opened Spec

    // A behavior is a sequence of events. The spec accepts a behavior if there
    // is a sequence of states such that the first state is an initial state,
    // and each event labels a step of the spec from one state to the next.
    ghost predicate Accepts(c: Constants, states: seq<Variables>, events: seq<Event>)
    {
        && |states| == |events| + 1
        && Init(c, states[0])
        && (forall i | 0 <= i < |events| :: Next(c, states[i], states[i + 1], events[i]))
    }

    // The behaviors from lecture.
    ghost function Behavior1(): seq<Event>
    {
        [Acquire(1), Acquire(1), Release(1), Release(1)]
    }

    ghost function Behavior2(): seq<Event>
    {
        [Release(2), Acquire(1), Release(1)]
    }

    ghost function Behavior3(): seq<Event>
    {
        [Acquire(1), Release(1), Acquire(2)]
    }

    // For each behavior, decide whether the spec accepts it, and write a lemma
    // that proves your answer:
    //   * If the spec accepts the behavior, prove that some sequence of states
    //     works, for example:
    //         ensures exists states :: Accepts(c, states, Behavior1())
    //   * If the spec does not accept the behavior, prove that no sequence of
    //     states works, for example, with `states` as a parameter:
    //         ensures !Accepts(c, states, Behavior1())



}

// ---------------------------------------------------------------------------
// Part 3 (preview of next week): Refinement
// ---------------------------------------------------------------------------

// A lock server that implements the lock service. Its steps are labeled by
// the same events as the spec. This module is given to you.
module LockServer {
    import opened Events

    datatype Constants = Constants()

    // locked: whether some client holds the lock
    // owner: the client that the lock was most recently given to
    // waiting: the clients that have asked for the lock
    datatype Variables = Variables(locked: bool, owner: nat, waiting: set<nat>)

    ghost predicate Init(c: Constants, v: Variables)
    {
        && !v.locked
        && v.waiting == {}
    }

    // The client `clientId` asks for the lock.
    ghost predicate RequestLock(c: Constants, v: Variables, v': Variables, evt: Event, clientId: nat)
    {
        && v' == v.(waiting := v.waiting + {clientId})
        && evt == NoOp
    }

    // The server gives the lock to a waiting client.
    ghost predicate GrantLock(c: Constants, v: Variables, v': Variables, evt: Event, clientId: nat)
    {
        && !v.locked
        && clientId in v.waiting
        && v' == v.(locked := true, owner := clientId, waiting := v.waiting - {clientId})
        && evt == Acquire(clientId)
    }

    // The client that holds the lock gives it back.
    ghost predicate ReturnLock(c: Constants, v: Variables, v': Variables, evt: Event, clientId: nat)
    {
        && v.locked
        && v.owner == clientId
        && v' == v.(locked := false)
        && evt == Release(clientId)
    }

    datatype Step =
        | RequestStep(clientId: nat)
        | GrantStep(clientId: nat)
        | ReturnStep(clientId: nat)

    ghost predicate NextStep(c: Constants, v: Variables, v': Variables, evt: Event, step: Step)
    {
        match step
            case RequestStep(clientId) => RequestLock(c, v, v', evt, clientId)
            case GrantStep(clientId) => GrantLock(c, v, v', evt, clientId)
            case ReturnStep(clientId) => ReturnLock(c, v, v', evt, clientId)
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Event)
    {
        exists step :: NextStep(c, v, v', evt, step)
    }
}

module RefinementProof {
    import opened UtilitiesLibrary
    import opened Events
    import Spec
    import LockServer

    ghost function ConstantsAbstraction(c: LockServer.Constants): Spec.Constants
    {
        Spec.Constants()
    }

    // The abstraction function: the spec state that the lock server state `v`
    // stands for.
    ghost function VariablesAbstraction(c: LockServer.Constants, v: LockServer.Variables): Spec.Variables
    {
        Spec.Variables()
    }

    // Dafny checks your abstraction function with these two lemmas. You do not
    // need to write proofs for them.
    //   * RefinementInit: each initial state of the lock server stands for an
    //     initial state of the spec.
    //   * RefinementNext: each step of the lock server stands for a step of the
    //     spec with the same event, or it is a "stutter" step: the event is
    //     NoOp, and the spec state does not change.
    //
    // Think about it: which steps of the lock server are stutter steps?

    lemma RefinementInit(c: LockServer.Constants, v: LockServer.Variables)
        requires LockServer.Init(c, v)
        ensures Spec.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))
    {
    }

    lemma RefinementNext(c: LockServer.Constants, v: LockServer.Variables, v': LockServer.Variables, evt: Event)
        requires LockServer.Next(c, v, v', evt)
        ensures
            || Spec.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), evt)
            || (VariablesAbstraction(c, v) == VariablesAbstraction(c, v') && evt == NoOp)
    {
    }
}
