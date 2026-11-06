// Credit: The primary-backup example is from Manos' lecture (Ch.6), and some
// boilerplate is adapted from Manos' in-class demo (Ch.6)
include "UtilitiesLibrary.dfy"

// A primary-backup register.
//
// A register stores one integer, initially 0. Clients can write a new value
// and read the current value. The outside world sees only these events:
//   * Write(value): the register now holds `value`.
//   * Read(value): a client reads the register and gets `value`.
//
// The register is replicated on two hosts, a primary and a backup, so that it
// survives a crash of the primary. They communicate over a network in which a
// message that has been sent can be received later, at most once.
//   * While the primary is alive, clients talk only to the primary. To write
//     a value, the primary sends the value to the backup in an Update message,
//     the backup applies it and sends back an Ack message, and only then does
//     the primary update its own value and reply to the client. The primary
//     handles one write at a time, and it does not answer reads while a write
//     is in progress.
//   * At some point, the primary may crash. Then the backup takes over as the
//     new primary, and clients talk to it instead. There is no backup anymore.
//
// The crash is modeled by the Failover step in the DistributedSystem module.
// It is not part of the protocol, and it is given to you.
//
// Your task:
//   * Part 1: Fill in the steps of the primary and of the backup, following the
//     comment above each step. The comment also says which event each step
//     produces.
//   * Part 2: Prove that the distributed system refines the spec: write the
//     abstraction function and an invariant, and prove RefinementInit and
//     RefinementNext.
//
// Optional, if you finish early: in lecture, the write takes effect when the
// backup has it. Check this in Dafny: move the Write event from ApplyUpdate to
// CompleteWrite, and see what fails in your proof.

module Events {
    datatype Event =
        | Write(value: int)
        | Read(value: int)
        | NoOp
}

// The spec: a single register.
module Spec {
    import opened Events

    datatype Constants = Constants()

    datatype Variables = Variables(value: int)

    ghost predicate Init(c: Constants, v: Variables)
    {
        v.value == 0
    }

    ghost predicate WriteValue(c: Constants, v: Variables, v': Variables, value: int)
    {
        v'.value == value
    }

    ghost predicate ReadValue(c: Constants, v: Variables, v': Variables, value: int)
    {
        && value == v.value
        && v' == v
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Event)
    {
        match evt
            case Write(value) => WriteValue(c, v, v', value)
            case Read(value) => ReadValue(c, v, v', value)
            case NoOp => v' == v
    }
}

module Types {
    import opened UtilitiesLibrary

    datatype Message =
        | Update(value: int)
        | Ack(value: int)

    datatype MessageOps = MessageOps(recv: Option<Message>, send: Option<Message>)
}

// ---------------------------------------------------------------------------
// Part 1: The primary and the backup
// ---------------------------------------------------------------------------

module Primary {
    import opened UtilitiesLibrary
    import opened Events
    import opened Types

    datatype Constants = Constants()

    // isAlive: whether the primary is still running. A primary that is not
    //          alive takes no steps.
    // value: the value of the register at the primary
    // pending: the write in progress, if there is one
    datatype Variables = Variables(isAlive: bool, value: int, pending: Option<int>)

    ghost predicate Init(c: Constants, v: Variables)
    {
        && v.isAlive
        && v.value == 0
        && v.pending.None?
    }

    // A client asks to write `value`. If no write is in progress, the primary
    // starts this write: it sends `value` to the backup in an Update message,
    // and receives no message. It does not change its own value yet. Event:
    // NoOp.
    ghost predicate BeginWrite(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps, value: int)
    {
        true
    }

    // The primary receives the Ack message for the write in progress. It
    // updates its own value, the write is no longer in progress, and the
    // primary replies to the client. It sends no message. Event: NoOp.
    ghost predicate CompleteWrite(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps)
    {
        true
    }

    // A client reads the register. If no write is in progress, the primary
    // answers with its own value. It sends and receives no message. Event:
    // Read(value), with the primary's value.
    ghost predicate ServeRead(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps)
    {
        true
    }

    datatype Step =
        | BeginWriteStep(value: int)
        | CompleteWriteStep()
        | ServeReadStep()

    ghost predicate NextStep(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps, step: Step)
    {
        match step
            case BeginWriteStep(value) => BeginWrite(c, v, v', evt, msgOps, value)
            case CompleteWriteStep => CompleteWrite(c, v, v', evt, msgOps)
            case ServeReadStep => ServeRead(c, v, v', evt, msgOps)
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps)
    {
        exists step :: NextStep(c, v, v', evt, msgOps, step)
    }
}

module Backup {
    import opened UtilitiesLibrary
    import opened Events
    import opened Types

    datatype Constants = Constants()

    // isPrimary: whether the backup has taken over as the new primary
    // value: the value of the register at the backup
    datatype Variables = Variables(isPrimary: bool, value: int)

    ghost predicate Init(c: Constants, v: Variables)
    {
        && !v.isPrimary
        && v.value == 0
    }

    // While the backup is not the primary:
    // The backup receives an Update message, sets its value to the value in
    // the message, and sends an Ack message with the same value back to the
    // primary. This is the step where the write takes effect. Event:
    // Write(value), with the value in the message.
    ghost predicate ApplyUpdate(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps)
    {
        true
    }

    // After the backup has taken over as the primary:
    // A client asks to write `value`. There is no backup anymore, so the new
    // primary sets its value right away. It sends and receives no message.
    // Event: Write(value).
    ghost predicate WriteAsPrimary(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps, value: int)
    {
        true
    }

    // After the backup has taken over as the primary:
    // A client reads the register, and the new primary answers with its value.
    // It sends and receives no message. Event: Read(value), with the new
    // primary's value.
    ghost predicate ServeRead(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps)
    {
        true
    }

    datatype Step =
        | ApplyUpdateStep()
        | WriteAsPrimaryStep(value: int)
        | ServeReadStep()

    ghost predicate NextStep(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps, step: Step)
    {
        match step
            case ApplyUpdateStep => ApplyUpdate(c, v, v', evt, msgOps)
            case WriteAsPrimaryStep(value) => WriteAsPrimary(c, v, v', evt, msgOps, value)
            case ServeReadStep => ServeRead(c, v, v', evt, msgOps)
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps)
    {
        exists step :: NextStep(c, v, v', evt, msgOps, step)
    }
}

// A message that has been sent can be received later, at most once. A message
// cannot be sent again while a copy of it is still in the network.
module Network {
    import opened UtilitiesLibrary
    import opened Types

    datatype Constants = Constants()

    datatype Variables = Variables(inFlightMessages: set<Message>)

    ghost predicate Init(c: Constants, v: Variables)
    {
        v.inFlightMessages == {}
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
    {
        && (msgOps.recv.Some? ==> msgOps.recv.value in v.inFlightMessages)
        && (msgOps.send.Some? ==> msgOps.send.value !in v.inFlightMessages)
        && v'.inFlightMessages ==
            v.inFlightMessages
                - (if msgOps.recv.None? then {} else {msgOps.recv.value})
                + (if msgOps.send.None? then {} else {msgOps.send.value})
    }
}

module DistributedSystem {
    import opened Events
    import opened Types
    import Network
    import Primary
    import Backup

    datatype Constants = Constants(
        primary: Primary.Constants,
        backup: Backup.Constants,
        network: Network.Constants
    )

    datatype Variables = Variables(
        primary: Primary.Variables,
        backup: Backup.Variables,
        network: Network.Variables
    )

    ghost predicate Init(c: Constants, v: Variables)
    {
        && Primary.Init(c.primary, v.primary)
        && Backup.Init(c.backup, v.backup)
        && Network.Init(c.network, v.network)
    }

    // The primary takes a step, and the backup stays the same.
    ghost predicate PrimaryAction(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps)
    {
        && Primary.Next(c.primary, v.primary, v'.primary, evt, msgOps)
        && v'.backup == v.backup
    }

    // The backup takes a step, and the primary stays the same.
    ghost predicate BackupAction(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps)
    {
        && Backup.Next(c.backup, v.backup, v'.backup, evt, msgOps)
        && v'.primary == v.primary
    }

    // The primary crashes, and the backup takes over as the new primary.
    // This step is not part of the protocol. It models the environment: a
    // crash, and a perfect failure detector that tells the backup right away.
    // It is the only step that changes two hosts at once.
    ghost predicate Failover(c: Constants, v: Variables, v': Variables, evt: Event)
    {
        && v.primary.isAlive
        && !v.backup.isPrimary
        && v'.primary == v.primary.(isAlive := false)
        && v'.backup == v.backup.(isPrimary := true)
        && v'.network == v.network
        && evt == NoOp
    }

    datatype Step =
        | PrimaryStep(msgOps: MessageOps)
        | BackupStep(msgOps: MessageOps)
        | FailoverStep()

    ghost predicate NextStep(c: Constants, v: Variables, v': Variables, evt: Event, step: Step)
    {
        match step
            case PrimaryStep(msgOps) =>
                && PrimaryAction(c, v, v', evt, msgOps)
                && Network.Next(c.network, v.network, v'.network, msgOps)
            case BackupStep(msgOps) =>
                && BackupAction(c, v, v', evt, msgOps)
                && Network.Next(c.network, v.network, v'.network, msgOps)
            case FailoverStep => Failover(c, v, v', evt)
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Event)
    {
        exists step :: NextStep(c, v, v', evt, step)
    }
}

// ---------------------------------------------------------------------------
// Part 2: Refinement
// ---------------------------------------------------------------------------

// The refinement obligation. This module is given to you.
abstract module RefinementTheorem {
    import opened Events
    import Spec
    import DistributedSystem

    ghost function ConstantsAbstraction(c: DistributedSystem.Constants): Spec.Constants

    ghost function VariablesAbstraction(c: DistributedSystem.Constants, v: DistributedSystem.Variables): Spec.Variables

    ghost predicate Inv(c: DistributedSystem.Constants, v: DistributedSystem.Variables)

    lemma RefinementInit(c: DistributedSystem.Constants, v: DistributedSystem.Variables)
        requires DistributedSystem.Init(c, v)
        ensures Inv(c, v)
        ensures Spec.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))

    lemma RefinementNext(c: DistributedSystem.Constants, v: DistributedSystem.Variables, v': DistributedSystem.Variables, evt: Event)
        requires DistributedSystem.Next(c, v, v', evt)
        requires Inv(c, v)
        ensures Inv(c, v')
        ensures Spec.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), evt)
}

// The RefinementProof module refines the abstract RefinementTheorem module: it
// inherits all its functions and lemmas, along with their pre- and
// postconditions. Below, we repeat the inherited conditions as comments for
// reference.
module RefinementProof refines RefinementTheorem {
    import opened UtilitiesLibrary
    import opened Types
    import Primary
    import Backup

    ghost function ConstantsAbstraction(c: DistributedSystem.Constants): Spec.Constants
    {
        Spec.Constants()
    }

    // The abstraction function: the value of the register that the state of
    // the distributed system stands for.
    ghost function VariablesAbstraction(c: DistributedSystem.Constants, v: DistributedSystem.Variables): Spec.Variables
    {
        Spec.Variables(0)
    }

    ghost predicate Inv(c: DistributedSystem.Constants, v: DistributedSystem.Variables)
    {
        true
    }

    lemma RefinementInit(c: DistributedSystem.Constants, v: DistributedSystem.Variables)
    //  requires DistributedSystem.Init(c, v)
    //  ensures Inv(c, v)
    //  ensures Spec.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))
    {
    }

    lemma RefinementNext(c: DistributedSystem.Constants, v: DistributedSystem.Variables, v': DistributedSystem.Variables, evt: Event)
    //  requires DistributedSystem.Next(c, v, v', evt)
    //  requires Inv(c, v)
    //  ensures Inv(c, v')
    //  ensures Spec.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), evt)
    {
    }
}
