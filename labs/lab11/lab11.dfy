// Credit: The distributed multiset is adapted from Ivan Wei's Lab 10 (Fall 2025),
// and some boilerplate is adapted from Manos' in-class demo (Ch.6)
include "UtilitiesLibrary.dfy"

// A distributed multiset.
//
// A multiset is like a set, except that an item can appear more than once.
// Initially, the multiset is empty. The outside world sees only these events:
//   * Insert(item): one copy of `item` is added.
//   * Remove(item): one copy of `item` is removed. This can happen only when
//     `item` is in the multiset.
//
// The multiset is spread over several hosts. Each host keeps its own multiset
// of items, initially empty.
//   * A host can insert an item into its own multiset, or remove an item that
//     it has.
//   * A host can also send one of its items to another host. The item leaves
//     the sender and waits in the inbox of the destination host, until that
//     host receives it and adds it to its own multiset.
// The network keeps one inbox per host. Each inbox is a multiset of items, so
// the same item can wait in an inbox more than once.
//
// Your task:
//   * Part 1: Fill in the steps of the host, following the comment above each
//     step. Decide which event each step produces.
//   * Part 2: Prove that the distributed system refines the spec: write the
//     abstraction function and an invariant, and prove RefinementInit and
//     RefinementNext. Define additional functions and lemmas as needed.

module Events {
    datatype Event =
        | Insert(item: int)
        | Remove(item: int)
        | NoOp
}

// The spec: a single multiset.
module Spec {
    import opened Events

    datatype Constants = Constants()

    datatype Variables = Variables(items: multiset<int>)

    ghost predicate Init(c: Constants, v: Variables)
    {
        v.items == multiset{}
    }

    ghost predicate InsertItem(c: Constants, v: Variables, v': Variables, item: int)
    {
        v'.items == v.items + multiset{item}
    }

    ghost predicate RemoveItem(c: Constants, v: Variables, v': Variables, item: int)
    {
        && item in v.items
        && v'.items == v.items - multiset{item}
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Event)
    {
        match evt
            case Insert(item) => InsertItem(c, v, v', item)
            case Remove(item) => RemoveItem(c, v, v', item)
            case NoOp => v' == v
    }
}

module Types {
    import opened UtilitiesLibrary

    type HostId = nat

    // An item on its way to the host `dest`.
    datatype Message = Transfer(item: int, dest: HostId)

    datatype MessageOps = MessageOps(recv: Option<Message>, send: Option<Message>)
}

// The network keeps one inbox per host. Sending Transfer(item, dest) adds one
// copy of `item` to the inbox of `dest`. Receiving Transfer(item, dest) takes
// one copy of `item` out of the inbox of `dest`.
module Network {
    import opened UtilitiesLibrary
    import opened Types

    datatype Constants = Constants(numHosts: nat)

    datatype Variables = Variables(inboxes: seq<multiset<int>>)

    ghost predicate Init(c: Constants, v: Variables)
    {
        && |v.inboxes| == c.numHosts
        && (forall id | 0 <= id < |v.inboxes| :: v.inboxes[id] == multiset{})
    }

    ghost function AfterRecv(inboxes: seq<multiset<int>>, recv: Option<Message>): seq<multiset<int>>
        requires recv.Some? ==> recv.value.dest < |inboxes|
    {
        if recv.None? then inboxes
        else inboxes[recv.value.dest := inboxes[recv.value.dest] - multiset{recv.value.item}]
    }

    ghost function AfterSend(inboxes: seq<multiset<int>>, send: Option<Message>): seq<multiset<int>>
        requires send.Some? ==> send.value.dest < |inboxes|
    {
        if send.None? then inboxes
        else inboxes[send.value.dest := inboxes[send.value.dest] + multiset{send.value.item}]
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
    {
        && |v.inboxes| == c.numHosts
        // Only allow receiving an item that is in the inbox of its destination.
        && (msgOps.recv.Some? ==>
                && msgOps.recv.value.dest < |v.inboxes|
                && msgOps.recv.value.item in v.inboxes[msgOps.recv.value.dest])
        // Only allow sending to a host that exists.
        && (msgOps.send.Some? ==> msgOps.send.value.dest < |v.inboxes|)
        && v'.inboxes == AfterSend(AfterRecv(v.inboxes, msgOps.recv), msgOps.send)
    }
}

// ---------------------------------------------------------------------------
// Part 1: The host
// ---------------------------------------------------------------------------

module Host {
    import opened UtilitiesLibrary
    import opened Events
    import opened Types

    datatype Constants = Constants(numHosts: nat, myId: HostId)

    // items: the multiset of items that this host has
    datatype Variables = Variables(items: multiset<int>)

    ghost predicate Init(c: Constants, v: Variables)
    {
        v.items == multiset{}
    }

    // The host adds one copy of `item` to its items. It sends and receives no
    // message.
    ghost predicate LocalInsert(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps, item: int)
    {
        true
    }

    // If `item` is in its items, the host removes one copy of it. It sends and
    // receives no message.
    ghost predicate LocalRemove(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps, item: int)
    {
        true
    }

    // If `item` is in its items and `dest` is the id of another host, the host
    // removes one copy of `item` from its items and sends it to `dest` in a
    // Transfer message. It receives no message.
    ghost predicate SendItem(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps, item: int, dest: HostId)
    {
        true
    }

    // The host receives a Transfer message whose destination is this host, and
    // adds one copy of the item in the message to its items. It sends no
    // message.
    ghost predicate ReceiveItem(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps)
    {
        true
    }

    datatype Step =
        | LocalInsertStep(item: int)
        | LocalRemoveStep(item: int)
        | SendItemStep(item: int, dest: HostId)
        | ReceiveItemStep()

    ghost predicate NextStep(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps, step: Step)
    {
        match step
            case LocalInsertStep(item) => LocalInsert(c, v, v', evt, msgOps, item)
            case LocalRemoveStep(item) => LocalRemove(c, v, v', evt, msgOps, item)
            case SendItemStep(item, dest) => SendItem(c, v, v', evt, msgOps, item, dest)
            case ReceiveItemStep => ReceiveItem(c, v, v', evt, msgOps)
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps)
    {
        exists step :: NextStep(c, v, v', evt, msgOps, step)
    }
}

module DistributedSystem {
    import opened Events
    import opened Types
    import Network
    import Host

    datatype Constants = Constants(
        hosts: seq<Host.Constants>,
        network: Network.Constants
    )
    {
        ghost predicate WF()
        {
            // Every host and the network agree on the number of hosts, and
            // every host knows its own id.
            && network.numHosts == |hosts|
            && (forall id: HostId | ValidHostId(id) :: hosts[id].numHosts == |hosts| && hosts[id].myId == id)
        }

        ghost predicate ValidHostId(id: HostId)
        {
            id < |hosts|
        }
    }

    datatype Variables = Variables(
        hosts: seq<Host.Variables>,
        network: Network.Variables
    )
    {
        ghost predicate WF(c: Constants)
        {
            && c.WF()
            && |hosts| == |c.hosts|
        }
    }

    ghost predicate Init(c: Constants, v: Variables)
    {
        && v.WF(c)
        && (forall id: HostId | c.ValidHostId(id) :: Host.Init(c.hosts[id], v.hosts[id]))
        && Network.Init(c.network, v.network)
    }

    // Host `hostid` takes a step, and every other host stays the same.
    ghost predicate HostAction(c: Constants, v: Variables, v': Variables, evt: Event, hostid: HostId, msgOps: MessageOps)
    {
        && v.WF(c)
        && v'.WF(c)
        && c.ValidHostId(hostid)
        && Host.Next(c.hosts[hostid], v.hosts[hostid], v'.hosts[hostid], evt, msgOps)
        && (forall other: HostId | c.ValidHostId(other) && other != hostid :: v'.hosts[other] == v.hosts[other])
    }

    datatype Step =
        | HostActionStep(hostid: HostId, msgOps: MessageOps)

    ghost predicate NextStep(c: Constants, v: Variables, v': Variables, evt: Event, step: Step)
    {
        && HostAction(c, v, v', evt, step.hostid, step.msgOps)
        // The network agrees on what is received and records what is sent
        && Network.Next(c.network, v.network, v'.network, step.msgOps)
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
        requires c.WF()

    ghost function VariablesAbstraction(c: DistributedSystem.Constants, v: DistributedSystem.Variables): Spec.Variables
        requires v.WF(c)

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
    import Host
    import Network

    ghost function ConstantsAbstraction(c: DistributedSystem.Constants): Spec.Constants
    //  requires c.WF()
    {
        Spec.Constants()
    }

    // The abstraction function: the multiset that the state of the distributed
    // system stands for.
    ghost function VariablesAbstraction(c: DistributedSystem.Constants, v: DistributedSystem.Variables): Spec.Variables
    //  requires v.WF(c)
    {
        Spec.Variables(multiset{})
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
