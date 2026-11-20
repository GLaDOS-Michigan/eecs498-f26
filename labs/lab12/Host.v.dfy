// The protocol of a host (from Lab 11). This file is untrusted: the Lab 11
// refinement proof shows that hosts following it refine the spec.
include "MultisetSystem.t.dfy"

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
        && msgOps == MessageOps(None, None)
        && v'.items == v.items + multiset{item}
        && evt == Insert(item)
    }

    // If `item` is in its items, the host removes one copy of it. It sends and
    // receives no message.
    ghost predicate LocalRemove(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps, item: int)
    {
        && item in v.items
        && msgOps == MessageOps(None, None)
        && v'.items == v.items - multiset{item}
        && evt == Remove(item)
    }

    // If `item` is in its items and `dest` is the id of another host, the host
    // removes one copy of `item` from its items and sends it to `dest` in a
    // Transfer message. It receives no message.
    ghost predicate SendItem(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps, item: int, dest: HostId)
    {
        && item in v.items
        && dest < c.numHosts
        && dest != c.myId
        && msgOps == MessageOps(None, Some(Transfer(item, dest)))
        && v'.items == v.items - multiset{item}
        && evt == NoOp
    }

    // The host receives a Transfer message whose destination is this host, and
    // adds one copy of the item in the message to its items. It sends no
    // message.
    ghost predicate ReceiveItem(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps)
    {
        && msgOps.recv.Some?
        && msgOps.recv.value.dest == c.myId
        && msgOps.send.None?
        && v'.items == v.items + multiset{msgOps.recv.value.item}
        && evt == NoOp
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
