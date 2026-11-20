// Credit: The protocol is the host of the distributed multiset from Lab 11, and
// the implementation style follows Manos' lecture (Ch.6, refinement down to an
// implementation)
include "ImplObligation.t.dfy"

// Refinement down to an implementation.
//
// In Lab 11, a host of the distributed multiset was described by protocol
// steps: predicates over mathematical values, such as multiset<int>. A real
// host runs code instead: methods over concrete values that a computer can
// store.
//
// In this lab, you write the code of one host, and prove that each step of
// the code is a step of the protocol:
//   * The host keeps its items in a sequence of 64-bit integers, sorted in
//     increasing order, so that it can find an item quickly.
//   * The sequence can hold at most MAX_LENGTH items. When it is full, a host
//     cannot add an item.
//   * In each step, the host receives one input from the outside world: a
//     request from a client, or a message from another host. It answers a
//     request with a reply, and may send a message.
//
// As in the homework, the code is split into trusted and untrusted files:
//   * MultisetSystem.t.dfy: the spec and the distributed system from Lab 11.
//   * Host.v.dfy: the protocol of a host from Lab 11. It is untrusted: the
//     Lab 11 refinement proof shows that it refines the spec.
//   * ImplObligation.t.dfy: the only way for a host to interact with the
//     outside world, and what the code of a host must do. The event of a step
//     comes from the request and the reply that the history records.
//   * lab12.dfy (this file): the code of a host.
// Do not change the other files.
//
// In this file, the state of a host, the abstraction function, the invariant,
// and the specifications of the helper methods are given to you. So are the
// bodies of FindPosition and InsertSorted, and the insert request case of
// StepImpl.
//
// Your task: fill in the rest of every method.

// The HostImpl module refines the abstract ImplObligation module: it inherits
// all its functions and methods, along with their pre- and postconditions.
// Below, we repeat the inherited conditions as comments for reference.
module HostImpl refines ImplObligation {
    // The most items that a host can hold.
    const MAX_LENGTH: nat := 0xFFFF_FFFF_FFFF_FFFF

    ghost predicate Sorted(s: seq<int64>)
    {
        forall i, j | 0 <= i < j < |s| :: s[i] <= s[j]
    }

    // items: the items of the host, sorted in increasing order
    datatype ImplVariables = ImplVariables(items: seq<int64>)

    // The abstraction function: the protocol state that the state of the
    // code stands for.
    ghost function VariablesAbstraction(v: ImplVariables): Host.Variables
    {
        Host.Variables(multiset(v.items))
    }

    ghost predicate Inv(v: ImplVariables)
    {
        && |v.items| <= MAX_LENGTH
        && Sorted(v.items)
    }

    // The position where `item` belongs in the sorted sequence `items`: every
    // item before it is smaller than `item`, and every item from it on is at
    // least `item`. It should take O(log |items|) steps.
    method FindPosition(items: seq<int64>, item: int64) returns (pos: nat)
        requires Sorted(items)
        ensures pos <= |items|
        ensures forall i | 0 <= i < pos :: items[i] < item
        ensures forall i | pos <= i < |items| :: item <= items[i]
    {
        var lo, hi := 0, |items|;
        while lo < hi
            invariant 0 <= lo <= hi <= |items|
            invariant forall i | 0 <= i < lo :: items[i] < item
            invariant forall i | hi <= i < |items| :: item <= items[i]
        {
            var mid := (lo + hi) / 2;
            if items[mid] < item {
                lo := mid + 1;
            } else {
                hi := mid;
            }
        }
        pos := lo;
    }
    // Insert one copy of `item` into the sorted sequence `items`, keeping it
    // sorted.
    method InsertSorted(items: seq<int64>, item: int64) returns (items': seq<int64>)
        requires Sorted(items)
        ensures Sorted(items')
        ensures |items'| == |items| + 1
        ensures multiset(items') == multiset(items) + multiset{item}
    {
        var pos := FindPosition(items, item);
        items' := items[..pos] + [item] + items[pos..];
        assert items == items[..pos] + items[pos..];
    }
    // Remove one copy of `item` from the sorted sequence `items`, keeping it
    // sorted. `found` says whether `item` was in `items`; if it was not,
    // `items'` is `items`.
    method RemoveSorted(items: seq<int64>, item: int64) returns (items': seq<int64>, found: bool)
        requires Sorted(items)
        ensures Sorted(items')
        ensures |items'| <= |items|
        ensures found <==> item in multiset(items)
        ensures found ==> multiset(items') == multiset(items) - multiset{item}
        ensures !found ==> items' == items
    {
    }

    // LocalInsert. If the host is full, it does nothing.
    method InsertImpl(c: ImplConstants, v: ImplVariables, item: int64) returns (v': ImplVariables)
        requires Inv(v)
        ensures Inv(v')
        ensures |v.items| < MAX_LENGTH ==>
            Host.LocalInsert(ConstantsAbstraction(c), VariablesAbstraction(v), VariablesAbstraction(v'),
                Insert(item), MessageOps(None, None), item)
        ensures |v.items| == MAX_LENGTH ==> VariablesAbstraction(v') == VariablesAbstraction(v)
    {
    }

    // LocalRemove. `removed` says whether the host removed `item`; it does
    // nothing only when it does not have `item`.
    method RemoveImpl(c: ImplConstants, v: ImplVariables, item: int64) returns (v': ImplVariables, removed: bool)
        requires Inv(v)
        ensures Inv(v')
        ensures removed ==>
            Host.LocalRemove(ConstantsAbstraction(c), VariablesAbstraction(v), VariablesAbstraction(v'),
                Remove(item), MessageOps(None, None), item)
        ensures !removed ==>
            && VariablesAbstraction(v') == VariablesAbstraction(v)
            && item !in VariablesAbstraction(v).items
    {
    }

    // SendItem. `msg` is the message that the host sends, if any; the host
    // sends nothing only when it does not have `item` or `dest` is not the id
    // of another host.
    method SendImpl(c: ImplConstants, v: ImplVariables, item: int64, dest: uint64) returns (v': ImplVariables, msg: Option<ImplMessage>)
        requires Inv(v)
        ensures Inv(v')
        ensures msg.Some? ==>
            Host.SendItem(ConstantsAbstraction(c), VariablesAbstraction(v), VariablesAbstraction(v'),
                NoOp, MessageOps(None, Some(MessageAbstraction(msg.value))), item, dest)
        ensures msg.None? ==>
            && VariablesAbstraction(v') == VariablesAbstraction(v)
            && (item !in VariablesAbstraction(v).items || dest >= c.numHosts || dest == c.myId)
    {
    }

    // ReceiveItem. `received` says whether the host received `msg`; it does
    // nothing only when `msg` is for another host or the host is full.
    method ReceiveImpl(c: ImplConstants, v: ImplVariables, msg: ImplMessage) returns (v': ImplVariables, received: bool)
        requires Inv(v)
        ensures Inv(v')
        ensures received ==>
            Host.ReceiveItem(ConstantsAbstraction(c), VariablesAbstraction(v), VariablesAbstraction(v'),
                NoOp, MessageOps(Some(MessageAbstraction(msg)), None))
        ensures !received ==>
            && VariablesAbstraction(v') == VariablesAbstraction(v)
            && (msg.dest != c.myId || |v.items| == MAX_LENGTH)
    {
    }

    method InitImpl(c: ImplConstants) returns (v: ImplVariables)
    //  ensures Inv(v)
    //  ensures Host.Init(ConstantsAbstraction(c), VariablesAbstraction(v))
    {
    }

    method StepImpl(c: ImplConstants, v: ImplVariables, world: World) returns (v': ImplVariables)
    //  requires Inv(v)
    //  modifies world
    //  ensures Inv(v')
    //  ensures |old(world.History())| <= |world.History()|
    //  ensures world.History()[..|old(world.History())|] == old(world.History())
    //  ensures var ios := world.History()[|old(world.History())|..];
    //      && ValidStep(ios)
    //      && (|| Host.Next(ConstantsAbstraction(c), VariablesAbstraction(v), VariablesAbstraction(v'),
    //                 EventOf(ios), MsgOpsOf(ios))
    //          || (&& VariablesAbstraction(v') == VariablesAbstraction(v)
    //              && EventOf(ios) == NoOp
    //              && MsgOpsOf(ios).send.None?))
    {
        ghost var h := world.History();
        var input := ReceiveInput(world);
        ghost var ac := ConstantsAbstraction(c);
        ghost var av := VariablesAbstraction(v);
        match input {
            case NetworkMessage(msg) =>
            case ClientRequest(req) =>
                match req {
                    case InsertRequest(item) =>
                        v' := InsertImpl(c, v, item);
                        if |v.items| < MAX_LENGTH {
                            SendReply(world, Done);
                            ghost var ios := [Received(input), Replied(Done)];
                            assert world.History()[|h|..] == ios;
                            assert Host.NextStep(ac, av, VariablesAbstraction(v'), EventOf(ios), MsgOpsOf(ios), Host.LocalInsertStep(item));
                        } else {
                            SendReply(world, NotDone);
                            assert world.History()[|h|..] == [Received(input), Replied(NotDone)];
                        }
                    case RemoveRequest(item) =>
                    case MoveRequest(item, dest) =>
                }
        }
    }
}
