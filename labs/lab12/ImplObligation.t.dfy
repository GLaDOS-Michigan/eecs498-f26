// What the code of a host must do. This file is trusted.
//   * Module Io is the only way for a host to interact with the outside world.
//     Every interaction is recorded in the history of the world.
//   * Module ImplObligation says what each step of the code must do.
include "MultisetSystem.t.dfy"

module Io {
    // Integers that fit in 64 bits.
    type int64 = x: int | -0x8000_0000_0000_0000 <= x < 0x8000_0000_0000_0000
    type uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

    datatype ImplMessage = ImplTransfer(item: int64, dest: uint64)

    // A request from a client.
    datatype Request =
        | InsertRequest(item: int64)
        | RemoveRequest(item: int64)
        | MoveRequest(item: int64, dest: uint64)

    // The reply of the host to a request.
    datatype Reply = Done | NotDone

    // What a host receives: a request from a client, or a message from
    // another host.
    datatype Input =
        | ClientRequest(req: Request)
        | NetworkMessage(msg: ImplMessage)

    // One interaction of a host with the outside world.
    datatype IoEvent =
        | Received(input: Input)
        | Replied(reply: Reply)
        | Sent(msg: ImplMessage)

    // The outside world, as one host sees it. History() is every interaction
    // of the host with the outside world, in order. World has no fields, so
    // only the methods below can change History().
    class World {
        ghost function {:axiom} History(): seq<IoEvent>
            reads this
    }

    method {:extern} {:axiom} ReceiveInput(world: World) returns (input: Input)
        modifies world
        ensures world.History() == old(world.History()) + [Received(input)]

    method {:extern} {:axiom} SendReply(world: World, reply: Reply)
        modifies world
        ensures world.History() == old(world.History()) + [Replied(reply)]

    method {:extern} {:axiom} SendMessage(world: World, msg: ImplMessage)
        modifies world
        ensures world.History() == old(world.History()) + [Sent(msg)]
}

abstract module ImplObligation {
    import opened UtilitiesLibrary
    import opened Events
    import opened Types
    import opened Io
    import Host

    datatype ImplConstants = ImplConstants(numHosts: uint64, myId: uint64)

    ghost function ConstantsAbstraction(c: ImplConstants): Host.Constants
    {
        Host.Constants(c.numHosts, c.myId)
    }

    ghost function MessageAbstraction(m: ImplMessage): Message
    {
        Transfer(m.item, m.dest)
    }

    // The interactions of one step: the host receives one input, then
    //   * for an insert or remove request: replies;
    //   * for a move request: replies NotDone, or sends the item to `dest`
    //     and replies Done;
    //   * for a message from another host: does nothing else.
    ghost predicate ValidStep(ios: seq<IoEvent>)
    {
        && 0 < |ios|
        && ios[0].Received?
        && match ios[0].input
            case NetworkMessage(_) => |ios| == 1
            case ClientRequest(req) =>
                if req.MoveRequest? then
                    || ios == [ios[0], Replied(NotDone)]
                    || ios == [ios[0], Sent(ImplTransfer(req.item, req.dest)), Replied(Done)]
                else
                    |ios| == 2 && ios[1].Replied?
    }

    // The event of a step. It comes from the request and the reply, not from
    // the code.
    ghost function EventOf(ios: seq<IoEvent>): Event
        requires ValidStep(ios)
    {
        if ios[0].input.ClientRequest? && ios[|ios| - 1] == Replied(Done) then
            match ios[0].input.req
                case InsertRequest(item) => Insert(item)
                case RemoveRequest(item) => Remove(item)
                case MoveRequest(_, _) => NoOp
        else
            NoOp
    }

    // The messages that the host receives and sends in a step.
    ghost function MsgOpsOf(ios: seq<IoEvent>): MessageOps
        requires ValidStep(ios)
    {
        MessageOps(
            if ios[0].input.NetworkMessage? then Some(MessageAbstraction(ios[0].input.msg)) else None,
            if |ios| == 3 then Some(MessageAbstraction(ios[1].msg)) else None)
    }

    // The implementation chooses the state of a host, the abstraction
    // function, and the invariant.
    type ImplVariables

    ghost function VariablesAbstraction(v: ImplVariables): Host.Variables

    ghost predicate Inv(v: ImplVariables)

    // The initial state of a host.
    method InitImpl(c: ImplConstants) returns (v: ImplVariables)
        ensures Inv(v)
        ensures Host.Init(ConstantsAbstraction(c), VariablesAbstraction(v))

    // One step of a host. The host may change only the world (through the
    // methods of Io) and its own state. What it did in the world must be a
    // valid step, and must be a step of the protocol, or change nothing.
    method StepImpl(c: ImplConstants, v: ImplVariables, world: World) returns (v': ImplVariables)
        requires Inv(v)
        modifies world
        ensures Inv(v')
        ensures |old(world.History())| <= |world.History()|
        ensures world.History()[..|old(world.History())|] == old(world.History())
        ensures var ios := world.History()[|old(world.History())|..];
            && ValidStep(ios)
            && (|| Host.Next(ConstantsAbstraction(c), VariablesAbstraction(v), VariablesAbstraction(v'),
                       EventOf(ios), MsgOpsOf(ios))
                || (&& VariablesAbstraction(v') == VariablesAbstraction(v)
                    && EventOf(ios) == NoOp
                    && MsgOpsOf(ios).send.None?))

    // The main loop of a host.
    method Main(c: ImplConstants, world: World)
        modifies world
        decreases *
    {
        var v := InitImpl(c);
        while true
            invariant Inv(v)
            decreases *
        {
            v := StepImpl(c, v, world);
        }
    }
}
