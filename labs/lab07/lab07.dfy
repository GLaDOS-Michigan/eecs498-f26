// Credit: Some boilerplate adapted from Manos' in-class demo (Ch.5)
include "UtilitiesLibrary.dfy"

// A distributed lock with a network. This is like the lock service in
// Problem Set 2, but there is no server: the hosts pass the lock among
// themselves by sending messages over a network.
//
// There are numHosts hosts, with ids 0, ..., numHosts - 1. Each host records
// whether it holds the lock. Initially, host 0 holds the lock, no other host
// holds it, and there are no messages in the network.
//
// The network: a message that has been sent can be received later, in any
// order, but each message can be received at most once. This is different
// from the network in lecture, where a message, once sent, can be received
// over and over.
//
// A host can perform two actions:
//   * SendLock: a host that holds the lock sends a message to transfer the
//     lock to a recipient host. It no longer holds the lock.
//   * ReceiveLock: a host receives a message that transfers the lock to it,
//     and now holds the lock.
//
// In each step of the distributed system, one host takes a step together
// with the network.
//
// Your task:
//   * Fill in the network: its Variables, Init, and Next.
//   * Fill in the host's Init, SendLock, and ReceiveLock.
//   * Fill in the distributed system's Init and HostAction. The Jay Normal
//     Form (JNF), which connects the host and the network, is already written
//     for you.
//   * Write the safety condition: no two hosts hold the lock at the same time.
//   * Write an invariant and prove that the system is safe.
//
// Think about it: what could go wrong if the network could deliver the same
// message more than once?

module HostIdentifiers {
    type HostId = int

    ghost predicate ValidHostId(numHosts: nat, hostid: HostId)
    {
        0 <= hostid < numHosts
    }
}

module Network {
    import opened UtilitiesLibrary

    datatype MessageOps<Message> = MessageOps(recv: Option<Message>, send: Option<Message>)

    datatype Constants = Constants(numHosts: nat)
    {
        ghost predicate Configure(numHosts: nat)
        {
            this.numHosts == numHosts
        }
    }

    datatype Variables<Message> = Variables()

    ghost predicate Init<Message>(c: Constants, v: Variables<Message>)
    {
        true
    }

    ghost predicate Next<Message>(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
    {
        true
    }
}

module Host {
    import opened UtilitiesLibrary
    import opened HostIdentifiers
    import Network

    datatype Message = TransferLockMsg(dest: HostId)

    datatype Constants = Constants(numHosts: nat, myId: HostId)
    {
        // host constants coupled to DistributedSystem Constants:
        // DistributedSystem tells us our id so we can recognize inbound messages.
        ghost predicate Configure(numHosts: nat, id: HostId)
        {
            && this.numHosts == numHosts
            && this.myId == id
        }
    }

    datatype Variables = Variables(holdsLock: bool)

    ghost predicate Init(c: Constants, v: Variables)
    {
        true
    }

    // Send a message that transfers the lock to `recipient`.
    ghost predicate SendLock(c: Constants, v: Variables, v': Variables, msgOps: Network.MessageOps<Message>, recipient: HostId)
    {
        true
    }

    // Receive a message that transfers the lock to this host.
    ghost predicate ReceiveLock(c: Constants, v: Variables, v': Variables, msgOps: Network.MessageOps<Message>)
    {
        true
    }

    datatype Step =
        | SendLockStep(recipient: HostId)
        | ReceiveLockStep()

    ghost predicate NextStep(c: Constants, v: Variables, v': Variables, msgOps: Network.MessageOps<Message>, step: Step)
    {
        match step
            case SendLockStep(recipient) => SendLock(c, v, v', msgOps, recipient)
            case ReceiveLockStep => ReceiveLock(c, v, v', msgOps)
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: Network.MessageOps<Message>)
    {
        exists step :: NextStep(c, v, v', msgOps, step)
    }
}

module DistributedSystem {
    import opened HostIdentifiers
    import Host
    import Network

    datatype Constants = Constants(
        hosts: seq<Host.Constants>,
        network: Network.Constants
    )
    {
        ghost predicate WF()
        {
            // Network numHosts and each host's numHosts agree with the size of our
            // own host list
            && network.Configure(|hosts|)
            && (forall id | ValidHostId(id) :: hosts[id].Configure(|hosts|, id))  // every host knows its id (and ids are unique)
        }

        ghost predicate ValidHostId(hostid: HostId)
        {
            HostIdentifiers.ValidHostId(|hosts|, hostid)
        }
    }

    datatype Variables = Variables(
        hosts: seq<Host.Variables>,
        network: Network.Variables<Host.Message>
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
        true
    }

    // Host `hostid` takes a step, and every other host stays the same.
    ghost predicate HostAction(c: Constants, v: Variables, v': Variables, hostid: HostId, msgOps: Network.MessageOps<Host.Message>)
    {
        true
    }

    datatype Step =
        | HostActionStep(hostid: HostId, msgOps: Network.MessageOps<Host.Message>)

    ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
    {
        && HostAction(c, v, v', step.hostid, step.msgOps)
        // The network agrees on what is received and records what is sent
        && Network.Next(c.network, v.network, v'.network, step.msgOps)
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables)
    {
        exists step :: NextStep(c, v, v', step)
    }
}

module SafetySpec {
    import opened HostIdentifiers
    import DistributedSystem

    ghost predicate Safety(c: DistributedSystem.Constants, v: DistributedSystem.Variables)
    {
        true
    }
}

module Proof {
    import opened HostIdentifiers
    import Host
    import opened DistributedSystem
    import opened SafetySpec

    // Define additional functions and lemmas as needed



    ghost predicate Inv(c: Constants, v: Variables)
    {
        true
    }

    lemma InitImpliesInv(c: Constants, v: Variables)
        requires Init(c, v)
        ensures Inv(c, v)
    {
        
    }

    lemma InvImpliesSafety(c: Constants, v: Variables)
        requires Inv(c, v)
        ensures Safety(c, v)
    {
        
    }

    lemma NextPreservesInv(c: Constants, v: Variables, v': Variables)
        requires Inv(c, v)
        requires Next(c, v, v')
        ensures Inv(c, v')
    {
        
    }
}
