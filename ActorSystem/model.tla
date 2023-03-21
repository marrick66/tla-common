(* This module is used for debugging and checking test invariants *)
---- MODULE model ----
EXTENDS TLC, ActorSystem, Bounds

(* Constraints: *)

(*  The below is needed to ensure that appending to mailboxes doesn't exceed the bound.
    Otherwise, the actor functions will fail due to the actor state not being in the range.
*)
MailboxesLessThanOrEqualToBound == \A addr \in Address: Len(actors[addr].inbox) <= NatBound /\ Len(actors[addr].outbox) <= NatBound

(* Invariants: *)
InboxContainsOnlyMessagesFor(addr) == LET inbox == actors[addr].inbox IN 
    \A index \in 1..Len(inbox): inbox[index].to = addr

InboxOnlyContainsMessagesForCorrectAddress == \A addr \in Address: InboxContainsOnlyMessagesFor(addr)

(* Temporal properties: *)
MessageEventuallyReceived == \A addr \in Address: 
    LET inbox == actors[addr].inbox IN 
    Len(inbox) > 0 => WF_vars(StartProcessing(addr))
    
====