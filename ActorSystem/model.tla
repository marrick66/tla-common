(* This module is used for debugging and checking test invariants *)
---- MODULE model ----
EXTENDS TLC, ActorSystem

VARIABLE op_count

(* Redefinitions: *)
BoundedNat == {1, 2}

BoundedSeq(S) == UNION { [BoundedNat -> S]}

ModelInit == /\ op_count = 0
             /\ Init

ModelToOutbox(from, to, msg) == /\ ToOutbox(from, to, msg)
                                /\ op_count' = op_count + 1
                            
ModelStartProcessing(addr) ==   /\ StartProcessing(addr)
                                /\ op_count' = op_count + 1

ModelFinishProcessing(addr) ==  /\ FinishProcessing(addr)
                                /\ op_count' = op_count + 1

ModelSend(addr) == /\ Send(addr)
                   /\ op_count' = op_count + 1

ModelNext == \/ \E to, from \in Address, msg \in Msg : ModelToOutbox(from, to, msg)
        \/ \E addr \in Address: ModelStartProcessing(addr) \/ ModelFinishProcessing(addr) \/ ModelSend(addr)
    
ModelSpec == ModelInit /\ [][ModelNext]_vars /\ WF_vars(Next)

(* Model constraints: *)
NoMailboxHasMoreThanTwoEnvelopes == \A addr \in Address: 
    Len(actors[addr].inbox) <= 2 /\ Len(actors[addr].outbox) <= 2

NoMoreThanNumOperations(num) == op_count <= num

NoMoreThanFourOperations == NoMoreThanNumOperations(4)


(* Invariants: *)
InboxContainsOnlyMessagesFor(addr) == LET inbox == actors[addr].inbox IN 
    \A index \in 1..Len(inbox): inbox[index].to = addr

InboxOnlyContainsMessagesForCorrectAddress == \A addr \in Address: InboxContainsOnlyMessagesFor(addr)

(* Temporal properties: *)
MessageEventuallyReceived == \A addr \in Address: 
    LET inbox == actors[addr].inbox IN 
    Len(inbox) > 0 => WF_vars(StartProcessing(addr))
    
====