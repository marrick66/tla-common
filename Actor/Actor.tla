---- MODULE Actor ----

(* This abstraction of an actor supports: 
    - Receiving a message from it's inbox
    - Sending a message to it's outbox (possibly back to itself)
    - Some abstract processing action to be refined later
*)

EXTENDS TLC, Sequences, Naturals

CONSTANT Msg, NoMsg, Address

VARIABLES currentMsg, outbox, inbox, currentAddr

(* Auxilary definitions *)
vars == <<currentMsg, outbox, inbox, currentAddr>>

PossibleMessages == Msg \union { NoMsg }

(* An envelope is needed for routing and responding to actors:  *)
Envelope == [to: Address, msg: Msg]

(* Type correctness invariant: *)
TypeOk ==   /\ currentMsg \in PossibleMessages
            /\ outbox \in Seq(Envelope)
            /\ inbox \in Seq(Envelope)
            /\ currentAddr \in Address

Init == /\ inbox = <<>>
        /\ outbox = <<>>
        /\ currentMsg = NoMsg
        /\ currentAddr \in Address

ToOutbox(to, msg) ==    /\ outbox' = Append(outbox, [to |-> to, msg |-> msg])
                        /\ UNCHANGED <<currentMsg, inbox, currentAddr>>

ToInbox(to, msg) == /\ to = currentAddr
                    /\ inbox' = Append(inbox, [to |-> to, msg |-> msg])
                    /\ UNCHANGED <<currentMsg, outbox, currentAddr>>

Receive ==  /\ currentMsg = NoMsg
            /\ Len(inbox) > 0
            /\ currentMsg' = Head(inbox).msg
            /\ inbox' = Tail(inbox)
            /\ UNCHANGED <<outbox,currentAddr>>

Process ==  /\ currentMsg # NoMsg
            /\ currentMsg' = NoMsg
            /\ UNCHANGED <<outbox, inbox, currentAddr>>

Next == \/ (\E to \in Address, msg \in Msg: ToOutbox(to, msg))
        \/ (\E to \in Address, msg \in Msg: ToInbox(to, msg))
        \/ Receive
        \/ Process


Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(* Other invariants: *)
MessagesSentToCorrectActor == \A index \in 1..Len(inbox): inbox[index].to = currentAddr

(* Temporal properties: *)
MessageEventuallyReceived == \E to \in Address, msg \in Msg: WF_vars(ToInbox(to, msg)) /\ WF_vars(Receive)
MessageEventuallyProcessed == WF_vars(Receive) /\ WF_vars(Process)

====