---- MODULE ActorSystem ----
EXTENDS TLC, Naturals, Envelope

VARIABLES actors

(* Auxilary definitions *)
vars == <<actors>>

ActorCommon == INSTANCE Actor

TypeOk ==  actors \in [Address -> ActorCommon!ActorState]

(* All actors start with empty in and out boxes, processing no messages. *)
Init == /\ TypeOk
        /\ actors = [a \in Address |-> [addr |-> a, inbox |-> <<>>, outbox |-> <<>>, currMsg |-> NoMsg]]

(* An actor wants to send some message to another actor *)
ToOutbox(from, to, msg) ==  LET env == ActorCommon!ToEnvelope[to, msg] IN
                            /\ actors' = [actors EXCEPT ![from] = ActorCommon!ToOutbox[env, @]]

(* An actor that has an envelope in it's inbox retrieves it and strips the message to local state *)                
StartProcessing(addr) ==    LET actor == actors[addr] IN
                            /\ Len(actor.inbox) > 0
                            /\ actors' = [actors EXCEPT ![addr] = ActorCommon!StartProcessing[actor]]

(* After some processing is complete for the current message, release it *)
FinishProcessing(addr) ==   LET actor == actors[addr] IN
                            /\ actor.currMsg # NoMsg
                            /\ actors' = [actors EXCEPT ![addr] = ActorCommon!FinishProcessing[actor]]

(* If there is an actor with an envelope waiting in it's outbox:
    1. Remove it from the outbox.
    2. Put it in the inbox of the actor at the "to" address.
*)
Send(addr) ==   LET 
                    from_actor == actors[addr]
                    env == Head(from_actor.outbox)
                    to_addr == env.to
                IN 
                /\ Len(from_actor.outbox) > 0
                /\ actors' = [actors EXCEPT ![addr] = ActorCommon!FromOutbox[@], ![to_addr] = ActorCommon!ToInbox[env, @]]

Next == \/ \E to, from \in Address, msg \in Msg : ToOutbox(from, to, msg)
        \/ \E addr \in Address: StartProcessing(addr) \/ FinishProcessing(addr) \/ Send(addr)
    
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====