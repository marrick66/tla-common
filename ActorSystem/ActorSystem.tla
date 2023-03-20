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

ToOutbox(from, to, msg) ==  LET env == ActorCommon!ToEnvelope(to, msg) IN
                            /\ actors' = [actors EXCEPT ![from] = ActorCommon!ToOutbox(env, @)]
                
ToInbox(from, to, msg)  ==  LET env == ActorCommon!ToEnvelope(to, msg) IN
                            LET actor == actors[to] IN
                            /\ actors' = [actors EXCEPT ![to] = ActorCommon!ToInbox(env, actor)]

StartProcessing(addr) ==    LET actor == actors[addr] IN
                            /\ Len(actor.inbox) > 0
                            /\ actors' = [actors EXCEPT ![addr] = ActorCommon!StartProcessing(actor)]

FinishProcessing(addr) ==   LET actor == actors[addr] IN
                            /\ actor.currMsg # NoMsg
                            /\ actors' = [actors EXCEPT ![addr] = ActorCommon!FinishProcessing(actor)]

Next == \/ \E to, from \in Address, msg \in Msg : ToOutbox(from, to, msg) \/ ToInbox(from, to, msg)
        \/ \E addr \in Address: StartProcessing(addr) \/ FinishProcessing(addr)
    
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====