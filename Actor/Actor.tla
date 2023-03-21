---- MODULE Actor ----

(* This abstraction of an actor supports: 
    - Receiving a message to it's inbox
    - Sending a message to it's outbox (possibly back to itself)
    - Initiate processing of a received message
    - Finish processing of the current message
    
    This isn't a full specification, since there isn't a refinement
    mapping for the records the actor system uses to keep track
    of individual actors.
*)

EXTENDS TLC, Sequences, Naturals, Envelope

ActorState == [addr: Address, inbox: Mailbox, outbox: Mailbox, currMsg: PossibleMessages]

ToOutbox[env \in Envelope, state \in ActorState] ==
    [state EXCEPT !.outbox = Append(@, env)]

FromOutbox[state \in ActorState] == 
    [state EXCEPT !.outbox = Tail(@)]

ToInbox[env \in Envelope, state \in ActorState] == 
    [state EXCEPT !.inbox = Append(@, env)]

ToEnvelope[to \in Address, msg \in Msg] ==
    [to |-> to, msg |-> msg]

StartProcessing[state \in ActorState] == LET env == Head(state.inbox) IN 
    [state EXCEPT !.inbox = Tail(@), !.currMsg = env.msg]

FinishProcessing[state \in ActorState] == 
    [state EXCEPT !.currMsg = NoMsg]

====