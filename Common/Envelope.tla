(* Contains actor message-related artifacts. *)
---- MODULE Envelope ----
EXTENDS TLC, Messages, Sequences

CONSTANT Address

(* An envelope is needed for routing and responding to actors:  *)
Envelope == [to: Address, msg: Msg]

(* Actors have both an inbox and outbox that use these: *)
Mailbox == Seq(Envelope)
====