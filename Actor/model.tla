(* This module is used for debugging and checking test invariants *)
---- MODULE model ----
EXTENDS TLC, Actor

(*Test constraint: *)
LengthConstraint == /\ Len(inbox) < 3
                    /\ Len(outbox) < 3

(* Test Invariants *)
MailboxesEmpty ==   \/  /\ inbox = <<>>
                        /\ outbox = <<>>
                    \/  /\ inbox # <<>>
                        /\ outbox = <<>>
                    \/  /\ inbox = <<>>
                        /\ outbox # <<>>

NeverReceived == currentMsg = NoMsg

====