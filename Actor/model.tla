(* This module is used for debugging and checking test invariants *)
---- MODULE model ----
EXTENDS TLC, Actor


(* Test Invariants *)
MailboxesEmpty ==   \/  /\ inbox = <<>>
                        /\ outbox = <<>>
                    \/  /\ inbox # <<>>
                        /\ outbox = <<>>
                    \/  /\ inbox = <<>>
                        /\ outbox # <<>>

NeverReceived == currentMsg = NoMsg

====