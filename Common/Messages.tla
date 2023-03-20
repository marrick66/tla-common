(* Module containing all common messaging artifacts. *)
---- MODULE Messages ----

EXTENDS TLC

CONSTANT Msg, NoMsg

(* NoMsg is a stand-in for no value *)
PossibleMessages == Msg \union { NoMsg }
====