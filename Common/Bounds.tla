(* This module is needed for redefinition of infinite or innumerable sets that the model checker can't compute: *)
---- MODULE Bounds ----
EXTENDS TLC, Naturals

CONSTANT NatBound

(* Redefinition of Nat and Seq to allow TLC to compute them: *)
BoundedNat == 0..NatBound

BoundedSeq(S) == UNION { [(1..y) -> S] : y \in 0..NatBound }

====