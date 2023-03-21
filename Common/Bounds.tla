(* This module is needed for redefinition of infinite or innumerable sets that the model checker can't compute: *)
---- MODULE Bounds ----
EXTENDS TLC, Naturals

CONSTANT NatBound

BoundedNat == 0..NatBound

BoundedSeq(S) == UNION { [(1..y) -> S] : y \in 0..NatBound }

====