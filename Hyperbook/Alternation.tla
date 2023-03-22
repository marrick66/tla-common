---- MODULE Alternation ----
EXTENDS TLC, Integers, Sequences

Put(s) == Append(s, "Widget")
Get(s) == Tail(s)

(* 
--algorithm Alternate {
    variable b = 0, box = <<>>;

    fair process (Producer = 0) {
        p1: while(TRUE) {
            await b = 0;
            box := Put(box);
            b := 1;
        }
    }

    process (Consumer = 1) {
        c1: while(TRUE) {
            await b = 1;
            box := Get(box);
            b := 0;
        }
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "98c31c0" /\ chksum(tla) = "c31e16d9")
VARIABLES b, box

vars == << b, box >>

ProcSet == {0} \cup {1}

Init == (* Global variables *)
        /\ b = 0
        /\ box = <<>>

Producer == /\ b = 0
            /\ box' = Put(box)
            /\ b' = 1

Consumer == /\ b = 1
            /\ box' = Get(box)
            /\ b' = 0

Next == Producer \/ Consumer

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Producer)

\* END TRANSLATION 

LengthInvariant == Len(box) <= 1

====
