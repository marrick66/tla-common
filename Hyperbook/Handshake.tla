---- MODULE Handshake ----
EXTENDS TLC, Integers, Sequences

Put(s) == Append(s, "Widget")
Get(s) == Tail(s)

a (+) b == (a + b) % 2

(*
--algorithm Handshake {
    variable p = 0, c = 0, box = <<>>;

    process (Producer = 0) {
        p1: while(TRUE) {
            await p = c;
            box := Put(box);
            p := p (+) 1;
        }
    }

    process (Consumer = 1) {
        c1: while(TRUE) {
            await p # c;
            box := Get(box);
            c := c (+) 1;
        }
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "9bfe55bd" /\ chksum(tla) = "4d9dae73")
VARIABLES p, c, box

vars == << p, c, box >>

ProcSet == {0} \cup {1}

Init == (* Global variables *)
        /\ p = 0
        /\ c = 0
        /\ box = <<>>

Producer == /\ p = c
            /\ box' = Put(box)
            /\ p' = p (+) 1
            /\ c' = c

Consumer == /\ p # c
            /\ box' = Get(box)
            /\ c' = c (+) 1
            /\ p' = p

Next == Producer \/ Consumer

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

A == INSTANCE Alternation WITH b <- p (+) c, box <- box

SpecA == A!Spec

LengthInvariant == Len(box) <= 1
====
