-------------------------------- MODULE cache --------------------------------
EXTENDS Naturals, TLC, Sequences
INSTANCE cach

(*
    A cache is an ordered set of values that can each have
    reads and writes done on them.
*)

CONSTANT NUMCACHEBLOCKS, MAXCACHEVALUE

(* --algorithm cache
variables Cache = [1..NUMCACHEBLOCKS -> 1..MAXCACHEVALUE];
begin
    skip;
end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES Cache, pc

vars == << Cache, pc >>

Init == (* Global variables *)
        /\ Cache = [1..NUMCACHEBLOCKS -> 1..MAXCACHEVALUE]
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ TRUE
         /\ pc' = "Done"
         /\ Cache' = Cache

Next == Lbl_1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Fri Apr 19 17:35:00 MYT 2019 by sriram
\* Created Thu Apr 18 19:15:57 MYT 2019 by sriram
