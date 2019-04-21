------------------------------- MODULE bsort -------------------------------
EXTENDS TLC, Integers, Sequences, FiniteSets
CONSTANT ARRAYLEN

\* Get all sequences that have a max length of n, element domain S
SeqMaxLen(S, n) ==  UNION {[1..m -> S] : m \in 0..n}
SwapArr(Arr, idx) == LET el1 == Arr[idx]
                         el2 == Arr[idx+1]
                     IN [Arr EXCEPT ![idx] = el2, ![idx+1] = el1]
                     
(* --fair algorithm bsort
\* Bubble sort algorithm on a sequence of integers
variables Array \in SeqMaxLen(0..ARRAYLEN, ARRAYLEN),
          sorted = FALSE,
          idx = 1,
          temp = -1; \* Does not matter, will be assigned
begin 
    \* Swap until no more swaps possible to sort
    while sorted = FALSE do
        \* Initial state: look at start of array
        idx := 1;
        sorted := TRUE;
        
        \* Look through array to see if any swaps required
        while idx < Len(Array) do
            if Array[idx] > Array[idx+1] then
                \* Swap adjacent elements if not in order
                sorted := FALSE;
                Array := SwapArr(Array, idx);
            end if;
        end while;
     end while
end algorithm; *)
       
\* BEGIN TRANSLATION
VARIABLES Array, sorted, idx, temp, pc

vars == << Array, sorted, idx, temp, pc >>

Init == (* Global variables *)
        /\ Array \in SeqMaxLen(0..ARRAYLEN, ARRAYLEN)
        /\ sorted = FALSE
        /\ idx = 1
        /\ temp = -1
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF sorted = FALSE
               THEN /\ idx' = 1
                    /\ sorted' = TRUE
                    /\ pc' = "Lbl_2"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << sorted, idx >>
         /\ UNCHANGED << Array, temp >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF idx < Len(Array)
               THEN /\ IF Array[idx] > Array[idx+1]
                          THEN /\ sorted' = FALSE
                               /\ Array' = SwapArr(Array, idx)
                          ELSE /\ TRUE
                               /\ UNCHANGED << Array, sorted >>
                    /\ pc' = "Lbl_2"
               ELSE /\ pc' = "Lbl_1"
                    /\ UNCHANGED << Array, sorted >>
         /\ UNCHANGED << idx, temp >>

Next == Lbl_1 \/ Lbl_2
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION
\* If one element is smaller than the other, it must have a lower idx
Sorted == <>[](\A x, y \in 1..Len(Array) : Array[x] < Array[y] => x < y)

=============================================================================
\* Modification History
\* Last modified Thu Apr 18 19:25:03 MYT 2019 by sriram
\* Created Thu Apr 18 12:41:28 MYT 2019 by sriram
