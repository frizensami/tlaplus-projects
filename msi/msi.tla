    -------------------------------- MODULE msi --------------------------------
EXTENDS Naturals, TLC, Sequences, FiniteSets

IsNat(X) == X \in Nat

CONSTANTS CacheSize, MinValue, MaxValue, MaxIter, NumProcessors
ASSUME IsNat(CacheSize) 
        /\ IsNat(MinValue) 
        /\ IsNat(MaxValue) 
        /\ IsNat(MaxIter)
        /\ IsNat(NumProcessors)

\* All values a cache block can take (potentially removable)
PossibleValues == MinValue..MaxValue

\* Modified, Shared, Invalid
MSIBlockStates == {"M", "S", "I"}

\* Index values for tuples with caches
CacheIndices == 1..CacheSize

\* Index values for tuples with processors
ProcessorIndices == 1..NumProcessors

\* Set of all possible starting cacheblocks, begins with Invalid state
CacheBlocks == [state: {"I"}]
\* CacheBlocks == [val: PossibleValues, state: {"I"}]


\* Set of all possible caches
Caches == UNION {[CacheIndices -> CacheBlocks]}

\* Each processor has a cache, all processors together is a system
Systems == UNION {[ProcessorIndices -> Caches]}


(*
    For all blocks:
        If a block is invalid, 
            ignore it, no effect
        If a block is shared, 
            no other cache can have it modified, all same value
        If a block is modified, 
            no other cache can have it modified or shared
    
    
*)
NoOtherBlocksWithStates(otherblocks, states) == ~\E block \in otherblocks : block.state \in states
ValidCacheBlock(sys, p , c) == 
    LET ourblock == sys[p][c]
        otherblocks == {sys[po][c] : po \in (ProcessorIndices \ {p})} 
    IN 
        CASE ourblock.state = "S" ->  NoOtherBlocksWithStates(otherblocks, {"M"}) 
                                       \* /\ (\A block \in otherblocks : block.state = "S" => block.val = ourblock.val)
          [] ourblock.state = "M" -> NoOtherBlocksWithStates(otherblocks, {"M", "S"}) 
          [] OTHER -> TRUE
ValidProcessor(sys, p) == \A c \in CacheIndices : ValidCacheBlock(sys, p, c)
ValidSystem(sys) == \A p \in ProcessorIndices : ValidProcessor(sys, p)
ValidSystems == {sys \in Systems : ValidSystem(sys)}

(*
    Caches can recieve requests from the processor:
        - PrRd(block): processor wants to read from a cache block
        - PrWr(block): processor wants to write to a cache block
    Caches can snoop events from the bus that it's connected to
        - BusRd(block): 
            Another cache is trying to read a block it doesn't have 
                (read miss)
        - BusRdX(block):
            Another cache is trying to write to a block it doesn't have 
                (write miss)
        - BusUpgr(block):
            Another cache is writing to a block it has
                (write hit)
        - Flush(block):
            Another cache is writing back its dirty block to memory
    
    State transitions
        Block is Invalid
            PrRd  --> "S" + BusRd
            PrWr  --> "M" + BusRdX
        Block is Shared
            PrWr           --> "M" + BusUpgr 
            BusRdX/BusUpgr --> "I"
        Block is Modified
            BusRd  -> "S" + Flush
            BusRdX -> "I" + Flush
            
*)
\* Events == {"PrRd", "PrWr", "BusRd", "BusRdX", "BusUpgr"}

\* State transition struct: 
\*  Events[name][curstate] -> <<NewState, {EmittedEvent}>>
\* If it's not in this struct, no change
Events == [PrRd    |-> [I |-> <<"S", "BusRd">>],
           PrWr    |-> [I |-> <<"M", "BusRdX">>, S |-> <<"M", "BusUpgr">>],
           BusRdX  |-> [S |-> <<"I", "">>, M |-> <<"I", "">>],
           BusUpgr |-> [S |-> <<"I", "">>],
           BusRd   |-> [M |-> <<"S", "">>]
          ]

\* If there is no change to be made, return empty tuple, else the event tuple
GetEvent(eventname, curstate) == LET statemapping == Events[eventname]
                                 IN IF curstate \notin (DOMAIN statemapping)
                                    THEN <<"", "">>
                                    ELSE statemapping[curstate]

ChangeBlockState(block, newstate) 
    == 
       IF newstate = ""
       THEN block 
       ELSE [block EXCEPT !.state = newstate]

ChangeBlock(block, eventname) == 
    IF eventname = ""
    THEN block
    ELSE ChangeBlockState(block, GetEvent(eventname, block.state)[1])

\* System overall, processor id, block id, event name, value to write
DispatchEvent(sys, pid, bid, eventname) == 
    LET 
        event == GetEvent(eventname, sys[pid][bid].state)
        newstate == IF event = << >> THEN "" ELSE event[1]
        newevent == IF event = << >> THEN "" ELSE event[2]    
    IN 
        \* Re-map processor (cache)
        \* If it's the processor that is doing the event, change that block
        \* For all other processors, propagate the new event
        [cpid \in DOMAIN sys |-> 
            IF cpid = pid 
            THEN [sys[cpid] EXCEPT ![bid] = ChangeBlockState(sys[cpid][bid], newstate)]
            ELSE [sys[cpid] EXCEPT ![bid] = ChangeBlock(sys[cpid][bid], newevent)]
        ]

(* --algorithm msi
variable system \in ValidSystems,
         iter = 0;
begin     
    \* The initial system needs to be valid for this to work
    assert ValidSystem(system);
    while iter < MaxIter do
        with pid \in ProcessorIndices, bid \in CacheIndices do
            either
                system := DispatchEvent(system, pid, bid, "PrRd")
            or
                system := DispatchEvent(system, pid, bid, "PrWr");
            end either;
        end with;
        iter := iter + 1;
     end while;
end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES system, iter, pc

vars == << system, iter, pc >>

Init == (* Global variables *)
        /\ system \in ValidSystems
        /\ iter = 0
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(ValidSystem(system), 
                   "Failure of assertion at line 140, column 5.")
         /\ pc' = "Lbl_2"
         /\ UNCHANGED << system, iter >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF iter < MaxIter
               THEN /\ \E pid \in ProcessorIndices:
                         \E bid \in CacheIndices:
                           \/ /\ system' = DispatchEvent(system, pid, bid, "PrRd")
                           \/ /\ system' = DispatchEvent(system, pid, bid, "PrWr")
                    /\ iter' = iter + 1
                    /\ pc' = "Lbl_2"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << system, iter >>

Next == Lbl_1 \/ Lbl_2
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
SystemAlwaysValid == ValidSystem(system)
TypeInvariant == \A pid \in DOMAIN system : (\A bid \in DOMAIN system[pid] : (system[pid][bid].state \in MSIBlockStates))

=============================================================================
\* Modification History
\* Last modified Sun Apr 21 21:09:14 MYT 2019 by sriram
\* Created Thu Apr 18 19:15:57 MYT 2019 by sriram
