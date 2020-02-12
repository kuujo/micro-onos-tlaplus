----------------------------- MODULE IndexedMap -----------------------------

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* An empty value
CONSTANT Nil

\* The set of possible keys
CONSTANT Key

\* The number of possible indexes
CONSTANT MaxIndex

\* The set of possible values
CONSTANT Value

\* The map state
VARIABLE map

\* A sequence of map events
VARIABLE mapEvents

\* The log state
VARIABLE log

\* A sequence of log events
VARIABLE logEvents

vars == <<map, mapEvents, log, logEvents>>

----

TypeInvariant == TRUE

----

(*
This section of the spec models map primitive operations.
*)

\* Get the value of index 'i' from the map
GetIndex(i) == TRUE

\* Get the value of key 'k' from the map
GetKey(k) == TRUE

\* Set key 'k' value to 'v'
PutKey(k, v) == TRUE

\* Remove the entry at index 'i'
RemoveIndex(i) == TRUE

\* Remove the entry with key 'k'
RemoveKey(k) == TRUE

\* Receive an event
ReceiveEvent == TRUE

----

Init ==
    /\ map = [k \in {} |-> [value |-> Nil, version |-> Nil]]
    /\ mapEvents = <<>>
    /\ log = <<>>
    /\ logEvents = <<>>

Next ==
    \/ \E i \in 1..MaxIndex : GetIndex(i)
    \/ \E k \in Key : GetKey(k)
    \/ \E k \in Key : \E v \in Value : PutKey(k, v)
    \/ \E i \in 1..MaxIndex : RemoveIndex(i)
    \/ \E k \in Key : RemoveKey(k)
    \/ ReceiveEvent

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Wed Feb 12 13:05:39 PST 2020 by jordanhalterman
\* Created Wed Feb 12 11:20:15 PST 2020 by jordanhalterman
