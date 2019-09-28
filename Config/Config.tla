------------------------------- MODULE Config -------------------------------

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* Indicates that a configuration change is waiting to be applied to the network
CONSTANT Pending

\* Indicates that a configuration change is being applied to the network
CONSTANT Applying

\* Indicates that a configuration change has been applied to the network
CONSTANT Complete

\* Indicates that a configuration change was successful
CONSTANT Succeeded

\* Indicates that a configuration change failed
CONSTANT Failed

\* The set of all nodes
CONSTANT Node

\* The set of all devices
CONSTANT Device

\* The set of all possible configuration changes
CONSTANT Change

\* An empty constant
CONSTANT Nil

\* Per-node election state
VARIABLE nodeState

\* Per-node per-device election state
VARIABLE deviceState

\* Store of network-wide configuration changes
VARIABLE networkChange

\* Store of device configuration changes
VARIABLE deviceChange

----
(*
Leader election
*)

\* Sets the current leader for the node
SetNodeLeader(n, l) ==
    /\ nodeState' = [nodeState EXCEPT ![n] = n = l]
    /\ UNCHANGED <<deviceState, networkChange, deviceChange>>

\* Sets the current leader for a device
SetDeviceLeader(n, d, l) ==
    /\ deviceState' = [deviceState EXCEPT ![n] = [deviceState[n] EXCEPT ![d] = n = l]]
    /\ UNCHANGED <<nodeState, networkChange, deviceChange>>

----
(*
Northbound API
*)

Configure(c) ==
    /\ networkChange' = Append(networkChange, [changes |-> c, status |-> Pending])
    /\ UNCHANGED <<nodeState, deviceState, deviceChange>>

----
(*
Network configuration change scheduler
*)

\* Node 'n' handles a network configuration change event 'c'
NetworkSchedulerNetworkChange(n, c) ==
    /\ nodeState[n] = TRUE \* Verify this node is the leader
    /\ LET change == networkChange[c] IN
           \* If the change does not intersect with the set of all pending/applied changes
           \* prior to the change then set the change status to Applying
           LET changeDevices == DOMAIN change.changes
               priorDevices == {d \in deviceChange : {i \in DOMAIN deviceChange[d] : 
                                   i < c /\ deviceChange[d][i].status \in {Pending, Applying}}}
           IN
               IF Cardinality(changeDevices \cap priorDevices) = 0 THEN
                   /\ networkChange' = [networkChange EXCEPT ![c].status = Applying]
               ELSE
                   /\ UNCHANGED <<networkChange>>
    /\ UNCHANGED <<nodeState, deviceState, deviceChange>>

----
(*
Network configuration controller
*)

\* Adds or updates a device change
SetDeviceChange(d, c, s) ==
    LET change == networkChange[c] IN
        IF d \in DOMAIN change.changes THEN
            IF Cardinality({x \in DOMAIN deviceChange[d] : deviceChange[d][x].id = c}) = 0 THEN
                Append(deviceChange[d], [change.changes[d] EXCEPT !.id = c, !.network = c, !.status = s])
            ELSE
                [deviceChange EXCEPT ![CHOOSE x \in DOMAIN deviceChange[d] :
                      deviceChange[d][x].id = c].status = s]
        ELSE
            deviceChange[d]

\* Node 'n' handles a network configuration change 'c'
NetworkControllerNetworkChange(n, c) ==
    /\ nodeState[n] = TRUE
    /\ LET change == networkChange[c] IN
           \/ /\ change.status = Pending
              /\ deviceChange' = [d \in Device |-> SetDeviceChange(d, c, Pending)]
           \/ /\ change.status = Applying
              /\ deviceChange' = [d \in Device |-> SetDeviceChange(d, c, Applying)]
              /\ Cardinality(DOMAIN change.changes \cap {d \in deviceChange 
                                 : {i \in DOMAIN deviceChange[d] 
                                     : deviceChange[d][i].network = c 
                                     /\ deviceChange[d][i].status = Applying}}) < Cardinality(change.changes)
              /\ deviceChange' = [d \in Device |-> IF d \in DOMAIN change.changes THEN 
                                      Append(deviceChange[d], [change.changes[d] EXCEPT 
                                                                   !.network = c, 
                                                                   !.status = Applying])
                                                              ELSE deviceChange[d]]
           \/ /\ change.status = Complete
              /\ UNCHANGED <<deviceChange>>
    /\ UNCHANGED <<nodeState, deviceState, networkChange>>

\* Node 'n' handles a device configuration change 'c'
NetworkControllerDeviceChange(n, d, c) ==
    /\ nodeState[n] = TRUE
    /\ LET change == deviceChange[d][c]
       IN
           \/ /\ deviceChange.status = Complete
              /\ LET netChange == networkChange[change.network]
                     completed == {x \in DOMAIN netChange.changes :
                                       deviceChange[x][CHOOSE i \in DOMAIN deviceChange[x] : 
                                           deviceChange[x][i].network = change.network].status = Complete}
                     succeeded == {x \in DOMAIN netChange.changes :
                                       deviceChange[x][CHOOSE i \in DOMAIN deviceChange[x] : 
                                           deviceChange[x][i].network = change.network].result = Succeeded}
                 IN
                     \/ /\ Cardinality(completed) = Cardinality(netChange.changes)
                        /\ IF Cardinality(succeeded) = Cardinality(completed) THEN
                               networkChange' = [networkChange EXCEPT ![change.network] = [
                                                     networkChange[change.network] EXCEPT
                                                         !.status = Complete, !.result = Succeeded]]
                           ELSE
                               networkChange' = [networkChange EXCEPT ![change.network] = [
                                                     networkChange[change.network] EXCEPT
                                                         !.status = Complete, !.result = Failed]]
           \/ /\ change.status # Complete
              /\ UNCHANGED <<networkChange>>
    /\ UNCHANGED <<nodeState, deviceState, deviceChange>>

----
(*
Device configuration controller
*)

\* Node 'n' handles a device configuration change event 'c'
DeviceControllerDeviceChange(n, d, c) ==
    /\ deviceState[n][d] = TRUE
    /\ LET change == deviceChange[d][c]
       IN
           \/ /\ change.status = Applying
              /\ deviceChange' = [deviceChange EXCEPT ![d] = [deviceChange[d] EXCEPT ![c] = [
                                      deviceChange[d][c] EXCEPT !.status = Complete, !.result = Succeeded]]]
           \/ /\ change.status # Applying
              /\ UNCHANGED <<deviceChange>>
    /\ UNCHANGED <<nodeState, deviceState, networkChange>>

----
(*
Init and next state predicates
*)

Init ==
    /\ nodeState = [n \in Node |-> FALSE]
    /\ deviceState = [n \in Node |-> [d \in Device |-> FALSE]]
    /\ networkChange = <<>>
    /\ deviceChange = [n \in Device |-> <<>>]

Next ==
    \/ \E d \in SUBSET Device : \E c \in Change : Configure([d -> c])
    \/ \E n \in Node : 
          \E l \in Node : 
             SetNodeLeader(n, l)
    \/ \E n \in Node :
          \E d \in Device :
             \E l \in Node :
                SetDeviceLeader(n, d, l)
    \/ \E n \in Node :
          \E c \in DOMAIN networkChange :
             NetworkSchedulerNetworkChange(n, c)
    \/ \E n \in Node :
          \E c \in DOMAIN networkChange :
             NetworkControllerNetworkChange(n, c)
    \/ \E n \in Node :
          \E d \in Device :
             \E c \in DOMAIN deviceChange[d] :
                NetworkControllerDeviceChange(n, d, c)
    \/ \E n \in Node :
          \E d \in Device :
             \E c \in DOMAIN deviceChange[d] :
                DeviceControllerDeviceChange(n, d, c)

=============================================================================
\* Modification History
\* Last modified Sat Sep 28 02:28:51 PDT 2019 by jordanhalterman
\* Created Fri Sep 27 13:14:24 PDT 2019 by jordanhalterman
