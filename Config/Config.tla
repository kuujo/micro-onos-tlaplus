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

\* An empty constant
CONSTANT Nil

\* Per-node election state
VARIABLE leadership

\* Per-node per-device election state
VARIABLE mastership

\* A sequence of network-wide configuration changes
\* Each change contains a record of 'changes' for each device
VARIABLE networkChange

\* A record of sequences of device configuration changes
\* Each sequence is a list of changes in the order in which they 
\* are to be applied to the device
VARIABLE deviceChange

\* A record of sequences of pending configuration changes to each device.
VARIABLE deviceQueue

\* A record of device states derived from configuration chagnes pushed
\* to each device.
VARIABLE deviceState

----

\* Node variables
nodeVars == <<leadership, mastership>>

\* Configuration variables
configVars == <<networkChange, deviceChange>>

\* Device variables
deviceVars == <<deviceQueue, deviceState>>

vars == <<leadership, mastership, networkChange, deviceChange, deviceState>>

----

(*
The invariant asserts that any configuration applied to a device implies that all prior configurations of the same
device have been applied to all associated devices.
*)
TypeInvariant ==
    /\ \A d \in DOMAIN deviceState :
          deviceState[d] # Nil => Cardinality({x \in deviceChange :
                                      {y \in deviceChange[d] : 
                                          /\ y < deviceState[d].network 
                                          /\ deviceChange[d][y].status # Complete}}) = 0

----
(*
This section models leader election for control loops and for devices.
Leader election is modelled as a simple boolean indicating whether each node
is the leader for the cluster and for each device. This model implies the ordering
of leadership changes is irrelevant to the correctness of the spec.
*)

\* Sets the current leader for the node
SetNodeLeader(n, l) ==
    /\ leadership' = [leadership EXCEPT ![n] = n = l]
    /\ UNCHANGED <<mastership, configVars, deviceVars>>

\* Sets the current leader for a device
SetDeviceLeader(n, d, l) ==
    /\ mastership' = [mastership EXCEPT ![n] = [mastership[n] EXCEPT ![d] = n = l]]
    /\ UNCHANGED <<leadership, configVars, deviceVars>>

----
(*
This section models the northbound API for the configuration service. The API
exposes a single step to enqueue a configuration change. Rollback is not explicitly
modelled as it can be implemented in an additional Configure step performing the
inverse of the change being rolled back. When a configuration change is enqueued,
it's simply added to network change for control loops to handle.
*)

\* Enqueues a configuration change to be applied to devices
Configure(c) ==
    /\ networkChange' = Append(networkChange, [changes |-> c, status |-> Pending])
    /\ UNCHANGED <<nodeVars, deviceChange, deviceVars>>

----
(*
This section models a configuration change scheduler. The roll of the scheduler is
to determine when network changes can be applied and enqueue the relevant changes
for application by changing their status from 'Pending' to 'Applying'. The scheduler
supports concurrent application of non-overlapping configuration changes (changes
that do not impact intersecting sets of devices) by comparing 'Pending' changes with
'Applying' changes.
*)

\* Returns the set of all device changes prior to the given change 'c'
PrevChanges(c) ==
    UNION {{deviceChange[d][i] :
                i \in {x \in DOMAIN deviceChange[d] : x < c}} :
                    d \in DOMAIN deviceChange}

\* Returns the set of all incomplete device changes prior to the given change 'c'
IncompleteChanges(c) ==
    UNION {{d : i \in {x \in DOMAIN deviceChange[d] : x < c /\ deviceChange[d][x].status # Complete}} :
                d \in DOMAIN deviceChange}

\* Returns the set of all devices configured by network change 'c'
NetworkDevices(c) == DOMAIN networkChange[c].changes

\* Node 'n' handles a network configuration change event 'c'
NetworkSchedulerNetworkChange(n, c) ==
    /\ leadership[n] = TRUE
    /\ IF Cardinality(NetworkDevices(c) \cap IncompleteChanges(c)) = 0 THEN
           /\ networkChange' = [networkChange EXCEPT ![c].status = Applying]
       ELSE
           /\ UNCHANGED <<networkChange>>
    /\ UNCHANGED <<nodeVars, deviceChange, deviceVars>>

----
(*
This section models the network-level change controller. The network control loop
reacts to both network and device changes. 
The network controller runs on each node in the cluster, and the control loop can only
be executed on a node that believes itself to be the leader. Note, however, that the
model does not require a single leader.

When a network change is received:
- If the network change status is 'Pending', add device changes for each configured device
- If the network change status is 'Applying', update device change statuses to 'Applying'
When a device change is received:
- If all device change statuses for the network are 'Complete', mark the network change
  'Complete' with a result of 'Succeeded' if all device changes succeeded, otherwise 'Failed'

Updates to network and device changes are atomic, and real-world implementations of the spec
must provide for atomic updates for network and device changes as well. This can be done using
either optimistic or pessimistic concurrency control.
*)

\* Returns a boolean indicating whether the given device change already exists
HasDeviceChange(d, c) ==
    Cardinality({x \in DOMAIN deviceChange[d] : deviceChange[d][x].network = c}) # 0

\* Adds a change to a device
AddDeviceChange(d, c, s) ==
    Append(deviceChange[d], [network |-> c, status |-> s, value |-> networkChange[c].changes[d]])

\* Updates the status of a device cahnge
UpdateDeviceChange(d, c, s) ==
    [deviceChange[d] EXCEPT ![CHOOSE x \in DOMAIN deviceChange[d] :
                  deviceChange[d][x].network = c].status = s]

\* Adds or updates a device change
SetDeviceChange(d, c, s) ==
    IF d \in DOMAIN networkChange[c].changes THEN
        IF HasDeviceChange(d, c) THEN
            UpdateDeviceChange(d, c, s)
        ELSE
            AddDeviceChange(d, c, s)
    ELSE
        deviceChange[d]

\* Returns the set of all device changes for the given network change 'c'
DeviceChanges(c) ==
    {d \in DOMAIN networkChange[c].changes :
        {x \in deviceChange[d] : deviceChange[d][x].network = c}}

\* Returns a boolean indicating whether all device changes for the given network change are complete
DeviceChangesComplete(c) ==
    Cardinality({x \in DeviceChanges(c) : x.status = Complete}) = Cardinality(DeviceChanges(c))

\* Returns a boolean indicating whether all device changes for the given network change were successful
DeviceChangesSucceeded(c) ==
    Cardinality({x \in DeviceChanges(c) : x.result = Succeeded}) = Cardinality(DeviceChanges(c))

\* Node 'n' handles a network configuration change 'c'
NetworkControllerNetworkChange(n, c) ==
    /\ leadership[n] = TRUE
    /\ LET change == networkChange[c] IN
           \/ /\ change.status = Pending
              /\ deviceChange' = [d \in Device |-> SetDeviceChange(d, c, Pending)]
           \/ /\ change.status = Applying
              /\ deviceChange' = [d \in Device |-> SetDeviceChange(d, c, Applying)]
           \/ /\ change.status = Complete
              /\ UNCHANGED <<deviceChange>>
    /\ UNCHANGED <<nodeVars, networkChange, deviceVars>>

\* Node 'n' handles a device configuration change 'c'
NetworkControllerDeviceChange(n, d, c) ==
    /\ leadership[n] = TRUE
    /\ LET change == deviceChange[d][c]
       IN
           \/ /\ change.status = Complete
              /\ \/ /\ DeviceChangesComplete(change.network)
                    /\ DeviceChangesSucceeded(change.network)
                    /\ networkChange' = [networkChange EXCEPT ![change.network] = [
                                             networkChange[change.network] EXCEPT
                                                 !.status = Complete, !.result = Succeeded]]
                 \/ /\ DeviceChangesComplete(change.network)
                    /\ ~DeviceChangesSucceeded(change.network)
                    /\ networkChange' = [networkChange EXCEPT ![change.network] = [
                                             networkChange[change.network] EXCEPT
                                                 !.status = Complete, !.result = Failed]]
                 \/ /\ ~DeviceChangesComplete(change.network)
                    /\ UNCHANGED <<networkChange>>
           \/ /\ change.status # Complete
              /\ UNCHANGED <<networkChange>>
    /\ UNCHANGED <<nodeVars, deviceChange, deviceVars>>

----
(*
This section models the device-level change controller. The device control loop reacts
to device changes and applies changes to devices.
The device controller runs on each node in the cluster. A master is elected for each device,
and the control loop can only be executed on the master for the device targeted by a change.
Note, however, that the model does not require a single master per device. Multiple masters
may exist for a device without violating safety properties.

When a device change is received:
- If the node believes itself to be the master for the device and the change status
  is 'Applying', apply the change
- Set the change status to 'Complete'
- If the change was applied successfully, set the change result to 'Succeeded'
- If the change failed, set the change result to 'Failed'

Note: the above is modelled in two separate steps to allow the model checker to succeed
and fail device changes.

Updates to network device changes are atomic, and real-world implementations of the spec
must provide for atomic updates for network and device changes as well. This can be done using
either optimistic or pessimistic concurrency control.
*)

\* Node 'n' handles a device configuration change event 'c'
DeviceControllerDeviceChange(n, d, c) ==
    /\ mastership[n][d] = TRUE
    /\ LET change == deviceChange[d][c]
       IN
           \/ /\ change.status = Applying
              /\ deviceQueue' = [deviceQueue EXCEPT ![d] = Append(deviceQueue[d], deviceChange[d][c])]
           \/ /\ change.status # Applying
              /\ UNCHANGED <<deviceQueue>>
    /\ UNCHANGED <<nodeVars, configVars, deviceState>>

\* Returns a sequence with the head removed
Pop(q) == SubSeq(q, 2, Len(q))

\* Marks a device change as succeeded
SucceedChange(d, c) ==
    /\ deviceChange' = [deviceChange EXCEPT ![d] = [deviceChange[d] EXCEPT ![c] = [
                            deviceChange[d][c] EXCEPT !.status = Complete, !.result = Succeeded]]]
    /\ deviceState' = [deviceState EXCEPT ![d] = deviceQueue[d]]
    /\ deviceQueue' = [deviceQueue EXCEPT ![d] = Pop(deviceQueue[d])]
    /\ UNCHANGED <<nodeVars, networkChange>>

\* Marks a device change as failed
FailChange(d, c) ==
    /\ deviceChange' = [deviceChange EXCEPT ![d] = [deviceChange[d] EXCEPT ![c] = [
                            deviceChange[d][c] EXCEPT !.status = Complete, !.result = Failed]]]
    /\ deviceQueue' = [deviceQueue EXCEPT ![d] = Pop(deviceQueue[d])]
    /\ UNCHANGED <<nodeVars, networkChange, deviceState>>

----
(*
Init and next state predicates
*)

Init ==
    /\ leadership = [n \in Node |-> FALSE]
    /\ mastership = [n \in Node |-> [d \in Device |-> FALSE]]
    /\ networkChange = <<>>
    /\ deviceChange = [d \in Device |-> <<>>]
    /\ deviceQueue = [d \in Device |-> <<>>]
    /\ deviceState = [d \in Device |-> Nil]

Next ==
    \/ \E d \in SUBSET Device : 
          Configure([x \in d |-> 1])
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
    \/ \E d \in Device :
          \E c \in DOMAIN deviceQueue[d] :
             SucceedChange(d, c)
    \/ \E d \in Device :
          \E c \in DOMAIN deviceQueue[d] :
             FailChange(d, c)

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Sun Sep 29 00:07:20 PDT 2019 by jordanhalterman
\* Created Fri Sep 27 13:14:24 PDT 2019 by jordanhalterman
