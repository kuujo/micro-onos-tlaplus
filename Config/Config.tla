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

\* Indicates a change is a configuration
CONSTANT Change

\* Indicates a change is a rollback
CONSTANT Rollback

\* Indicates a device is available
CONSTANT Available

\* Indicates a device is unavailable
CONSTANT Unavailable

\* Indicates that an error occurred when applying a change
CONSTANT Error

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

\* A record of device configurations derived from configuration chagnes pushed
\* to each device.
VARIABLE deviceConfig

\* A record of device states - either Available or Unavailable
VARIABLE deviceState

\* A count of leader changes to serve as a state constraint
VARIABLE electionCount

\* A count of configuration changes to serve as a state constraint
VARIABLE configCount

\* A count of device availability changes to serve as a state constraint
VARIABLE availabilityCount

----

\* Node variables
nodeVars == <<leadership, mastership>>

\* Configuration variables
configVars == <<networkChange, deviceChange>>

\* Device variables
deviceVars == <<deviceQueue, deviceConfig, deviceState>>

\* State constraint variables
constraintVars == <<electionCount, configCount, availabilityCount>>

vars == <<leadership, mastership, networkChange, deviceChange, deviceConfig>>

----

(*
The invariant asserts that any configuration applied to a device implies that all prior configurations of the same
device have been applied to all associated devices.
*)
TypeInvariant ==
    /\ \A d \in DOMAIN deviceConfig :
          deviceConfig[d] # 0 =>
              Cardinality(UNION {{y \in DOMAIN deviceChange[x] :
                                    /\ deviceChange[x][y].network < deviceConfig[x] 
                                    /\ deviceChange[x][y].state # Complete} :
                                        x \in DOMAIN deviceChange}) = 0

----
(*
This section models leader election for control loops and for devices.
Leader election is modelled as a simple boolean indicating whether each node
is the leader for the cluster and for each device. This model implies the ordering
of leadership changes is irrelevant to the correctness of the spec.
*)

\* Set the leader for node n to l
SetNodeLeader(n, l) ==
    /\ leadership' = [leadership EXCEPT ![n] = n = l]
    /\ electionCount' = electionCount + 1
    /\ UNCHANGED <<mastership, configVars, deviceVars, configCount, availabilityCount>>

\* Set the master for device d on node n to l
SetDeviceMaster(n, d, l) ==
    /\ mastership' = [mastership EXCEPT ![n] = [mastership[n] EXCEPT ![d] = n = l]]
    /\ electionCount' = electionCount + 1
    /\ UNCHANGED <<leadership, configVars, deviceVars, configCount, availabilityCount>>

----
(*
This section models the northbound API for the configuration service.
*)

\* Enqueue network configuration change c
SubmitChange(c) ==
    /\ networkChange' = Append(networkChange, [
                            phase   |-> Change,
                            changes |-> c, 
                            value   |-> Len(networkChange),
                            state   |-> Pending,
                            result  |-> Nil])
    /\ configCount' = configCount + 1
    /\ UNCHANGED <<nodeVars, deviceChange, deviceVars, electionCount, availabilityCount>>

\* Roll back configuration change c
SubmitRollback(c) ==
    /\ networkChange' = Append(networkChange, [
                            phase   |-> Rollback,
                            changes |-> networkChange[c].changes,
                            value   |-> c,
                            state   |-> Pending,
                            result  |-> Nil])
    /\ configCount' = configCount + 1
    /\ UNCHANGED <<nodeVars, deviceChange, deviceVars, electionCount, availabilityCount>>

----
(*
This section models a configuration change scheduler. The role of the scheduler is
to determine when network changes can be applied and enqueue the relevant changes
for application by changing their state from Pending to Applying. The scheduler
supports concurrent application of non-overlapping configuration changes (changes
that do not impact intersecting sets of devices) by comparing Pending changes with
Applying changes.
*)

\* Return the set of all network changes prior to the given change
PriorNetworkChanges(c) ==
    {n \in DOMAIN networkChange : n < c}

\* Return the set of all completed device changes for network change c
NetworkCompletedChanges(c) ==
    {d \in DOMAIN networkChange[c].changes :
        /\ Cardinality({x \in DOMAIN deviceChange[d] : deviceChange[d][x].network = c}) # 0 
        /\ deviceChange[d][CHOOSE x \in DOMAIN deviceChange[d] 
               : deviceChange[d][x].network = c].state = Complete}

\* Return a boolean indicating whether all device changes are complete for the given network change
NetworkChangesComplete(c) == 
    Cardinality(NetworkCompletedChanges(c)) = Cardinality(DOMAIN networkChange[c].changes)

\* Return the set of all incomplete device changes prior to network change c
PriorIncompleteDevices(c) ==
    UNION {DOMAIN networkChange[n].changes : 
               n \in {n \in PriorNetworkChanges(c) : ~NetworkChangesComplete(n)}}

\* Return the set of all devices configured by network change c
NetworkChangeDevices(c) == DOMAIN networkChange[c].changes

\* Return a boolean indicating whether network change c can be applied
\* A change can be applied if its devices do not intersect with past device
\* changes that have not been applied
CanApply(c) ==
    Cardinality(NetworkChangeDevices(c) \cap PriorIncompleteDevices(c)) = 0

\* Node n handles a network configuration change event c
NetworkSchedulerNetworkChange(n, c) ==
    /\ leadership[n] = TRUE
    /\ networkChange[c].state = Pending
    /\ CanApply(c)
    /\ networkChange' = [networkChange EXCEPT ![c].state = Applying]
    /\ UNCHANGED <<nodeVars, deviceChange, deviceVars, constraintVars>>

----
(*
This section models the network-level change controller. The network control loop
reacts to both network and device changes. 
The network controller runs on each node in the cluster, and the control loop can only
be executed on a node that believes itself to be the leader. Note, however, that the
model does not require a single leader.

When a network change is received:
- If the network change state is Pending
  - Add device changes for each configured device
- If the network change state is Applying
  - Update device change states to Applying

When a device change is received:
- If all device change states for the network are Complete
  - Mark the network change Complete with a Succeeded result if all device changes succeeded
  - Otherwise mark the network change Complete with a Failed result
- If all device changes failed due to Unavailable devices
  - Set the network change back to Pending
- If at least one device change succeeded but a subset failed
  - Fail the network change

Updates to network and device changes are atomic, and real-world implementations of the spec
must provide for atomic updates for network and device changes as well. This can be done using
either optimistic or pessimistic concurrency control.
*)

\* Return a boolean indicating whether change c on device d already exists
HasDeviceChange(d, c) ==
    Cardinality({x \in DOMAIN deviceChange[d] : deviceChange[d][x].network = c}) # 0

\* Return the index of the device change for network change c
DeviceChange(d, c) ==
    CHOOSE x \in DOMAIN deviceChange[d] : deviceChange[d][x].network = c

\* Return a boolean indicating whether the device change for network change c has state s
HasDeviceState(d, c, s) ==
    HasDeviceChange(d, c) /\ deviceChange[d][DeviceChange(d, c)].state = s

\* Add change c on device s
AddDeviceChange(d, c) ==
    IF d \in DOMAIN networkChange[c].changes /\ ~HasDeviceChange(d, c) THEN
        Append(deviceChange[d], [
            network |-> c, 
            phase   |-> networkChange[c].phase,
            state   |-> Pending, 
            value   |-> networkChange[c].value, 
            result  |-> Nil,
            reason  |-> Nil])
    ELSE
        deviceChange[d]

\* Change the state of change c on device s from Pending to Applying
ApplyDeviceChange(d, c) ==
    IF d \in DOMAIN networkChange[c].changes THEN
        IF HasDeviceChange(d, c) THEN
            IF HasDeviceState(d, c, Pending) THEN
                [deviceChange[d] EXCEPT ![DeviceChange(d, c)].state = Applying]
            ELSE
                deviceChange[d]
        ELSE
            Append(deviceChange[d], [
                network |-> c, 
                phase   |-> networkChange[c].phase,
                state   |-> Applying, 
                value   |-> networkChange[c].value, 
                result  |-> Nil,
                reason  |-> Nil])
    ELSE
        deviceChange[d]

\* Change the state of change c on device s to Pending
PendDeviceChange(d, c) ==
    IF d \in DOMAIN networkChange[c].changes THEN
        [deviceChange[d] EXCEPT ![DeviceChange(d, c)].state = Pending]
    ELSE
        deviceChange[d]

\* Return the set of all device changes for network change c
DeviceChanges(c) ==
    {deviceChange[d][DeviceChange(d, c)] :
        d \in {d \in DOMAIN networkChange[c].changes : HasDeviceChange(d, c)}}

\* Return a boolean indicating whether all device changes for network change c are complete
DeviceChangesComplete(c) ==
    Cardinality({x \in DeviceChanges(c) : x.state = Complete}) = Cardinality(DeviceChanges(c))

\* Return a boolean indicating whether all device changes for network change c were successful
DeviceChangesSucceeded(c) ==
    Cardinality({x \in DeviceChanges(c) : x.result = Succeeded}) = Cardinality(DeviceChanges(c))

\* Return a boolean indicating whether all device changes failed due to Unavailable devices
DeviceChangesUnavailable(c) ==
    Cardinality({x \in DeviceChanges(c) : x.result = Failed /\ x.reason = Unavailable}) =
        Cardinality(DeviceChanges(c))

\* Node n handles a network configuration change c
NetworkControllerNetworkChange(n, c) ==
    /\ leadership[n] = TRUE
    /\ LET change == networkChange[c] IN
           \/ /\ change.state = Pending
              /\ Cardinality({d \in DOMAIN networkChange[c].changes : 
                     ~HasDeviceState(d, c, Pending)}) > 0
              /\ deviceChange' = [d \in Device |-> AddDeviceChange(d, c)]
           \/ /\ change.state = Applying
              /\ Cardinality({d \in DOMAIN networkChange[c].changes : 
                     ~HasDeviceState(d, c, Applying)}) > 0
              /\ deviceChange' = [d \in Device |-> ApplyDeviceChange(d, c)]
    /\ UNCHANGED <<nodeVars, networkChange, deviceVars, constraintVars>>

\* Node n handles a device configuration change c
NetworkControllerDeviceChange(n, d, c) ==
    /\ leadership[n] = TRUE
    /\ LET change == deviceChange[d][c]
       IN
           /\ change.state = Complete
           /\ networkChange[change.network].state # Complete
           /\ \/ /\ DeviceChangesUnavailable(change.network)
                 /\ networkChange' = [networkChange EXCEPT ![change.network] = [
                                          networkChange[change.network] EXCEPT 
                                              !.state = Pending]]
              \/ /\ DeviceChangesComplete(change.network)
                 /\ DeviceChangesSucceeded(change.network)
                 /\ networkChange' = [networkChange EXCEPT ![change.network] = [
                                          networkChange[change.network] EXCEPT
                                              !.state = Complete, !.result = Succeeded]]
              \/ /\ DeviceChangesComplete(change.network)
                 /\ ~DeviceChangesSucceeded(change.network)
                 /\ networkChange' = [networkChange EXCEPT ![change.network] = [
                                          networkChange[change.network] EXCEPT
                                              !.state = Complete, !.result = Failed]]
    /\ UNCHANGED <<nodeVars, deviceChange, deviceVars, constraintVars>>

----
(*
This section models the device-level change controller. The device control loop reacts
to device changes and applies changes to devices.
The device controller runs on each node in the cluster. A master is elected for each device,
and the control loop can only be executed on the master for the device targeted by a change.
Note, however, that the model does not require a single master per device. Multiple masters
may exist for a device without violating safety properties.

When a device change is received:
- If the node believes itself to be the master for the device and the change state
is Applying, apply the change
- Set the change state to Complete
- If the change was applied successfully, set the change result to Succeeded
- If the change failed, set the change result to Failed

Note: the above is modelled in two separate steps to allow the model checker to succeed
and fail device changes.

Updates to network device changes are atomic, and real-world implementations of the spec
must provide for atomic updates for network and device changes as well. This can be done using
either optimistic or pessimistic concurrency control.
*)

\* Node n handles a device configuration change event c
DeviceControllerDeviceChange(n, d, c) ==
    /\ mastership[n][d] = TRUE
    /\ LET change == deviceChange[d][c]
       IN
           /\ change.state = Applying
           /\ Cardinality({i \in DOMAIN deviceQueue[n][d] : deviceQueue[n][d][i] = c}) = 0
           /\ \/ /\ change.phase = Change
                 /\ deviceQueue' = [deviceQueue EXCEPT ![n] = [
                                     deviceQueue[n] EXCEPT ![d] = Append(deviceQueue[n][d], c)]]
              \/ /\ change.phase = Rollback
                 /\ networkChange[deviceChange[change.value]].state = Complete
                 /\ networkChange[deviceChange[change.value]].result = Succeeded
                 /\ deviceQueue' = [deviceQueue EXCEPT ![n] = [
                                     deviceQueue[n] EXCEPT ![d] = Append(deviceQueue[n][d], c)]]
    /\ UNCHANGED <<nodeVars, configVars, deviceConfig, deviceState, constraintVars>>

\* Return a sequence with the head removed
Pop(q) == SubSeq(q, 2, Len(q))

\* Mark change c on device d succeeded
SucceedChange(n, d) ==
    /\ Len(deviceQueue[n][d]) > 0
    /\ deviceState[d] = Available
    /\ deviceChange' = [deviceChange EXCEPT ![d] = [
                            deviceChange[d] EXCEPT ![deviceQueue[n][d][1]] = [
                                deviceChange[d][deviceQueue[n][d][1]] EXCEPT 
                                    !.state = Complete,
                                    !.result = Succeeded]]]
    /\ deviceConfig' = [deviceConfig EXCEPT ![d] = 
                           deviceChange[d][deviceQueue[n][d][1]].value]
    /\ deviceQueue' = [deviceQueue EXCEPT ![n] = [
                           deviceQueue[n] EXCEPT ![d] = Pop(deviceQueue[n][d])]]
    /\ UNCHANGED <<nodeVars, networkChange, deviceState, constraintVars>>

\* Mark change c on device d failed
\* A change can be failed if the device rejects the change or the device is not reachable.
FailChange(n, d) ==
    /\ Len(deviceQueue[n][d]) > 0
    /\ deviceChange' = [deviceChange EXCEPT ![d] = [
                            deviceChange[d] EXCEPT ![deviceQueue[n][d][1]] = [
                                deviceChange[d][deviceQueue[n][d][1]] EXCEPT 
                                    !.state = Complete, 
                                    !.result = Failed]]]
    /\ deviceQueue' = [deviceQueue EXCEPT ![n] = [
                           deviceQueue[n] EXCEPT ![d] = Pop(deviceQueue[n][d])]]
    /\ UNCHANGED <<nodeVars, networkChange, deviceConfig, deviceState, constraintVars>>

----
(*
This section models device states. Devices begin in the Unavailable state and can only
be configured while in the Available state.
*)

\* Set device d state to Available
ActivateDevice(d) ==
    /\ deviceState' = [deviceState EXCEPT ![d] = Available]
    /\ availabilityCount' = availabilityCount + 1
    /\ UNCHANGED <<nodeVars, configVars, deviceQueue, deviceConfig, electionCount, configCount>>

\* Set device d state to Unavailable
DeactivateDevice(d) ==
    /\ deviceState' = [deviceState EXCEPT ![d] = Unavailable]
    /\ availabilityCount' = availabilityCount + 1
    /\ UNCHANGED <<nodeVars, configVars, deviceQueue, deviceConfig, electionCount, configCount>>

----
(*
Init and next state predicates
*)

Init ==
    /\ leadership = [n \in Node |-> FALSE]
    /\ mastership = [n \in Node |-> [d \in Device |-> FALSE]]
    /\ networkChange = <<>>
    /\ deviceChange = [d \in Device |-> <<>>]
    /\ deviceQueue = [n \in Node |-> [d \in Device |-> <<>>]]
    /\ deviceConfig = [d \in Device |-> 0]
    /\ deviceState = [d \in Device |-> Unavailable]
    /\ electionCount = 0
    /\ configCount = 0
    /\ availabilityCount = 0

Next ==
    \/ \E d \in SUBSET Device : 
          SubmitChange([x \in d |-> 1])
    \/ \E c \in DOMAIN networkChange :
          SubmitRollback(c)
    \/ \E n \in Node : 
          \E l \in Node : 
             SetNodeLeader(n, l)
    \/ \E n \in Node :
          \E d \in Device :
             \E l \in Node :
                SetDeviceMaster(n, d, l)
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
    \/ \E n \in Node :
          \E d \in Device :
             SucceedChange(n, d)
    \/ \E n \in Node :
          \E d \in Device :
             FailChange(n, d)
    \/ \E d \in Device :
          ActivateDevice(d)
    \/ \E d \in Device :
          DeactivateDevice(d)

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Thu Dec 12 12:13:07 PST 2019 by jordanhalterman
\* Created Fri Sep 27 13:14:24 PDT 2019 by jordanhalterman
