--------------------------- MODULE PollingSubstate ---------------------------
EXTENDS Naturals, TLC

CONSTANTS
    DETECT,           \* Exit to Detect
    CONFIGURATION     \* Exit to Configuration

VARIABLES
    state,            \* Current state: "Active", "Configuration", "Compliance"
    exitTo            \* Exit destination: DETECT or CONFIGURATION or "None"

vars == <<state, exitTo>>

-----------------------------------------------------------------------------

\* Type invariant
TypeOK ==
    /\ state \in {"Active", "Configuration", "Compliance"}
    /\ exitTo \in {DETECT, CONFIGURATION, "None"}

\* Initial state - Entry goes to Polling.Active
Init ==
    /\ state = "Active"
    /\ exitTo = "None"

-----------------------------------------------------------------------------

\* Transition from Active to Configuration
ActiveToConfiguration ==
    /\ state = "Active"
    /\ state' = "Configuration"
    /\ UNCHANGED exitTo

\* Transition from Active to Compliance
ActiveToCompliance ==
    /\ state = "Active"
    /\ state' = "Compliance"
    /\ UNCHANGED exitTo

\* Transition from Compliance back to Active
ComplianceToActive ==
    /\ state = "Compliance"
    /\ state' = "Active"
    /\ UNCHANGED exitTo

\* Exit from Active to Detect
ActiveToDetect ==
    /\ state = "Active"
    /\ exitTo' = DETECT
    /\ UNCHANGED state

\* Exit from Configuration to Configuration state
ConfigurationToConfiguration ==
    /\ state = "Configuration"
    /\ exitTo' = CONFIGURATION
    /\ UNCHANGED state

\* Exit from Compliance to Detect
ComplianceToDetect ==
    /\ state = "Compliance"
    /\ exitTo' = DETECT
    /\ UNCHANGED state

-----------------------------------------------------------------------------

Next ==
    \/ ActiveToConfiguration
    \/ ActiveToCompliance
    \/ ComplianceToActive
    \/ ActiveToDetect
    \/ ConfigurationToConfiguration
    \/ ComplianceToDetect

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* Properties to verify

\* Eventually the system should be able to reach any state
EventuallyActive == <>(state = "Active")
EventuallyConfiguration == <>(state = "Configuration")
EventuallyCompliance == <>(state = "Compliance")

\* No deadlocks - always possible to make a transition
NoDeadlock == state \in {"Active", "Configuration", "Compliance"} 
              => ENABLED Next

=============================================================================
