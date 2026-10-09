```text
ERDŐS #287:
    OPEN

ANCHORED V2:
    FROZEN

ANCHORED V3:
    FROZEN

ANCHORED V4:
    BANKED / OPEN ROUTE

ANCHORED V4 CURRENT OPEN OWNERS:
    ENTRY_EXISTENCE
    SAFE_DESCENT_SUPPLY
    GUARDED_ABSORBER_ANALYTIC_SUPPLY

CONTACT-CORE LOCAL CLASSIFICATION:
    PAY / CLOSED

CONTACT-CORE GATE A:
    GLOBAL OPEN

CONTACT-CORE GATE B:
    OPEN
    generic long families paid

CONTACT-CORE GATE C:
    OPEN
    reduced excess core

CONTACT-CORE GATE D:
    CLOSED

CONTACT-CORE CURRENT OWNER:
    STRICT_HEIGHT_EXCEPTIONAL_LEAF_CAPACITY

ORIGINAL ERDŐS #287:
    OPEN
```

## Machine-readable counterpart

The statuses above are mirrored in Lean in
`RequestProject/Erdos287/ResearchBankV5/GateLedger.lean`
(`gateStatus`, `routeStatus`, `erdos287Status`, `currentOwner`, `routeOwners`) and in
`RequestProject/Erdos287/ResearchBankV5/AsymptoticInputs.lean`
(`externalAsymptoticInputs`).

## Firewall reminder

A route-aware research ledger is not a proof of route equivalence.

Anchored V4 and the Contact-core programme remain distinct.

A theorem proved in one route may be reused in the other only through an explicit proved bridge.

No OPEN external analytic statement is inhabited merely because it is recorded as BANKED research
state.
