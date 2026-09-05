# BANKED / formal

The canonical Lean source remains in [`../../RequestProject/`](../../RequestProject/) so import paths and reproducibility are not broken for cosmetic reasons.

Use the audited R12 formal-scope map at [`../../paper/audited-release/2026-09-05-r12/audit/FORMAL_MODULE_MAP.md`](../../paper/audited-release/2026-09-05-r12/audit/FORMAL_MODULE_MAP.md) to determine what is actually kernel-checked.

Important firewall: `KERNEL-PROVED` means only that the stated Lean theorem is accepted at its exact formal scope. It does not promote external analytic hypotheses or populate uninhabited effectivity sockets.
