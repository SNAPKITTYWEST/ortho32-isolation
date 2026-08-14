# Trusted Computing Base

## In TCB

| Component | Language | Why |
|---|---|---|
| Management SoC firmware | C | Owns boot measurement, attestation, signed commands |
| Hypervisor (vm.c memory.c iommu.c entry.S) | C + ASM | CPU/memory partition, VM entry/exit |
| DPU firmware (network.c storage.c) | C | Data plane isolation |
| Lean 4 kernel | Lean 4 | Proof checker trusted base |
| HOL Light kernel | OCaml | Cross-verification trusted base |

## Not In TCB

- Tenant OS / guest kernel
- Host userspace applications
- Swift desktop
- TypeScript AI gateway
- Java SDK
- Python tooling
- Web browsers
- Any general-purpose OS running on the host CPU

## TCB Size Target

The hypervisor must remain small enough to be auditable. No shell, no SSH, no package manager, no general-purpose filesystem, no local admin account anywhere in the TCB.

## Formal Assumptions

Every theorem in `formal/` rests on explicit assumptions. These are listed in each file. Lean 4 axioms used: `propext`, `Classical.choice`, `Quot.sound`, `Nat`, `Int`. No Mathlib.
