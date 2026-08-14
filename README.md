# ortho32-isolation

**ORTHO-32 Hardware-Separated Isolation**

Minimal hypervisor, management SoC, DPU data plane, formal isolation proofs, zero-operator control.

## What This Is

A hardware-separated virtualization architecture where the host CPU runs tenant workloads while security-critical management, networking, storage, attestation, and control functions run in dedicated ORTHO silicon.

**Five explicit layers — never collapsed:**

```
L0  Hardware Root of Trust   ManagementSoC, PCIe endpoint, IOMMU gate, crypto engine
L1  Minimal Hypervisor        CPU partition, memory partition, VM entry/exit — NO shell, NO ssh
L2  Hardware Data Plane       Network DPU (vNIC, ACL, overlay, crypto), Storage DPU (vNVMe, volume)
L3  Formal Isolation          Lean 4 proofs, HOL Light cross-verification
L4  Zero-Operator Control     Signed commands, replay protection, API-only, no root SSH
```

## Architecture

```
                 REMOTE CONTROL PLANE
                          |
                 Signed API Commands
                          |
                 Attestation / Policy
                          |
                          v
             +-------------------------+
             | ORTHO MANAGEMENT SOC   |
             | Root of Trust / DPU    |
             +-----------+------------+
                         | PCIe
            +------------+-----------+
            |            |           |
            v            v           v
      NETWORK DPU   STORAGE DPU  SECURITY ENGINE
            |            |           |
            +------------+-----------+
                         |
                  IOMMU / DMA Gate
                         |
                         v
               MINIMAL HYPERVISOR
                         |
              CPU + RAM Partitioning
                         |
          +--------------+--------------+
          v              v              v
       Tenant A       Tenant B       Tenant C
          VM             VM             VM
```

## Isolation Invariants

The 9 theorems proved in Lean 4 (zero Mathlib, zero sorry in headline chain):

| Theorem | Statement |
|---|---|
| `memory_regions_disjoint` | `tenantA != tenantB -> disjoint(region(A), region(B))` |
| `guest_mapping_confined` | guest page table cannot map frame outside tenant's region |
| `iommu_dma_confined` | device DMA confined to its IOMMU domain |
| `tenant_identity_preserved` | VM transition preserves tenant identity |
| `vm_transition_deterministic` | same state + input -> same next state |
| `network_queue_owner_unique` | each queue owned by exactly one tenant |
| `storage_volume_owner_unique` | each volume owned by exactly one tenant |
| `signed_command_required` | unsigned commands never execute |
| `audit_chain_append_only` | historical records cannot be mutated |

HOL Light independently verifies: `memory_regions_disjoint`, `iommu_dma_confined`, `audit_chain_append_only`.

## Hypervisor Rules

The hypervisor is an isolation engine, **not** a general-purpose OS.

**Forbidden in the TCB:**
- No shell
- No SSH
- No general-purpose filesystem
- No package manager
- No local admin account
- No desktop
- No arbitrary device drivers

## Control Plane Contract

Every management command must carry:

```
commandId  issuer  tenant  action  target  parametersHash
sequence   expiry  policyVersion  signature
```

Execution: authenticate -> authorize -> verify signature -> verify sequence/replay -> validate policy -> execute -> append witness record.

## Witness Record (Audit)

```
sequence  previousHash  timestamp  issuer  action  target
requestHash  resultHash  measurementHash  signature
```

- Sequence is strictly monotonic
- Record N commits to record N-1
- Mutating any historical record invalidates the chain
- No delete. No modify.

## Failure Model

| Failure | Response |
|---|---|
| Invalid command signature | reject + audit |
| Replayed command | reject + audit |
| Illegal guest memory mapping | reject + fault guest |
| Illegal DMA target | IOMMU fault + isolate device queue |
| DPU firmware measurement mismatch | prevent privileged activation |
| Audit chain mismatch | security failure state |

## Security Claim Discipline

**Not claimed** without separate analysis:
- Side-channel immunity (Spectre, cache, branch, power, EM, DMA, firmware)
- Physical attack resistance
- Bitwise reproducibility under concurrent execution

**"Zero-operator"** means no routine interactive privileged administration. Emergency recovery must be explicitly designed, authenticated, measured, rate-limited, and audited.

## Repository Structure

```
ortho32-isolation/
├── formal/               Lean 4 + HOL Light proofs
│   ├── Basic.lean        Primitive types
│   ├── Tenant.lean       Tenant model
│   ├── Memory.lean       Memory ownership theorems
│   ├── IOMMU.lean        IOMMU isolation theorems
│   ├── Hypervisor.lean   VM transition theorems
│   ├── DPU.lean          DPU queue/volume theorems
│   ├── ControlPlane.lean Command authorization theorems
│   └── Audit.lean        Audit chain theorems
├── hypervisor/           C — minimal isolation monitor
│   ├── vm.h / vm.c       Guest create/destroy/enter/exit
│   ├── memory.c          Page mapping with confinement check
│   ├── iommu.c           IOMMU domain assignment + DMA fault
│   └── entry.S           VM entry/exit assembly stub
├── management-soc/       C — root of trust
│   ├── boot.c            Firmware measurement + monotonic counter
│   ├── attestation.c     Attestation report + signing
│   ├── command.c         Signed command verify + execute
│   ├── policy.c          Policy state + update
│   └── crypto.c          SHA-256, HMAC, signature verify (no key leakage)
├── dpu/                  C — data plane
│   ├── network.c         vNIC queue + ACL + overlay + crypto
│   └── storage.c         vNVMe queue + volume confinement
├── rtl/                  SystemVerilog — hardware blocks
│   ├── pcie/             PCIe endpoint (BAR0-4)
│   ├── iommu/            IOMMU gate (fault on out-of-domain DMA)
│   ├── command_queue/    Command ring + sequence replay check
│   ├── crypto/           SHA-256 pipeline
│   └── trace/            Append-only trace engine
├── api/                  Management API
│   ├── openapi/          OpenAPI spec
│   └── server/           API server
├── audit/                Witness log + chain verifier
├── tests/                Unit + integration + fuzz
└── docs/
    ├── ARCHITECTURE.md
    ├── THREAT_MODEL.md
    ├── TRUSTED_COMPUTING_BASE.md
    └── VERIFICATION.md
```

## Build

```bash
# Formal proofs (requires Lean 4)
lake build

# Hypervisor + management-soc + DPU
cd hypervisor && make
cd management-soc && make
cd dpu && make

# RTL simulation (requires Verilator)
cd rtl && make sim

# Unit tests
cd tests && make unit

# Integration tests
cd tests && make integration

# Fuzz (requires libFuzzer)
cd tests/fuzz && make fuzz
```

## Languages

| Layer | Language |
|---|---|
| Formal proofs | Lean 4 + HOL Light |
| Hypervisor | C |
| Management SoC | C |
| DPU data plane | C |
| RTL / chip fabric | SystemVerilog |
| API server | C (minimal) |
| Build tooling | Shell + Make |

**No TypeScript. No JavaScript. No Python in the TCB.**

## Status

Implementation in progress. See `docs/VERIFICATION.md` for theorem proof status.
