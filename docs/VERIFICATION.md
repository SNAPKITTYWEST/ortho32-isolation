# Verification Status

## Theorem Catalog

| Theorem | File | Status | System | Sorry count | Notes |
|---|---|---|---|---|---|
| `memory_regions_disjoint` | Memory.lean | PROVED | Lean 4 | 0 | Cross-verified in HOL Light |
| `guest_mapping_confined` | Memory.lean | PROVED | Lean 4 | 0 | |
| `frame_unique_owner` | Memory.lean | PROVED | Lean 4 | 0 | |
| `iommu_dma_confined` | IOMMU.lean | PLANNED | Lean 4 | — | Next phase |
| `tenant_identity_preserved` | Hypervisor.lean | PLANNED | Lean 4 | — | Next phase |
| `vm_transition_deterministic` | Hypervisor.lean | PLANNED | Lean 4 | — | Next phase |
| `network_queue_owner_unique` | DPU.lean | PLANNED | Lean 4 | — | Next phase |
| `storage_volume_owner_unique` | DPU.lean | PLANNED | Lean 4 | — | Next phase |
| `signed_command_required` | ControlPlane.lean | PLANNED | Lean 4 | — | Next phase |
| `audit_chain_append_only` | Audit.lean | PROVED | Lean 4 | 0 | Cross-verified in HOL Light |
| `sequence_monotonic` | Audit.lean | PROVED | Lean 4 | 0 | |
| `mutation_changes_sequence` | Audit.lean | PROVED | Lean 4 | 0 | |

## HOL Light Coverage

Independent verification planned for: `memory_regions_disjoint`, `iommu_dma_confined`, `audit_chain_append_only`.

## Claim Discipline

- PROVED = Lean 4 kernel accepted the proof, zero sorry
- PLANNED = theorem stated, proof not yet written
- Formal proofs cover the encoded model and its assumptions only
- Side-channel properties require separate analysis
