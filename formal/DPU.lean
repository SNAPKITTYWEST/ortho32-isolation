import formal.Basic

namespace Ortho32.DPU

open Ortho32

-- DPU state: network queues, storage volumes and explicit forwarding rules
structure DPUState where
  networkQueues : List (TenantId × Nat)
  storageVolumes : List (TenantId × (UInt64 × UInt64))
  forwardingRules : List (TenantId × TenantId × Nat)
  wfQueues : ∀ (t1 t2 : TenantId) (qid : Nat), (t1, qid) ∈ networkQueues → (t2, qid) ∈ networkQueues → t1 = t2
  wfVolumes : ∀ (t1 t2 : TenantId) (base : UInt64) (sz1 sz2 : UInt64), (t1, (base, sz1)) ∈ storageVolumes → (t2, (base, sz2)) ∈ storageVolumes → t1 = t2 ∧ sz1 = sz2

-- A volume contains a block address
def volumeContains (vol : TenantId × (UInt64 × UInt64)) (addr : UInt64) : Prop :=
  vol.2.1 ≤ addr ∧ addr < vol.2.1 + vol.2.2

-- Valid block access: address lies in a volume owned by the tenant
def isValidBlockAccess (s : DPUState) (tenant : TenantId) (addr : UInt64) : Prop :=
  ∃ vol, vol ∈ s.storageVolumes ∧ vol.1 = tenant ∧ volumeContains vol addr

-- Packet model
structure Packet where
  srcTenant : TenantId
  dstQueueId : Nat
  deriving Repr, DecidableEq

-- Delivery is allowed only to an existing queue and only if same tenant or explicit rule
def CanDeliver (s : DPUState) (pkt : Packet) (dstTenant : TenantId) : Prop :=
  (dstTenant, pkt.dstQueueId) ∈ s.networkQueues ∧ (pkt.srcTenant = dstTenant ∨ (pkt.srcTenant, dstTenant, pkt.dstQueueId) ∈ s.forwardingRules)

-- Each virtual NIC queue is owned by exactly one tenant
theorem network_queue_owner_unique (s : DPUState) (qid : Nat) (t1 t2 : TenantId)
    (h1 : (t1, qid) ∈ s.networkQueues) (h2 : (t2, qid) ∈ s.networkQueues) : t1 = t2 :=
  s.wfQueues t1 t2 qid h1 h2

-- Each storage volume (identified by base address) is owned by exactly one tenant
theorem storage_volume_owner_unique (s : DPUState) (base : UInt64) (t1 t2 : TenantId) (sz1 sz2 : UInt64)
    (h1 : (t1, (base, sz1)) ∈ s.storageVolumes) (h2 : (t2, (base, sz2)) ∈ s.storageVolumes) : t1 = t2 :=
  (s.wfVolumes t1 t2 base sz1 sz2 h1 h2).1

-- Any address within a tenant's volume is a valid access for that tenant
theorem volume_address_confined (s : DPUState) (tenant : TenantId) (addr base size : UInt64)
    (hMem : (tenant, (base, size)) ∈ s.storageVolumes)
    (hWithin : base ≤ addr ∧ addr < base + size) :
    isValidBlockAccess s tenant addr := by
  unfold isValidBlockAccess
  refine ⟨(tenant, (base, size)), hMem, rfl, ?_⟩
  unfold volumeContains
  exact hWithin

-- A packet from tenant A cannot reach tenant B's queue without an explicit authorized forwarding rule
theorem no_cross_tenant_packet (s : DPUState) (pkt : Packet) (dstTenant : TenantId)
    (hNe : pkt.srcTenant ≠ dstTenant)
    (hNoFwd : (pkt.srcTenant, dstTenant, pkt.dstQueueId) ∉ s.forwardingRules) :
    ¬ CanDeliver s pkt dstTenant := by
  intro hDeliver
  unfold CanDeliver at hDeliver
  rcases hDeliver with ⟨_, hOr⟩
  rcases hOr with hEq | hFwd
  · exact hNe hEq
  · exact hNoFwd hFwd

end Ortho32.DPU
